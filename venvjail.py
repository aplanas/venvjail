#!/usr/bin/env python3

# Copyright (c) 2017 SUSE LINUX GmbH, Nuernberg, Germany.
# Copyright (c) 2020 SUSE LLC.
#
# All modifications and additions to the file contributed by third parties
# remain the property of their copyright owners, unless otherwise agreed
# upon. The license for this file, and modifications and additions to the
# file, is the same license as for the pristine package itself (unless the
# license for the pristine package is not an Open Source License, in which
# case the license is the MIT License). An "Open Source License" is a
# license that conforms to the Open Source Definition (Version 1.9)
# published by the Open Source Initiative.

# Please submit bugfixes or comments via http://bugs.opensuse.org/
#

# Script to help the creation of a virtual environment based of binary
# and Python RPMs.  Used to jail OpenStack services.

import argparse
import datetime
import fnmatch
import glob
import itertools
import os
import os.path
import pathlib
import re
import subprocess
import xml.etree.ElementTree as ET

# Sane default for exclude-rpm file
EXCLUDE_RPM = r"""# List of packages to ignore (use Python regex)

# Note that `exclude` takes precedence over `include`.  So if a
# package match both constrains, it will be excluded.

# Exclude irrelevant sub-packages
.*-debuginfo$
.*-debugsource$
.*-devel$
.*-devel-.*
# Exclude docs packages (but do not exclude docker)
.*-doc$
.*-docs$
.*-doc-.*
.*-test

# Python base breaks the venv
python-base
python3-base

# Exclude all Python 3 packages
python3.*

# Exclude rpmlint related packages
rpmlint.*
"""

LICENSE = f"""# Copyright (c) {datetime.datetime.today().year} SUSE LLC.
#
# All modifications and additions to the file contributed by third parties
# remain the property of their copyright owners, unless otherwise agreed
# upon. The license for this file, and modifications and additions to the
# file, is the same license as for the pristine package itself (unless the
# license for the pristine package is not an Open Source License, in which
# case the license is the MIT License). An "Open Source License" is a
# license that conforms to the Open Source Definition (Version 1.9)
# published by the Open Source Initiative.
"""


class FileList:
    """File list with comments and regular expressions."""

    def __init__(self, filename):
        try:
            self.items = [
                re.compile(line.strip())
                for line in open(filename)
                if line.strip() and not line.strip().startswith("#")
            ]
        except IOError:
            self.items = []

    def is_populated(self):
        return self.items

    def contains(self, item):
        return any(i.match(item) for i in self.items)

    def __contains__(self, item):
        return self.contains(item)


def _replace(filename, original, line):
    """Replace a line in a file using regular expressions."""
    lines = re.sub(original, line, open(filename).read())
    open(filename, "w").writelines(lines)


def _insert(filename, after, line):
    """Insert a line after the `after` line."""
    lines = open(filename).readlines()
    # If the line is not found, will produce a ValueError exception
    # and will end the script.  We do not want to capture the
    # exception, so we can see in OBS that the precondition was not
    # meet
    index = lines.index(after + "\n")
    lines.insert(index + 1, line + "\n")
    open(filename, "w").writelines(lines)


def _fix_virtualenv(dest_dir, relocated, no_relocate_shebang):
    """Fix virtualenv activators."""
    # New path where the venv will live at the end
    virtual_env = relocated / dest_dir

    _fix_filesystem(dest_dir)
    _fix_alternatives(dest_dir, relocated)
    _fix_broken_links(dest_dir, directories=["srv"])
    _fix_relocation(dest_dir, virtual_env, no_relocate_shebang)
    _fix_activators(dest_dir, virtual_env)
    _fix_loader(dest_dir, virtual_env)
    _fix_systemd_services(dest_dir, virtual_env)


def _fix_filesystem(dest_dir):
    """Fix filesystem permissions."""
    # When a directory is not owned by a package, cpio can create the
    # directory with wrong permissions.  For SLE12 cpio is not taking
    # care of the global mask (022), and create the directory with
    # 700.
    dirs = {
        "etc": 0o755,
        "etc/cron.daily": 0o755,
        "etc/logrotate.d": 0o755,
        "etc/modprobe.d": 0o755,
        "etc/sudoers.d": 0o750,
        "srv": 0o755,
        "srv/www": 0o755,
        "usr": 0o755,
        "usr/share": 0o755,
        "usr/share/doc": 0o755,
        "usr/share/doc/packages": 0o755,
        "usr/share/help": 0o755,
        "usr/share/help/C": 0o755,
        "usr/share/man": 0o755,
        "usr/share/man/man1": 0o755,
        "var": 0o755,
        "var/cache": 0o755,
        "var/lib": 0o755,
        "var/log": 0o755,
    }

    # Since OBS do not (if it is not white-listed) run as root, all
    # the cpio output will create files with the same owner (the OBS
    # user).  This create bugs like bsc#1083826, when a directory can
    # only be accessed by the owner or the group but not for others.
    # dirs.update({"usr/share/keystone": 0o755})

    for dir_, mod_ in dirs.items():
        dir_ = dest_dir / dir_
        if dir_.is_dir():
            dir_.chmod(mod_)


def _fix_alternatives(dest_dir, relocated):
    """Fix alternative links."""
    # os.scandir() was implemented in 3.5, but for now we are in 3.4
    for dirpath, dirnames, filenames in os.walk(dest_dir):
        for name in filenames:
            rel_name = os.path.join(dirpath, name)
            if os.path.islink(rel_name) and "alternatives" in os.readlink(rel_name):
                # We assume that the Python 3.8 alternative is living
                # in the same directory, but we create the link the
                # the place were it will live at the end
                alt_name = os.path.join(relocated, dirpath, name + "-3.8")
                alt_rel_name = rel_name + "-3.8"
                if os.path.exists(alt_rel_name):
                    os.unlink(rel_name)
                    os.symlink(alt_name, rel_name)
                else:
                    print(f"ERROR: alternative link for {name} not found")


def _fix_broken_links(dest_dir, directories=None):
    """Fix broken links."""
    # Some packages create absolute soft-links.  We can use some
    # heuristics to detect them, and if is possible, fix them.
    for fix_dir in directories:
        fix_dir = os.path.join(dest_dir, fix_dir)
        for dirpath, dirnames, filenames in os.walk(fix_dir):
            for name in itertools.chain(dirnames, filenames):
                rel_name = os.path.join(dirpath, name)
                if os.path.islink(rel_name) and os.readlink(rel_name).startswith("/"):
                    link_to = os.path.join(dest_dir, os.readlink(rel_name)[1:])
                    if os.path.exists(link_to):
                        # Convert the absolute link into a relative
                        # link, also takes care of removing the
                        # initial '/' from the path
                        rel_link = os.path.relpath(link_to, os.path.dirname(rel_name))
                        os.unlink(rel_name)
                        os.symlink(rel_link, rel_name)
                    else:
                        print(f"ERROR: alternative link for {name} not found")


def _fix_relocation(dest_dir, virtual_env, no_relocate_shebang):
    """Fix relocation shebang from python scripts"""
    shebang = "#!" + os.path.join(virtual_env, "bin", "python")
    for dirpath, dirnames, filenames in os.walk(dest_dir):
        for name in filenames:
            rel_name = os.path.join(dirpath, name)
            if any(fnmatch.fnmatch(rel_name, path) for path in no_relocate_shebang):
                continue
            if os.path.isfile(rel_name):
                try:
                    line = open(rel_name).readline().strip()
                    if line.startswith("#!") and "python" in line:
                        _replace(rel_name, line, shebang)
                except Exception:
                    pass


def _fix_activators(dest_dir, virtual_env):
    """Fix virtualenv activators."""
    ld_library_path = virtual_env / "lib"
    activators = {
        "activate": {
            "replace": (r'VIRTUAL_ENV=".*"', f'VIRTUAL_ENV="{virtual_env}"'),
            "insert": (
                "deactivate nondestructive",
                f'export LD_LIBRARY_PATH="{ld_library_path}"',
            ),
        },
        "activate.csh": {
            "replace": (
                r'setenv VIRTUAL_ENV ".*"',
                f'setenv VIRTUAL_ENV "{virtual_env}"',
            ),
            "insert": (
                "deactivate nondestructive",
                f'setenv LD_LIBRARY_PATH "{ld_library_path}"',
            ),
        },
        "activate.fish": {
            "replace": (
                r'set -gx VIRTUAL_ENV ".*"',
                f'set -gx VIRTUAL_ENV "{virtual_env}"',
            ),
            "insert": (
                "deactivate nondestructive",
                f'set -gx LD_LIBRARY_PATH "{ld_library_path}"',
            ),
        },
    }

    for activator, action in activators.items():
        filename = dest_dir / "bin" / activator
        # Fix the VIRTUAL_ENV directory
        original, line = action["replace"]
        _replace(filename, original, line)

        # Add the new LD_LIBRARY_PATH.  We use the `lib` instead of
        # `lib64` in the assumption that this will remain invariant
        # for different architectures
        after, line = action["insert"]
        _insert(filename, after, line)


def _fix_loader(dest_dir, virtual_env):
    """Fix virtualenv python entry point."""
    loader = f"""#!/bin/sh

export VIRTUAL_ENV="{virtual_env}"
export PATH="$VIRTUAL_ENV/bin:$PATH"
export LD_LIBRARY_PATH="$VIRTUAL_ENV/bin"
exec {{}} "$@"
"""

    # We replace all the python interpreters with a loader that set
    # the correct env variables before executing it
    for python in (dest_dir / "bin").glob("python*"):
        new_name = python.with_suffix(".original")
        python.rename(new_name)
        with python.open("w") as f:
            new_python = virtual_env / "bin" / new_name.name
            f.write(loader.format(new_python))
        python.chmod(0o755)


def _fix_systemd_services_in(services_dir, virtual_env):
    for service in services_dir.glob("*.service"):
        # Service files are read only
        service.chmod(0o644)
        _replace(service, r"ExecStart=(.*)", rf"ExecStart={virtual_env}\1")
        _replace(service, r"ExecStartPre=-(.*)", rf"ExecStartPre=-{virtual_env}\1")
        service.chmod(0o444)

        # TODO: Do we need this? If so, we should adjust some After and Before
        # For convenience, rename the service
        service.rename(services_dir / ("venv-" + service.name))


def _fix_systemd_services(dest_dir, virtual_env):
    """Fix systemd services."""
    for systemd_dir in ("lib/systemd/system", "usr/lib/systemd/system"):
        _fix_systemd_services_in(dest_dir / systemd_dir, virtual_env)


def _extract_rpm(package, directory):
    subprocess.call(
        f"cd {directory}; rpm2cpio {package} | "
        "cpio --extract --unconditional "
        "--preserve-modification-time --make-directories "
        "--extract-over-symlinks",
        stdout=subprocess.DEVNULL,
        shell=True,
    )


def _extract_deb(package, directory):
    subprocess.call(
        f"cd {directory}; ar x {package}; "
        "tar -xJvf data.tar.xz; "
        "rm control.tar.gz data.tar.xz debian-binary",
        stdout=subprocess.DEVNULL,
        shell=True,
    )


def _get_rpm_track_info(package):
    query = "|".join(
        ("%{NAME}", "%{EPOCH}", "%{VERSION}", "%{RELEASE}", "%{ARCH}", "%{DISTURL}")
    )
    return subprocess.check_output(
        f"rpm -qp --queryformat='{query}' {package}",
        stderr=subprocess.DEVNULL,
        shell=True,
    )


def _get_deb_track_info(package):
    query = "|".join(
        ("${Package}", "None", "${Version}", "None", "${Architecture}", "None", "None")
    )

    return subprocess.check_output(
        f"dpkg-deb -W --showformat='{query}' {package}",
        stderr=subprocess.DEVNULL,
        shell=True,
    )


def create(args):
    """Function called for the `create` command."""
    # Create the virtual environment
    options = []
    if args.system_site_packages:
        options.append("--system-site-packages")
    options.append("--without-pip")
    options = " ".join(options)
    subprocess.call(f"python3 -m venv {options} {args.dest_dir}", shell=True)

    # Prepare the links for /usr/bin and /usr/lib[64]
    usr = args.dest_dir / "usr"
    usr.mkdir()
    (usr / "bin").symlink_to("../bin")
    (usr / "lib").symlink_to("../lib")
    (usr / "lib64").symlink_to("../lib")

    # If both are populated, the algorithm will take precedence over
    # the `exclude` list
    include = FileList(args.include)
    exclude = FileList(args.exclude)

    # Install the packages and maintain a log
    included = []
    excluded = []
    packages = itertools.chain.from_iterable(
        args.repo.glob(pkgs) for pkgs in ("*.rpm", "*.deb")
    )
    for package in packages:
        pkg = package.name
        if pkg in exclude:
            excluded.append(pkg)
            continue
        if include.is_populated() and pkg not in include:
            excluded.append(pkg)
            continue
        included.append(pkg)

        package = package.absolute()
        if package.suffix == ".rpm":
            _extract_rpm(package, args.dest_dir)
        elif package.suffix == ".deb":
            _extract_deb(package, args.dest_dir)

    _fix_virtualenv(args.dest_dir, args.relocate, args.no_relocate_shebang_list)

    # Write the log file, useful to better taylor the inclusion /
    # exclusion of packages.
    with (args.dest_dir / "packages.log").open("w") as f:
        print("# Included packages", file=f)
        for pkg in sorted(included):
            print(pkg, file=f)
        print("\n\n# Excluded packages", file=f)
        for pkg in sorted(excluded):
            print(pkg, file=f)

    # Write the L3/Maintenance track file, required to track the
    # content of the venv inside OBS.
    if args.track:
        with args.track.open("w") as f:
            for pkg in sorted(included):
                pkg = args.repo / pkg
                if pkg.suffix == ".rpm":
                    line = _get_rpm_track_info(pkg)
                elif pkg.suffix == ".deb":
                    line = _get_deb_track_info(pkg)
                else:
                    line = ["None"] * 7
                print(line.decode("utf-8"), file=f)


def _filter_binary_xml(root):
    """Filter a XML tree of binary elements"""
    elements = []
    for binary in root.findall("binary"):
        rpm = binary.get("filename")
        if rpm.startswith("_"):
            continue
        if rpm.endswith(".log"):
            continue
        if rpm.endswith("src.rpm"):
            continue
        elements.append(rpm)
    return elements


def _filter_binary_name(names, args):
    """Filter a list of package names"""
    exclude = FileList(args.exclude)
    if args.all:
        return names
    else:
        return [pkg for pkg in names if pkg not in exclude]


def _repository(args):
    """List binary packages from a repository"""
    api = f"/build/{args.project}/{args.repo}/{args.arch}/_repository"
    output = subprocess.check_output(
        f"osc --apiurl {args.apiurl} api {api}", shell=True
    )
    elements = _filter_binary_xml(ET.fromstring(output))
    # Unversioned name, so we remove the file extension
    elements = [re.sub(r"\.rpm$|\.deb$", "", pkg) for pkg in elements]
    return _filter_binary_name(elements, args)


def include(args):
    """Generate initial include-rpm file"""
    if not all((args.project, args.repo, args.arch)):
        print("ERROR: please, specify the project, repository and architecture")
        exit(1)

    print("# List of packages to include (use Python regex)")
    print()
    print("# Packages from the repository")
    for name in _repository(args):
        print(f"{name}.*")


def exclude(args):
    """Generate initial exclude-rpm file"""
    print(EXCLUDE_RPM)


def binary(args):
    """List binary packages from a source package"""
    if not all((args.project, args.repo, args.arch, args.package)):
        print(
            "ERROR: please, specify the project, repository, architecture and package"
        )
        exit(1)

    # OBS generate a full package name, including the version and
    # architecture.  To generate include-pkg and exclude-pkg, we will
    # need only the name of the package
    pkg_re = re.compile(
        r"(?:(.*)-([^-]+)-([^-]+)\.([^-\.]+)\.rpm)|(?:(.*)_([^_]+)_([^_]+)\.deb)"
    )

    api = f"/build/{args.project}/{args.repo}/{args.arch}/{args.package}"
    output = subprocess.check_output(
        f"osc --apiurl {args.apiurl} api {api}", shell=True
    )
    elements = _filter_binary_xml(ET.fromstring(output))
    # Take only the name of the package
    elements = [
        pkg_re.match(pkg).groups()[0] or pkg_re.match(pkg).groups()[4]
        for pkg in elements
        if pkg_re.match(pkg)
    ]
    elements = _filter_binary_name(elements, args)
    for pkg in elements:
        print(pkg)


def _filter_requires_spec(spec):
    """Recover the Requires elements from a spec file"""
    requires = re.findall(r"^Requires:\s*([-\.\w]+)(.*)?$", spec, re.MULTILINE)
    return dict(requires)


def requires(args):
    """List requirements for a source package"""
    if not all((args.project, args.package)):
        print("ERROR: please, specify the project and package")
        exit(1)

    # TODO: we need to find a way for Debian
    api = f"/source/{args.project}/{args.package}/{args.package}.spec"
    output = subprocess.check_output(
        f"osc --apiurl {args.apiurl} api {api}", shell=True
    )
    requires_and_version = _filter_requires_spec(output.decode("utf-8"))
    requires = requires_and_version.keys()

    # Remove the packages included in the venv
    include = FileList(args.include)
    exclude = FileList(args.exclude)
    in_venv = []
    for pkg in requires:
        if pkg in exclude:
            continue
        if include.is_populated() and pkg not in include:
            continue
        in_venv.append(pkg)
    requires = set(requires) - set(in_venv)

    for pkg in sorted(requires):
        requires = f"{pkg} {requires_and_version[pkg].strip()}"
        print(requires.strip())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Utility to help venvs creation for Python services"
    )
    subparsers = parser.add_subparsers(help="Sub-commands for venvjail")

    # Parser for `create` command
    subparser = subparsers.add_parser("create", help="Create a virtualenv")
    subparser.add_argument(
        "dest_dir",
        type=pathlib.Path,
        metavar="DEST_DIR",
        help="Virtual environment directory",
    )
    subparser.add_argument(
        "-s",
        "--system-site-packages",
        action="store_false",
        help="Allows access to the global site-packages",
    )
    subparser.add_argument(
        "-l",
        "--relocate",
        type=pathlib.Path,
        default="/opt/venv",
        help="Relocated virtual environment directory",
    )
    subparser.add_argument(
        "--no-relocate-shebang-list",
        metavar="PATH",
        default=[],
        nargs="+",
        help="Do not change the shebang in these files. "
        "Wildcards supported (fnmatch/bash style). "
        "Specify with DEST_DIR.",
    )
    subparser.add_argument(
        "-r",
        "--repo",
        type=pathlib.Path,
        default=pathlib.Path("/.build.binaries"),
        help="Repository directory",
    )
    subparser.add_argument(
        "-i",
        "--include",
        type=pathlib.Path,
        default="include-rpm",
        help="File with the list of packages to install",
    )
    subparser.add_argument(
        "-x",
        "--exclude",
        type=pathlib.Path,
        default="exclude-rpm",
        help="File with packages to exclude",
    )
    subparser.add_argument(
        "-t",
        "--track",
        type=pathlib.Path,
        help="Filename for the L3/Maintenance track file",
    )
    subparser.add_argument("-v", "--version", default="0.1.0", help="Package version")
    subparser.set_defaults(func=create)

    # Parser for `include` command
    subparser = subparsers.add_parser(
        "include", help="Generate initial include-rpm file"
    )
    subparser.add_argument(
        "-A", "--apiurl", default="https://api.opensuse.org", help="API address"
    )
    subparser.add_argument("-p", "--project", help="Project name")
    subparser.add_argument("-r", "--repo", default="standard", help="Repository name")
    subparser.add_argument("-a", "--arch", default="x86_64", help="Architecture")
    subparser.add_argument("--all", action="store_true", help="Include all packages")
    subparser.add_argument(
        "-x", "--exclude", default="exclude-rpm", help="File with packages to exclude"
    )
    subparser.set_defaults(func=include)

    # Parser for `exclude` command
    subparser = subparsers.add_parser(
        "exclude", help="Generate initial exclude-rpm file"
    )
    subparser.set_defaults(func=exclude)

    # Parser for `binary` command
    subparser = subparsers.add_parser("binary", help="List the binary packages")
    subparser.add_argument("package", metavar="PACKAGE", help="Source package name")
    subparser.add_argument(
        "-A", "--apiurl", default="https://api.opensuse.org", help="API address"
    )
    subparser.add_argument("-p", "--project", help="Project name")
    subparser.add_argument("-r", "--repo", default="standard", help="Repository name")
    subparser.add_argument("-a", "--arch", default="x86_64", help="Architecture")
    subparser.add_argument("--all", action="store_true", help="Include all packages")
    subparser.add_argument(
        "-x", "--exclude", default="exclude-rpm", help="File with packages to exclude"
    )
    subparser.set_defaults(func=binary)

    # Parser for `requires` command
    subparser = subparsers.add_parser(
        "requires", help="List requirements for a package"
    )
    subparser.add_argument("package", metavar="PACKAGE", help="Source package name")
    subparser.add_argument(
        "-A", "--apiurl", default="https://api.opensuse.org", help="API address"
    )
    subparser.add_argument("-p", "--project", help="Project name")
    subparser.add_argument(
        "-i",
        "--include",
        default="include-rpm",
        help="File with the list of packages to install",
    )
    subparser.add_argument(
        "-x", "--exclude", default="exclude-rpm", help="File with packages to exclude"
    )
    subparser.set_defaults(func=requires)

    args = parser.parse_args()
    if not hasattr(args, "func"):
        print("ERROR: No action specified")
        parser.print_help()
        exit(1)
    args.func(args)
