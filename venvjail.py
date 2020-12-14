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
import fnmatch
import glob
import itertools
import os
import os.path
import re
import subprocess
import xml.etree.ElementTree as ET

# Sane default for exclude-rpm file
EXCLUDE_RPM = r"""# List of packages to ignore (use Python regex)

# Note that `exclude` takes precedence over `include`.  So if a
# package match both constrains, it will be excluded.

# Exclude irrelevan sub-packages
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

LICENSE = """# Copyright (c) 2020 SUSE LLC.
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
    virtual_env = os.path.join(relocated, dest_dir)

    _fix_filesystem(dest_dir)
    _fix_alternatives(dest_dir, relocated)
    _fix_broken_links(dest_dir, directories=["srv"])
    _fix_relocation(dest_dir, virtual_env, no_relocate_shebang)
    _fix_activators(dest_dir, virtual_env)
    _fix_systemd_services(dest_dir, virtual_env)


def _fix_filesystem(dest_dir):
    """Fix filesystem permissions."""

    # When a directory is not owned by a package, cpio can create the
    # directory with wrong permissions.  For SLE12 spio is not taking
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

    # Since OBS do not (if is not white-listed) run as root, all the
    # cpio output will be create file with the same owner (the OBS
    # user).  This create bugs like bsc#1083826, when a directory can
    # only be accessed by the owner or the group but not for others.
    dirs.update(
        {
            "usr/share/keystone": 0o755,
        }
    )

    for dir_, mod_ in dirs.items():
        dir_ = os.path.join(dest_dir, dir_)
        if os.path.isdir(dir_):
            os.chmod(dir_, mod_)


def _fix_alternatives(dest_dir, relocated):
    """Fix alternative links."""
    # os.scandir() was implemented in 3.5, but for now we are in 3.4
    for dirpath, dirnames, filenames in os.walk(dest_dir):
        for name in filenames:
            rel_name = os.path.join(dirpath, name)
            if os.path.islink(rel_name) and "alternatives" in os.readlink(rel_name):
                # We assume that the Python 2.7 alternative is living
                # in the same directory, but we create the link the
                # the place were it will live at the end
                alt_name = os.path.join(relocated, dirpath, name + "-2.7")
                alt_rel_name = rel_name + "-2.7"
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
    shebang = "#!" + os.path.join(virtual_env, "bin", "python2")
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
    ld_library_path = os.path.join(virtual_env, "lib")
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
        filename = os.path.join(dest_dir, "bin", activator)
        # Fix the VIRTUAL_ENV directory
        original, line = action["replace"]
        _replace(filename, original, line)

        # Add the new LD_LIBRARY_PATH.  We use the `lib` instead of
        # `lib64` in the assumption that this will remain invariant
        # for different architectures
        after, line = action["insert"]
        _insert(filename, after, line)


def _fix_systemd_services(dest_dir, virtual_env):
    """Fix OpenStack systemd services."""
    services = os.path.join(dest_dir, "usr/lib/systemd/system")
    for service in glob.glob(os.path.join(services, "*.service")):
        # Service files are read only
        os.chmod(service, 0o644)
        _replace(service, r"ExecStart=(.*)", rf"ExecStart={virtual_env}\1")
        _replace(service, r"ExecStartPre=-(.*)", rf"ExecStartPre=-{virtual_env}\1")
        os.chmod(service, 0o444)
        # For convenience, rename the service
        os.rename(service, os.path.join(services, "venv-" + os.path.basename(service)))


def _os_release(ardana_version):
    """Recover release information."""
    output = subprocess.check_output("lsb_release -a", shell=True)
    output = output.decode("utf-8")
    return {
        "distributor_id": re.findall(r"Distributor ID:\s+(.*)$", output, re.MULTILINE)[
            0
        ],
        "description": re.findall(r"Description:\s+(.*)$", output, re.MULTILINE)[0],
        "release": re.findall(r"Release:\s+(.*)$", output, re.MULTILINE)[0],
        "codename": re.findall(r"Codename:\s+(.*)$", output, re.MULTILINE)[0],
        "deployer_version": f"ardana-{ardana_version}",
        "pip_mirror": "OBS",
    }


def _pip_freeze(dest_dir):
    """Return the output from `pip freeze`."""
    output = subprocess.check_output(
        f"cd {dest_dir}; source bin/activate; pip freeze", shell=True
    )
    output = output.decode("utf-8")
    return output.split("\n")


def add_meta_inf(dest_dir, version, ardana_version):
    """Add META-INF directory content."""
    meta_inf = os.path.join(dest_dir, "META-INF")
    os.mkdir(meta_inf)

    service, timestamp = os.path.basename(dest_dir).rsplit("-", 1)

    # Add version YAML file
    version_yml = os.path.join(meta_inf, "version.yml")
    with open(version_yml, "w+") as f:
        print(LICENSE, file=f)
        print(file=f)
        print(f"# Version for: {service}", file=f)
        print("---", file=f)
        print(file=f)
        print("file_format: 1", file=f)
        print(f"version: {version}", file=f)
        print(f"timestamp: {timestamp}", file=f)

    release = _os_release(ardana_version)
    pip_freeze = _pip_freeze(dest_dir)

    # Add manifest YAML file
    manifest_yml = os.path.join(meta_inf, "manifest.yml")
    with open(manifest_yml, "w+") as f:
        print(f"# Manifest for: {service}", file=f)
        print("---", file=f)
        print(file=f)

        print("# Ardana environment", file=f)
        print("environment:", file=f)
        for key, value in release.items():
            print(f"  {key}: {value}", file=f)
        print(file=f)

        print("# Pip freeze output", file=f)
        print("pip: |", file=f)
        for line in pip_freeze:
            print(f"  {line}", file=f)


def create(args):
    """Function called for the `create` command."""
    # Create the virtual environment
    options = []
    if args.system_site_packages:
        options.append("--system-site-packages")
    options = " ".join(options)
    subprocess.call(f"virtualenv {options} {args.dest_dir}", shell=True)

    # Prepare the links for /usr/bin and /usr/lib[64]
    usr = os.path.join(args.dest_dir, "usr")
    os.mkdir(usr)
    os.symlink("../bin", os.path.join(usr, "bin"))
    os.symlink("../lib", os.path.join(usr, "lib"))
    os.symlink("../lib", os.path.join(usr, "lib64"))

    # If both are populated, the algorithm will take precedence over
    # the `exclude` list
    include = FileList(args.include)
    exclude = FileList(args.exclude)

    # Install the packages and maintain a log
    included = []
    excluded = []
    for package in glob.glob(os.path.join(args.repo, "*.rpm")):
        rpm = os.path.basename(package)
        if rpm in exclude:
            excluded.append(rpm)
            continue
        if include.is_populated() and rpm not in include:
            excluded.append(rpm)
            continue
        included.append(rpm)

        package = os.path.abspath(package)
        subprocess.call(
            f"cd {args.dest_dir}; rpm2cpio {package} | "
            "cpio --extract --unconditional "
            "--preserve-modification-time --make-directories "
            "--extract-over-symlinks",
            stdout=subprocess.DEVNULL,
            shell=True,
        )

    add_meta_inf(args.dest_dir, args.version, args.ardana_version)

    _fix_virtualenv(args.dest_dir, args.relocate, args.no_relocate_shebang_list)

    # Write the log file, useful to better taylor the inclusion /
    # exclusion of packages.
    with open(os.path.join(args.dest_dir, "packages.log"), "w") as f:
        print("# Included packages", file=f)
        for rpm in sorted(included):
            print(rpm, file=f)
        print("\n\n# Excluded packages", file=f)
        for rpm in sorted(excluded):
            print(rpm, file=f)

    # Write the L3/Maintenance track file, required to track the
    # content of the venv inside OBS.
    query = "|".join(
        ("%{NAME}", "%{EPOCH}", "%{VERSION}", "%{RELEASE}", "%{ARCH}", "%{DISTURL}")
    )
    with open(args.track, "w") as f:
        for rpm in sorted(included):
            rpm = os.path.join(args.repo, rpm)
            output = subprocess.check_output(
                f"rpm -qp --queryformat='{query}' {rpm}",
                stderr=subprocess.DEVNULL,
                shell=True,
            )
            print(output.decode("utf-8"), file=f)


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
    """Filter a list of RPM names"""
    exclude = FileList(args.exclude)
    if args.all:
        return names
    else:
        return [rpm for rpm in names if rpm not in exclude]


def _repository(args):
    """List binary packages from a repository"""
    api = f"/build/{args.project}/{args.repo}/{args.arch}/_repository"
    output = subprocess.check_output(
        f"osc --apiurl {args.apiurl} api {api}", shell=True
    )
    elements = _filter_binary_xml(ET.fromstring(output))
    # Unversioned name, so we remove the file extension
    elements = [rpm.replace(".rpm", "") for rpm in elements]
    return _filter_binary_name(elements, args)


def include(args):
    """Generate initial include-rpm file"""
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

    # OBS generate a full RPM package name, including the version and
    # architecture.  To generate include-rpm and exclude-rpm, we will
    # need only the name of the package
    rpm_re = re.compile(r"(.*)-([^-]+)-([^-]+)\.([^-\.]+)\.rpm")

    api = f"/build/{args.project}/{args.repo}/{args.arch}/{args.package}"
    output = subprocess.check_output(
        f"osc --apiurl {args.apiurl} api {api}", shell=True
    )
    elements = _filter_binary_xml(ET.fromstring(output))
    # Take only the name of the package
    elements = [rpm_re.match(rpm).groups()[0] for rpm in elements]
    elements = _filter_binary_name(elements, args)
    for rpm in elements:
        print(rpm)


def _filter_requires_spec(spec):
    """Recover the Requires elements from a spec file"""
    requires = re.findall(r"^Requires:\s*([-\.\w]+)(.*)?$", spec, re.MULTILINE)
    return dict(requires)


def requires(args):
    """List requirements for a source package"""

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
    for rpm in requires:
        if rpm in exclude:
            continue
        if include.is_populated() and rpm not in include:
            continue
        in_venv.append(rpm)
    requires = set(requires) - set(in_venv)

    for rpm in sorted(requires):
        requires = f"{rpm} {requires_and_version[rpm].strip()}"
        print(requires.strip())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Utility to help venvs creation for OpenStack services"
    )
    subparsers = parser.add_subparsers(help="Sub-commands for venvjail")

    # Parser for `create` command
    subparser = subparsers.add_parser("create", help="Create a virtualenv")
    subparser.add_argument(
        "dest_dir", metavar="DEST_DIR", help="Virtual environment directory"
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
        default="/opt/stack/venv",
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
        "-r", "--repo", default="/.build.binaries", help="Repository directory"
    )
    subparser.add_argument(
        "-i",
        "--include",
        default="include-rpm",
        help="File with the list of packages to install",
    )
    subparser.add_argument(
        "-x", "--exclude", default="exclude-rpm", help="File with packages to exclude"
    )
    subparser.add_argument(
        "-t", "--track", help="Filename for the L3/Maintenance track file"
    )
    subparser.add_argument("-v", "--version", default="0.1.0", help="Package version")
    subparser.add_argument(
        "-a", "--ardana-version", default="0.9.0", help="Ardana version"
    )
    subparser.set_defaults(func=create)

    # Parser for `include` command
    subparser = subparsers.add_parser(
        "include", help="Generate initial include-rpm file"
    )
    subparser.add_argument(
        "-A", "--apiurl", default="https://api.opensuse.org", help="API address"
    )
    subparser.add_argument(
        "-p", "--project", default="Cloud:OpenStack:Master", help="Project name"
    )
    subparser.add_argument("-r", "--repo", default="SLE_12_SP3", help="Repository name")
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
    subparser.add_argument(
        "-p", "--project", default="Cloud:OpenStack:Master", help="Project name"
    )
    subparser.add_argument("-r", "--repo", default="SLE_12_SP3", help="Repository name")
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
    subparser.add_argument(
        "-p", "--project", default="Cloud:OpenStack:Master", help="Project name"
    )
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
    args.func(args)
