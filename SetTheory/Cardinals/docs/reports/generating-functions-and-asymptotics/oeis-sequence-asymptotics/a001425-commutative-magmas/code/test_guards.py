#!/usr/bin/env python3
"""Adversarial input/manifest checks, active with normal Python and python -O.

Standard library only. These tests reject malformed data and altered packages;
they are independent of the mathematical and PDF replay.
"""
from __future__ import annotations
import copy
import importlib.util
import json
import os
import shutil
import subprocess
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

spec = importlib.util.spec_from_file_location("report200_builder_guards", HERE.parent/"build.py")
if spec is None or spec.loader is None:
    raise RuntimeError("Cannot load builder for guard tests")
builder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(builder)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def rejected(action, exceptions, name):
    try:
        action()
    except exceptions:
        return name
    raise RuntimeError("Guard did not reject: "+name)


def fixture(root):
    for name in builder.PUBLIC_FILES:
        path = root/name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(("fixture "+name+"\n").encode("ascii"))
    (root/builder.SOURCE_MANIFEST).write_bytes(builder.canonical_bytes(
        builder.source_manifest(root, "pdfTeX fixture-engine")))
    (root/builder.PACKAGE_MANIFEST).write_bytes(builder.canonical_bytes(builder.package_manifest(root)))
    builder.validate_package(root)


def main():
    passed = []
    for name in ("", "/Report200.tex", "../Report200.tex", "code/../build.py", "./build.py",
                 "code//magma.py", "code\\magma.py", "code/magma.py/", "x\x00y", "a b", "C:/file"):
        passed.append(rejected(lambda name=name:builder.safe_relative(name), builder.BuildError,
                               "invalid manifest path "+repr(name)))
    with tempfile.TemporaryDirectory(prefix="report200-guard-tests-") as temp:
        temp = Path(temp)
        raw = temp/"malformed.json"
        bad_json = [("duplicate JSON keys", '{"x":1,"x":2}'),
                    ("NaN JSON", '{"x":NaN}'), ("Infinity JSON", '{"x":Infinity}'),
                    ("truncated JSON", '{"x":'), ("trailing JSON content", '{}{}')]
        for name, text in bad_json:
            raw.write_text(text, encoding="utf-8")
            passed.append(rejected(lambda:builder.strict_json(raw), builder.BuildError, name+" in manifest"))
        raw.write_bytes(b"\xff")
        passed.append(rejected(lambda:builder.strict_json(raw), builder.BuildError, "invalid manifest UTF-8"))
        counter = 0
        def package_case(name, mutate):
            nonlocal counter
            counter += 1
            root = temp/str(counter)
            root.mkdir()
            fixture(root)
            mutate(root)
            passed.append(rejected(lambda:builder.validate_package(root), builder.BuildError, name))
        package_case("missing public file", lambda root:(root/"README.md").unlink())
        package_case("undeclared public file", lambda root:(root/"unlisted.txt").write_text("extra"))
        package_case("undeclared empty directory", lambda root:(root/"extra").mkdir())
        package_case("undeclared hidden source", lambda root:(root/".hidden").write_text("extra"))
        if hasattr(os, "mkfifo"):
            package_case("FIFO public member", lambda root:((root/"README.md").unlink(), os.mkfifo(root/"README.md")))
        def oversized(root):
            with (root/"README.md").open("wb") as stream:
                stream.truncate(builder.MAX_FILE_BYTES+1)
        package_case("oversized public member", oversized)
        package_case("corrupt source bytes", lambda root:(root/"Report200.tex").write_text("changed"))
        package_case("corrupt data bytes", lambda root:(root/"data/validation.json").write_text("changed"))
        package_case("corrupt PDF bytes", lambda root:(root/"Report200.pdf").write_bytes(b"changed"))
        package_case("symlink public file", lambda root:((root/"README.md").unlink(),
                     (root/"README.md").symlink_to("Report200.tex")))
        def edit_manifest(root, source, transform):
            name = builder.SOURCE_MANIFEST if source else builder.PACKAGE_MANIFEST
            value = builder.strict_json(root/name)
            transform(value)
            (root/name).write_bytes(builder.canonical_bytes(value))
        cases = [
            ("wrong manifest schema", lambda x:x.update(schema="wrong")),
            ("extra manifest key", lambda x:x.update(extra=True)),
            ("missing manifest record", lambda x:x["files"].pop()),
            ("duplicate manifest record", lambda x:x["files"].__setitem__(1,x["files"][0])),
            ("out-of-order manifest", lambda x:x["files"].reverse()),
            ("manifest traversal path", lambda x:x["files"][0].update(path="../README.md")),
            ("absolute manifest path", lambda x:x["files"][0].update(path="/README.md")),
            ("noncanonical manifest path", lambda x:x["files"][0].update(path="./README.md")),
            ("boolean manifest byte count", lambda x:x["files"][0].update(bytes=True)),
            ("float manifest byte count", lambda x:x["files"][0].update(bytes=1.0)),
            ("negative manifest byte count", lambda x:x["files"][0].update(bytes=-1)),
            ("bad manifest hash length", lambda x:x["files"][0].update(sha256="a"*63)),
            ("uppercase manifest hash", lambda x:x["files"][0].update(sha256="A"*64)),
            ("incorrect valid hash", lambda x:x["files"][0].update(sha256="0"*64)),
            ("extra file-record key", lambda x:x["files"][0].update(extra=0)),
        ]
        for source in (True, False):
            for name, transform in cases:
                package_case(("source " if source else "package ")+name,
                    lambda root, source=source, transform=transform:edit_manifest(root, source, transform))
        package_case("wrong source epoch", lambda root:edit_manifest(root, True,
                     lambda x:x.update(source_date_epoch="0")))
        package_case("invalid engine banner", lambda root:edit_manifest(root, True,
                     lambda x:x.update(pdf_engine_banner=42)))
        package_case("noncanonical source-manifest bytes", lambda root:(root/builder.SOURCE_MANIFEST).write_bytes(
                     (root/builder.SOURCE_MANIFEST).read_bytes()+b"\n"))
        package_case("noncanonical package-manifest bytes", lambda root:(root/builder.PACKAGE_MANIFEST).write_bytes(
                     (root/builder.PACKAGE_MANIFEST).read_bytes()+b"\n"))
        # Deterministic ZIP creation uses fixed metadata and uncompressed members.
        root = temp/"zip-fixture"
        root.mkdir()
        fixture(root)
        z1, z2 = temp/"one.zip", temp/"two.zip"
        h1, h2 = builder.deterministic_zip(root,z1), builder.deterministic_zip(root,z2)
        require(h1 == h2 and z1.read_bytes() == z2.read_bytes(), "ZIP byte determinism failed")
        passed.append("deterministic ZIP bytes")
        passed.append(rejected(lambda:builder.build(root,root,temp/"fresh.zip"), builder.BuildError,
                               "build output cannot equal source"))
        passed.append(rejected(lambda:builder.build(root,root/"child",temp/"fresh.zip"), builder.BuildError,
                               "build output cannot be nested in source"))
        passed.append(rejected(lambda:builder.build(root,temp,temp/"fresh.zip"), builder.BuildError,
                               "build output cannot contain source"))
        passed.append(rejected(lambda:builder.build(root,temp/"fresh-output",root/"new.zip"), builder.BuildError,
                               "build archive cannot modify source"))
        passed.append(rejected(lambda:builder.deterministic_zip(root,z1), builder.BuildError,
                               "existing ZIP is not overwritten"))
        passed.append(rejected(lambda:builder.deterministic_zip(root,root/"nested.zip"), builder.BuildError,
                               "ZIP cannot be nested inside its package"))
        dangling_zip = temp/"dangling.zip"
        dangling_zip.symlink_to(temp/"uncreated.zip")
        passed.append(rejected(lambda:builder.deterministic_zip(root,dangling_zip), builder.BuildError,
                               "dangling archive symlink rejected by ZIP writer"))
        passed.append(rejected(lambda:builder.build(root,temp/"fresh-build",dangling_zip), builder.BuildError,
                               "dangling archive symlink rejected by builder"))
        dangling_output = temp/"dangling-output"
        dangling_output.symlink_to(temp/"uncreated-output")
        passed.append(rejected(lambda:builder.build(root,dangling_output,temp/"fresh-archive.zip"), builder.BuildError,
                               "dangling output symlink rejected by builder"))
        require(not (temp/"uncreated.zip").exists() and not (temp/"uncreated-output").exists(),
                "Rejected dangling destination created its target")
    # The README's direct data-only command must not create local bytecode.
    with tempfile.TemporaryDirectory(prefix="report200-direct-regression-") as temp:
        root = Path(temp)/"source"
        code = root/"code"
        code.mkdir(parents=True)
        for name in ("check.py", "magma.py"):
            shutil.copyfile(HERE/name, code/name)
        before = {p.relative_to(root).as_posix(): p.read_bytes()
                  for p in root.rglob("*") if p.is_file()}
        env = {**os.environ}
        env.pop("PYTHONDONTWRITEBYTECODE", None)
        env.pop("PYTHONPYCACHEPREFIX", None)
        command = [sys.executable]
        if sys.flags.optimize: command.append("-O")
        command += ["-S", str(code/"check.py"), "--exact-only", "--output-dir", str(Path(temp)/"data")]
        result = subprocess.run(command, capture_output=True, text=True, env=env, timeout=120)
        require(result.returncode == 0, "Direct exact-only regression failed: "+result.stderr)
        after = {p.relative_to(root).as_posix(): p.read_bytes()
                 for p in root.rglob("*") if p.is_file()}
        require(before == after and not list(root.rglob("__pycache__")),
                "Direct command modified its source package")
        passed.append("direct exact-only command leaves source unchanged with bytecode environment unset")
    print(json.dumps({"status":"PASS", "guard_checks":len(passed), "checks":passed}, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
