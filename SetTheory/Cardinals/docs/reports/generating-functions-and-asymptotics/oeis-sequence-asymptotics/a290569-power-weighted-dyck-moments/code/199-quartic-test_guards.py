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
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import exact

spec = importlib.util.spec_from_file_location("report199_builder_guards", HERE.parent/"build.py")
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
    for value in (-1, 2001, True, False, 1.0, "3", None):
        passed.append(rejected(lambda value=value: exact.exact_moments(value, lambda h:h**4),
            exact.VerificationError, "invalid moment limit "+repr(value)))
    for weight in (lambda h:0, lambda h:-h, lambda h:1.0, lambda h:True):
        passed.append(rejected(lambda weight=weight: exact.exact_moments(2, weight),
            exact.VerificationError, "invalid nonpositive or noninteger weight"))
    for exponent in (True, 1.0, "-2", None):
        passed.append(rejected(lambda exponent=exponent: exact.power_coefficients([1,1], exponent, 1),
            exact.VerificationError, "invalid power exponent "+repr(exponent)))
    for m in ([0,1], [1,1.0], [1,True]):
        passed.append(rejected(lambda m=m: exact.power_coefficients(m, -2, 1),
            exact.VerificationError, "invalid formal series "+repr(m)))
    valid = {"schema":"report199-exact-values-v1", "moment_limit":500, "cumulant_limit":160,
             "m":["1"]*501, "four_gamma":["1"]*501, "a":["1"]*161}
    exact.validate_values(valid)
    mutations = [
        ("extra values key", lambda v:v.update(extra=1)),
        ("missing values key", lambda v:v.pop("a")),
        ("wrong values schema", lambda v:v.update(schema="other")),
        ("boolean moment limit", lambda v:v.update(moment_limit=True)),
        ("float cumulant limit", lambda v:v.update(cumulant_limit=160.0)),
        ("short integer array", lambda v:v["m"].pop()),
        ("numeric rather than string integer", lambda v:v["a"].__setitem__(1,1)),
        ("noncanonical leading zero", lambda v:v["a"].__setitem__(1,"01")),
        ("negative integer string", lambda v:v["a"].__setitem__(1,"-1")),
        ("signed integer string", lambda v:v["a"].__setitem__(1,"+1")),
        ("noninteger string", lambda v:v["a"].__setitem__(1,"1.0")),
        ("whitespace integer string", lambda v:v["a"].__setitem__(1,"1 ")),
        ("wrong constant coefficient", lambda v:v["m"].__setitem__(0,"0")),
    ]
    for name, mutate in mutations:
        value = copy.deepcopy(valid)
        mutate(value)
        passed.append(rejected(lambda value=value:exact.validate_values(value), exact.VerificationError, name))
    for name in ("", "/Report199.tex", "../Report199.tex", "code/../build.py", "./build.py",
                 "code//exact.py", "code\\exact.py", "code/exact.py/", "x\x00y", "a b", "C:/file"):
        passed.append(rejected(lambda name=name:builder.safe_relative(name), builder.BuildError,
                               "invalid manifest path "+repr(name)))
    with tempfile.TemporaryDirectory(prefix="report199-guard-tests-") as temp:
        temp = Path(temp)
        raw = temp/"malformed.json"
        bad_json = [("duplicate JSON keys", '{"x":1,"x":2}'),
                    ("NaN JSON", '{"x":NaN}'), ("Infinity JSON", '{"x":Infinity}'),
                    ("truncated JSON", '{"x":'), ("trailing JSON content", '{}{}')]
        for name, text in bad_json:
            raw.write_text(text, encoding="utf-8")
            passed.append(rejected(lambda:builder.strict_json(raw), builder.BuildError, name+" in manifest"))
            passed.append(rejected(lambda:exact.load_json(raw), exact.VerificationError, name+" in exact data"))
        raw.write_bytes(b"\xff")
        passed.append(rejected(lambda:builder.strict_json(raw), builder.BuildError, "invalid manifest UTF-8"))
        passed.append(rejected(lambda:exact.load_json(raw), exact.VerificationError, "invalid exact-data UTF-8"))
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
        package_case("corrupt source bytes", lambda root:(root/"Report199.tex").write_text("changed"))
        package_case("corrupt data bytes", lambda root:(root/"data/exact_checks.json").write_text("changed"))
        package_case("corrupt PDF bytes", lambda root:(root/"Report199.pdf").write_bytes(b"changed"))
        package_case("symlink public file", lambda root:((root/"README.md").unlink(),
                     (root/"README.md").symlink_to("Report199.tex")))
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
    print(json.dumps({"status":"PASS", "guard_checks":len(passed), "checks":passed}, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
