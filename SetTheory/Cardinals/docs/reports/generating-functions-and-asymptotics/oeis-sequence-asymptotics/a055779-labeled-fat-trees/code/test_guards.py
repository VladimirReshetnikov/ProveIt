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
import re
from decimal import Decimal

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

spec = importlib.util.spec_from_file_location("report203_builder_guards", HERE/"build.py")
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


def article_examples(tex, exact, diagnostics):
    """Compare public numerical displays with data actually replayed by the build."""
    checked = []
    enumeration = {row['n']: row['polynomial'] for row in exact['original_model_enumeration']}
    examples = re.findall(r'A_(\d+)\(M\)&?=([^,\\\n]+)', tex)
    require({int(n) for n, value in examples} == {1, 2, 3, 6}, 'Unexpected article polynomial display set')
    for n, value in examples:
        coefficients = {}
        for term in value.replace(' ', '').rstrip('.').split('+'):
            match = re.fullmatch(r'(\d*)M(?:\^(\d+))?', term)
            if match:
                coefficient = int(match.group(1) or '1')
                degree = int(match.group(2) or '1')
            else:
                require(term.isdigit(), 'Unsupported article polynomial term')
                coefficient, degree = int(term), 0
            coefficients[degree] = coefficients.get(degree, 0) + coefficient
        vector = [coefficients.get(k, 0) for k in range(max(coefficients)+1)]
        require(vector == enumeration[int(n)], 'Article small-n polynomial mismatch at n='+n)
        checked.append('article exact polynomial n='+n)
    sequence = re.findall(r'first six values are \$([^$]+)\$', tex)
    require(len(sequence) == 1, 'Expected one first-six-term display')
    require([int(x) for x in sequence[0].split(',')] == [sum(enumeration[n]) for n in range(1, 7)],
            'Article first-six-term display disagrees with exact enumeration')
    checked.append('article first six values from original model enumeration')
    rows = re.findall(r'^(20|80|320|640) & \$([^$]+)\$ & \$([^$]+)\$\\\\$', tex, flags=re.MULTILINE)
    require([int(row[0]) for row in rows] == [20, 80, 320, 640], 'Unexpected diagnostic table rows')
    values = {row['n']:row for row in diagnostics['asymptotics'] if row['kind'] == 'fixed_1'}
    def rounded(value):
        return format(Decimal(value).quantize(Decimal('0.000000000001')), '.12f')
    for n, first, second in rows:
        for j, shown in enumerate((first, second)):
            require(shown == rounded(values[int(n)]['scaled_remainders_J0_to_J3'][j]),
                    'Article rounded diagnostic mismatch at n='+n+', column='+str(j+1))
            checked.append('article rounded diagnostic n='+n+', column='+str(j+1))
    limits = re.findall(r'^Predicted limit & \$([^$]+)\$ & \$([^$]+)\$\\\\$', tex, flags=re.MULTILINE)
    require(len(limits) == 1, 'Expected one predicted-limit row')
    for j, shown in enumerate(limits[0]):
        require(shown == rounded(values[20]['next_coefficients_c1_to_c4'][j]),
                'Article rounded predicted limit mismatch')
        checked.append('article rounded predicted limit column='+str(j+1))
    return checked


def main():
    passed = []
    for name in ("", "/Report203.tex", "../Report203.tex", "repro/../build.py", "./build.py",
                 "repro//check.py", "repro\\check.py", "repro/check.py/", "x\x00y", "a b", "C:/file"):
        passed.append(rejected(lambda name=name:builder.safe_relative(name), builder.BuildError,
                               "invalid manifest path "+repr(name)))
    with tempfile.TemporaryDirectory(prefix="report203-guard-tests-") as temp:
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
        package_case("corrupt source bytes", lambda root:(root/"Report203.tex").write_text("changed"))
        package_case("corrupt data bytes", lambda root:(root/"code/expected/exact_checks.json").write_text("changed"))
        package_case("corrupt PDF bytes", lambda root:(root/"Report203.pdf").write_bytes(b"changed"))
        package_case("symlink public file", lambda root:((root/"README.md").unlink(),
                     (root/"README.md").symlink_to("Report203.tex")))
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
    tex = (HERE/'Report203.tex').read_text(encoding='utf-8')
    exact = json.loads((HERE/'code/expected/exact_checks.json').read_text(encoding='utf-8'))
    diagnostics = json.loads((HERE/'code/expected/numerical_diagnostics.json').read_text(encoding='utf-8'))
    passed.extend(article_examples(tex, exact, diagnostics))
    passed.append(rejected(lambda:article_examples(tex.replace('A_2(M)=1+M','A_2(M)=1+2M'),
                          exact,diagnostics), RuntimeError, 'incorrect printed polynomial rejected'))
    passed.append(rejected(lambda:article_examples(tex.replace('-0.023143706446$','-0.023143706445$'),
                          exact,diagnostics), RuntimeError, 'incorrect printed rounding rejected'))
    print(json.dumps({"status":"PASS", "guard_checks":len(passed), "checks":passed}, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
