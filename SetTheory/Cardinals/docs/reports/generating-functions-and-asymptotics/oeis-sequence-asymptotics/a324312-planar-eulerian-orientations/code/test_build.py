#!/usr/bin/env python3
"""Test ZIP metadata, hashes, deterministic ordering and deliberate build failures."""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import zipfile

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import build
from companion import ValidationError, json_bytes, require, write_new
from test_companion import expect_error


def run_tests():
    passed = []
    with tempfile.TemporaryDirectory(prefix="report171-zip-test-") as temporary:
        work = Path(temporary)
        tree = work / "tree"
        tree.mkdir()
        (tree / "z.txt").write_text("zeta\n")
        (tree / "a.txt").write_text("alpha\n")
        expected = build.manifest(tree)
        require(expected["a.txt"] == hashlib.sha256(b"alpha\n").hexdigest(), "hash mismatch")
        write_new(tree / "SHA256SUMS.json", json_bytes(expected))
        first, second = work / "one.zip", work / "two.zip"
        build.make_zip_bytes_tree(tree, first)
        build.make_zip_bytes_tree(tree, second)
        require(first.read_bytes() == second.read_bytes(), "ZIP bytes not reproducible")
        passed.append("two_ZIPs_identical")
        with zipfile.ZipFile(first) as archive:
            require(archive.namelist() == sorted(archive.namelist()), "ZIP member ordering")
            for item in archive.infolist():
                require(item.date_time == build.ZIP_TIME and item.external_attr >> 16 == 0o100644,
                        "ZIP metadata changed")
            for name, digest in expected.items():
                require(hashlib.sha256(archive.read(name)).hexdigest() == digest, "archived hash mismatch")
        passed.extend(["fixed_timestamps_permissions", "sorted_members", "archive_hashes_verified"])
        expect_error(FileExistsError, build.make_zip_bytes_tree, tree, first)
        passed.append("existing_archive_rejected")
        expect_error(ValidationError, build.build, first)
        passed.append("build_destination_no_clobber")
        target = work / "same"
        expect_error(ValidationError, build.build, target, target)
        passed.append("duplicate_destinations_rejected")
        # Compiler-control tests use a local deterministic fake TeX process;
        # they test stabilization and rejection without depending on installed TeX.
        source = work / "source.tex"
        source.write_text("test source\n")
        original_run = build.run
        try:
            for label, defect, changing, bad_pdf, expected_passes in [
                    ("aux_stabilizes_after_two", "", False, False, 2),
                    ("overfull_box_rejected", "Overfull \\hbox (3.0pt too wide)", False, False, None),
                    ("missing_glyph_rejected", "Missing character: There is no X", False, False, None),
                    ("undefined_references_rejected", "There were undefined references", False, False, None),
                    ("six_pass_limit_enforced", "", True, False, None),
                    ("invalid_pdf_rejected", "", False, True, None)]:
                tex = work / label
                tex.mkdir()
                calls = [0]

                def fake_run(command, cwd, env, timeout=600):
                    calls[0] += 1
                    (tex / "Report171.aux").write_text(str(calls[0]) if changing else "stable")
                    (tex / "Report171.log").write_text(defect)
                    (tex / "Report171.pdf").write_bytes(b"invalid" if bad_pdf else b"%PDF-test")
                    return ""

                build.run = fake_run
                if expected_passes is None:
                    expect_error(ValidationError, build.compile_pdf, source, tex, {})
                else:
                    require(build.compile_pdf(source, tex, {}) == expected_passes, "compile pass count")
                require(calls[0] <= 6, "compiler exceeded pass limit")
                passed.append(label)
        finally:
            build.run = original_run
    return {"schema": "Report171-build-tests-v1", "optimization_level": sys.flags.optimize,
            "status": "passed", "count": len(passed), "tests": passed}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.output and (args.output.exists() or args.output.is_symlink()):
        parser.error("refusing existing output")
    data = json_bytes(run_tests())
    if args.output:
        write_new(args.output, data)
    else:
        sys.stdout.buffer.write(data)


if __name__ == "__main__":
    main()
