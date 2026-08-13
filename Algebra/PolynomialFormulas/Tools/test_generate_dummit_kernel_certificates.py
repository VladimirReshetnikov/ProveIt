#!/usr/bin/env python3
"""Regression tests for focused Dummit certificate generator modes."""

from pathlib import Path
import os
import subprocess
import sys
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

import generate_dummit_kernel_certificates as generator


ROW_LENGTHS = (138, 86, 44, 22)
GENERATED_SUFFIXES = (
    "Data",
    "Certificate",
    "State0Data",
    "State12NormalizeRawCertificate",
)

SYNTHETIC_TAIL_ROW = [
    (1, (1, 0, 0, 0, 0)),
    (-2, (0, 1, 0, 0, 0)),
    (3, (0, 0, 1, 0, 0)),
    (-4, (0, 0, 0, 1, 0)),
    (5, (0, 0, 0, 0, 0)),
    (6, (1, 0, 0, 0, 0)),
    (-7, (0, 1, 0, 0, 0)),
    (8, (0, 0, 1, 0, 0)),
]


def term_name(table: int, position: int, suffix: str) -> str:
    return f"{generator.PREFIX}Table{table}Term{position}{suffix}"


class TableTermOwnershipTest(unittest.TestCase):
    def test_exhaustive_cross_position_ownership(self) -> None:
        for table, row_length in enumerate(ROW_LENGTHS):
            for target in range(row_length):
                for actual in range(row_length):
                    for suffix in GENERATED_SUFFIXES:
                        name = term_name(table, actual, suffix)
                        self.assertEqual(
                            generator.owns_table_term_target(
                                name, table, target),
                            actual == target,
                            (table, target, actual, suffix),
                        )

        for table, row_length in enumerate(ROW_LENGTHS):
            other_table = (table + 1) % len(ROW_LENGTHS)
            for target in range(row_length):
                self.assertFalse(generator.owns_table_term_target(
                    term_name(other_table, 0, "Data"), table, target))

    def test_every_ambiguous_target_rejects_descendants(self) -> None:
        expected_ambiguous = {
            0: set(range(1, 14)),
            1: set(range(1, 9)),
            2: set(range(1, 5)),
            3: {1, 2},
        }
        for table, row_length in enumerate(ROW_LENGTHS):
            actual_ambiguous: set[int] = set()
            for target in range(row_length):
                descendants = [
                    actual for actual in range(row_length)
                    if actual != target and
                    str(actual).startswith(str(target))
                ]
                if descendants:
                    actual_ambiguous.add(target)
                for actual in descendants:
                    self.assertFalse(generator.owns_table_term_target(
                        term_name(table, actual, "Data"), table, target))
            self.assertEqual(actual_ambiguous, expected_ambiguous[table])

    def test_manifest_filters_descendants_and_has_exact_bytes(self) -> None:
        target_modules = {
            term_name(0, 2, "Data"),
            term_name(0, 2, "Certificate"),
            term_name(0, 2, "State0Data"),
        }
        descendant_modules = {
            term_name(0, 20, "Data"),
            term_name(0, 29, "Certificate"),
        }
        unrelated = generator.RAW_MUL_APPEND_MODULE
        written = target_modules | descendant_modules | {unrelated}

        with TemporaryDirectory() as directory:
            lean_dir = Path(directory)
            for module in target_modules | descendant_modules:
                (lean_dir / f"{module}.lean").write_text("source\n")
            with (
                    patch.object(generator, "LEAN_DIR", lean_dir),
                    patch.object(generator, "WRITTEN_MODULES", written)):
                generator.write_target_manifest_and_check(0, 2)

            manifest = lean_dir / (
                f"{generator.PREFIX}Table0Term2GeneratedFiles.txt")
            expected = "".join(
                f"{module}.lean\n" for module in sorted(target_modules))
            self.assertEqual(manifest.read_bytes(), expected.encode("utf-8"))

    def test_same_owner_stale_file_fails_closed(self) -> None:
        data = term_name(0, 2, "Data")
        stale = term_name(0, 2, "LegacyShard")
        with TemporaryDirectory() as directory:
            lean_dir = Path(directory)
            (lean_dir / f"{data}.lean").write_text("source\n")
            (lean_dir / f"{stale}.lean").write_text("stale\n")
            with (
                    patch.object(generator, "LEAN_DIR", lean_dir),
                    patch.object(generator, "WRITTEN_MODULES", {data})):
                with self.assertRaisesRegex(
                        RuntimeError,
                        rf"stale generated shards: {stale}\.lean"):
                    generator.write_target_manifest_and_check(0, 2)

    def test_missing_expected_file_fails_closed(self) -> None:
        missing = term_name(0, 2, "Data")
        with TemporaryDirectory() as directory:
            lean_dir = Path(directory)
            with (
                    patch.object(generator, "LEAN_DIR", lean_dir),
                    patch.object(generator, "WRITTEN_MODULES", {missing})):
                with self.assertRaisesRegex(
                        RuntimeError,
                        rf"missing generated shards: {missing}\.lean"):
                    generator.write_target_manifest_and_check(0, 2)

    def test_legacy_equivalence_for_established_targets(self) -> None:
        established = (51, 72, 85, 86, 87, 90,
                       109, 110, 111, 120, 125, 131)
        for position in established:
            prefix = f"{generator.PREFIX}Table0Term{position}"
            names = [
                *(f"{prefix}{suffix}" for suffix in GENERATED_SUFFIXES),
                f"{prefix}LegacyShard",
                term_name(0, 0, "Data"),
                generator.RAW_MUL_APPEND_MODULE,
            ]
            for name in names:
                self.assertEqual(
                    generator.owns_table_term_target(name, 0, position),
                    name.startswith(prefix),
                    (position, name),
                )


class RootOwnershipTest(unittest.TestCase):
    def test_plural_aggregate_is_owned_exactly(self) -> None:
        root = f"{generator.PREFIX}Root0Final.lean"
        root_legacy = f"{generator.PREFIX}RootLegacy.lean"
        aggregate = f"{generator.PREFIX}s.lean"
        aggregate_legacy = f"{generator.PREFIX}sLegacy.lean"
        table = f"{generator.PREFIX}Table0Final.lean"
        with TemporaryDirectory() as directory:
            lean_dir = Path(directory)
            for name in (root, root_legacy, aggregate,
                         aggregate_legacy, table):
                (lean_dir / name).write_text("source\n")
            self.assertEqual(
                generator.existing_owned_root_paths(lean_dir),
                {
                    lean_dir / root,
                    lean_dir / root_legacy,
                    lean_dir / aggregate,
                },
            )


class TailShardTest(unittest.TestCase):
    def exact_modules(self) -> tuple[str, ...]:
        prefix = f"{generator.PREFIX}Table0Tail0"
        return (
            f"{prefix}Data",
            f"{prefix}MergeStep3Data",
            f"{prefix}MergeStep2Data",
            f"{prefix}MergeStep1Data",
            f"{prefix}MergeStep3Certificate",
            f"{prefix}MergeStep2Certificate",
            f"{prefix}MergeStep1Certificate",
            f"{prefix}MergeStep0Certificate",
            f"{prefix}Certificate",
        )

    def exact_imports(self) -> dict[str, tuple[str, ...]]:
        prefix = f"{generator.PREFIX}Table0Tail0"
        tail_data = f"{prefix}Data"
        return {
            tail_data: (
                f"{generator.PREFIX}Table0RowData",
                f"{generator.PREFIX}Table0Tail1Certificate",
                *(f"{generator.PREFIX}Table0Term{position}Certificate"
                  for position in range(4)),
            ),
            f"{prefix}MergeStep3Data": (tail_data,),
            f"{prefix}MergeStep2Data": (tail_data,),
            f"{prefix}MergeStep1Data": (tail_data,),
            f"{prefix}MergeStep3Certificate": (
                f"{prefix}MergeStep3Data",),
            f"{prefix}MergeStep2Certificate": (
                f"{prefix}MergeStep2Data",
                f"{prefix}MergeStep3Data",
            ),
            f"{prefix}MergeStep1Certificate": (
                f"{prefix}MergeStep1Data",
                f"{prefix}MergeStep2Data",
            ),
            f"{prefix}MergeStep0Certificate": (
                tail_data,
                f"{prefix}MergeStep1Data",
            ),
            f"{prefix}Certificate": (
                tail_data,
                f"{prefix}MergeStep3Certificate",
                f"{prefix}MergeStep2Certificate",
                f"{prefix}MergeStep1Certificate",
                f"{prefix}MergeStep0Certificate",
            ),
        }

    def render(self) -> tuple[dict[str, str],
                              dict[str, tuple[str, ...]]]:
        return generator.render_tail_shard_target(
            0, 0, SYNTHETIC_TAIL_ROW)

    def materialize(self, directory: Path,
                    rendered: dict[str, str]) -> dict[str, bytes]:
        payloads = generator.tail_shard_file_payloads(
            rendered, 0, 0)
        for filename, payload in payloads.items():
            (directory / filename).write_bytes(payload)
        return payloads

    def test_exact_nine_module_graph_and_stage_arithmetic(self) -> None:
        rendered, imports = self.render()
        expected_modules = set(self.exact_modules())
        self.assertEqual(len(expected_modules), 9)
        self.assertEqual(set(rendered), expected_modules)
        self.assertEqual(imports, self.exact_imports())

        plan = generator.tail_merge_shard_plan(
            0, 0, SYNTHETIC_TAIL_ROW)
        accumulator = plan.next_normal
        for step in reversed(range(generator.TABLE_BLOCK_SIZE)):
            self.assertEqual(
                plan.raw_sizes[step],
                len(plan.term_normals[step]) + len(accumulator),
            )
            accumulator = generator.independent_polynomial_add(
                plan.term_normals[step], accumulator)
            self.assertEqual(plan.stage_normals[step], accumulator)
            if step:
                literal = generator.lean_polynomial(
                    generator.table_tail_merge_step_normal(0, 0, step),
                    accumulator)
                data_module = generator.table_tail_merge_step_data_module(
                    0, 0, step)
                self.assertIn(literal, rendered[data_module])

    def test_limits_and_explicit_authorization_fail_closed(self) -> None:
        plan = generator.tail_merge_shard_plan(
            0, 0, SYNTHETIC_TAIL_ROW)
        max_raw = max(plan.raw_sizes)
        max_literal = max(len(stage) for stage in plan.stage_normals)
        with patch.object(generator, "TAIL_MERGE_RAW_LIMIT", max_raw):
            generator.validate_tail_merge_shard_plan(
                plan, SYNTHETIC_TAIL_ROW)
        with patch.object(generator, "TAIL_MERGE_RAW_LIMIT", max_raw - 1):
            with self.assertRaisesRegex(RuntimeError, "raw size"):
                generator.validate_tail_merge_shard_plan(
                    plan, SYNTHETIC_TAIL_ROW)
        with patch.object(
                generator, "TAIL_MERGE_LITERAL_LIMIT", max_literal):
            generator.validate_tail_merge_shard_plan(
                plan, SYNTHETIC_TAIL_ROW)
        with patch.object(
                generator, "TAIL_MERGE_LITERAL_LIMIT", max_literal - 1):
            with self.assertRaisesRegex(RuntimeError, "literal size"):
                generator.validate_tail_merge_shard_plan(
                    plan, SYNTHETIC_TAIL_ROW)
        with self.assertRaisesRegex(RuntimeError, "unauthorized"):
            generator.tail_merge_shard_plan(0, 1, SYNTHETIC_TAIL_ROW)
        with self.assertRaisesRegex(RuntimeError, "unauthorized"):
            generator.tail_merge_shard_plan(1, 0, SYNTHETIC_TAIL_ROW)

    def test_tail_data_matches_unchanged_direct_formula(self) -> None:
        rendered, _ = self.render()
        groups = [
            SYNTHETIC_TAIL_ROW[start:start + generator.TABLE_BLOCK_SIZE]
            for start in range(
                0, len(SYNTHETIC_TAIL_ROW), generator.TABLE_BLOCK_SIZE)
        ]
        suffix: generator.Polynomial = {}
        suffix_normals: dict[int, generator.Polynomial] = {
            len(groups): suffix,
        }
        for group in reversed(range(len(groups))):
            suffix = generator.add(*(
                generator.substitute_term(term) for term in groups[group]),
                suffix)
            suffix_normals[group] = suffix
        positions = (0, 1, 2, 3)
        imports = [
            f"{generator.PREFIX}Table0RowData",
            generator.table_tail_certificate_module(0, 1),
            *(generator.table_term_certificate_module(0, position)
              for position in positions),
        ]
        normal_terms = [
            generator.table_term_normal(0, position)
            for position in positions
        ]
        declarations = [
            generator.lean_polynomial(
                generator.table_tail_normal(0, 0), suffix_normals[0]),
            "def table0Tail0Candidate : SparsePolynomial :=\n  "
            + generator.nested_add(
                normal_terms, generator.table_tail_normal(0, 1)),
        ]
        expected = generator.module_text(imports, declarations)
        self.assertEqual(
            rendered[generator.table_tail_data_module(0, 0)], expected)

    def test_public_proof_text_retains_endpoints(self) -> None:
        rendered, _ = self.render()
        module = generator.table_tail_certificate_module(0, 0)
        payload = rendered[module]
        self.assertIn(
            "theorem table0_tail0_merge_certificate :\n"
            "    table0Tail0Candidate = table0Tail0Normal := by",
            payload,
        )
        final = generator.tail_public_certificate_declaration(
            0, 0, SYNTHETIC_TAIL_ROW, (0, 1, 2, 3))
        self.assertEqual(payload.count(final), 1)
        ordered = ", ".join(
            generator.table_tail_merge_step_certificate(0, 0, step)
            for step in (3, 2, 1, 0))
        self.assertIn(f"  rw [{ordered}]", payload)
        self.assertNotIn("  decide", payload)
        for step in (3, 2, 1, 0):
            certificate = rendered[
                generator.table_tail_merge_step_certificate_module(
                    0, 0, step)]
            self.assertIn("set_option maxHeartbeats 20000000", certificate)
            self.assertIn("  decide", certificate)

    def test_tail_one_does_not_own_tail_ten(self) -> None:
        tail1 = f"{generator.PREFIX}Table0Tail1Data.lean"
        tail10 = f"{generator.PREFIX}Table0Tail10Data.lean"
        self.assertTrue(generator.owns_table_tail_target(tail1, 0, 1))
        self.assertFalse(generator.owns_table_tail_target(tail10, 0, 1))
        with TemporaryDirectory() as directory:
            lean_dir = Path(directory)
            (lean_dir / tail1).write_text("one\n")
            (lean_dir / tail10).write_text("ten\n")
            self.assertEqual(
                generator.existing_owned_tail_paths(0, 1, lean_dir),
                {lean_dir / tail1},
            )

    def test_manifest_missing_stale_and_reconcile_behavior(self) -> None:
        rendered, _ = self.render()
        manifest_name = generator.tail_shard_manifest_name(0, 0)
        expected_manifest = "".join(
            f"{module}.lean\n" for module in sorted(self.exact_modules())
        ).encode("utf-8")
        self.assertEqual(
            generator.tail_shard_manifest_bytes(rendered),
            expected_manifest,
        )
        with TemporaryDirectory() as directory:
            lean_dir = Path(directory)
            with self.assertRaisesRegex(RuntimeError, r"missing \(10\)"):
                generator.check_tail_shard_target(
                    0, 0, SYNTHETIC_TAIL_ROW, lean_dir)

            payloads = self.materialize(lean_dir, rendered)
            fixed_time = 1_700_000_000_000_000_000
            for filename in payloads:
                os.utime(lean_dir / filename,
                         ns=(fixed_time, fixed_time))
            generator.write_tail_shard_target(
                0, 0, SYNTHETIC_TAIL_ROW, lean_dir)
            self.assertTrue(all(
                (lean_dir / filename).stat().st_mtime_ns == fixed_time
                for filename in payloads))
            self.assertEqual(
                (lean_dir / manifest_name).read_bytes(), expected_manifest)
            digest = generator.check_tail_shard_target(
                0, 0, SYNTHETIC_TAIL_ROW, lean_dir)
            self.assertEqual(digest, generator.tail_shard_digest(rendered))

            stale_name = f"{generator.PREFIX}Table0Tail0Legacy.lean"
            (lean_dir / stale_name).write_text("stale\n")
            with self.assertRaisesRegex(RuntimeError, r"unexpected \(1\)"):
                generator.write_tail_shard_target(
                    0, 0, SYNTHETIC_TAIL_ROW, lean_dir)
            (lean_dir / stale_name).unlink()

            changed_name = generator.table_tail_certificate_module(
                0, 0) + ".lean"
            (lean_dir / changed_name).write_text("changed\n")
            with self.assertRaisesRegex(
                    RuntimeError, r"stale-content \(1\)"):
                generator.check_tail_shard_target(
                    0, 0, SYNTHETIC_TAIL_ROW, lean_dir)
            generator.write_tail_shard_target(
                0, 0, SYNTHETIC_TAIL_ROW, lean_dir)
            self.assertEqual(
                (lean_dir / changed_name).read_bytes(),
                payloads[changed_name],
            )

            missing_name = generator.table_tail_merge_step_data_module(
                0, 0, 2) + ".lean"
            (lean_dir / missing_name).unlink()
            with self.assertRaisesRegex(RuntimeError, r"missing \(1\)"):
                generator.check_tail_shard_target(
                    0, 0, SYNTHETIC_TAIL_ROW, lean_dir)

    def test_symlink_and_nonregular_paths_are_refused_before_writes(
            self) -> None:
        rendered, _ = self.render()
        expected_name = generator.table_tail_data_module(0, 0) + ".lean"
        unexpected_name = f"{generator.PREFIX}Table0Tail0Legacy.lean"
        with TemporaryDirectory() as directory:
            lean_dir = Path(directory)
            target = lean_dir / "target"
            target.write_text("target\n")
            (lean_dir / expected_name).symlink_to(target)
            with self.assertRaisesRegex(RuntimeError, "non-regular"):
                generator.write_tail_shard_target(
                    0, 0, SYNTHETIC_TAIL_ROW, lean_dir)
            manifest = lean_dir / generator.tail_shard_manifest_name(0, 0)
            self.assertFalse(manifest.exists())
            self.assertEqual(
                {path.name for path in lean_dir.iterdir()},
                {"target", expected_name},
            )

        with TemporaryDirectory() as directory:
            lean_dir = Path(directory)
            (lean_dir / unexpected_name).mkdir()
            with self.assertRaisesRegex(RuntimeError, "non-regular"):
                generator.tail_shard_differences(
                    rendered, 0, 0, lean_dir)

    def test_render_digest_is_identical_normally_and_with_optimization(
            self) -> None:
        tools_dir = Path(__file__).resolve().parent
        code = (
            "import generate_dummit_kernel_certificates as g; "
            f"row={SYNTHETIC_TAIL_ROW!r}; "
            "rendered,_=g.render_tail_shard_target(0,0,row); "
            "print(g.tail_shard_digest(rendered))"
        )
        normal = subprocess.check_output(
            [sys.executable, "-c", code], cwd=tools_dir, text=True)
        optimized = subprocess.check_output(
            [sys.executable, "-O", "-c", code],
            cwd=tools_dir, text=True)
        self.assertEqual(normal, optimized)
        self.assertEqual(
            normal.strip(),
            "7c1dfd2dcdcbae86c8f733543aea26804247dd1b220d343f7098fc0fcd9c4480",
        )


if __name__ == "__main__":
    unittest.main()
