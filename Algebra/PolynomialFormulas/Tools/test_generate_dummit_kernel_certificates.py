#!/usr/bin/env python3
"""Regression tests for Dummit certificate generator ownership checks."""

from pathlib import Path
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


if __name__ == "__main__":
    unittest.main()
