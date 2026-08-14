#!/usr/bin/env python3
"""Regression tests for focused Dummit certificate generator modes."""

from pathlib import Path
from collections.abc import Iterable
import hashlib
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

ROOT_MODULE_COUNT = 563
ROOT_IMPORT_COUNT = 1549
ROOT_UTF8_BYTES = 17670054
ROOT_CLOSURE_DIGEST = \
    "badba94c6bc2df9a06b8472355e6d116342fa4a3b006ef080e10ff2481944d73"
ROOT_MODULE_NAMES_DIGEST = \
    "cf6b89b886e7778506b2a65035c660e21f02e3319f466ca8869c17607e2bef84"


def term_name(table: int, position: int, suffix: str) -> str:
    return f"{generator.PREFIX}Table{table}Term{position}{suffix}"


def root_module_names_digest(modules: Iterable[str]) -> str:
    digest = hashlib.sha256()
    for module in sorted(modules):
        digest.update(module.encode("utf-8"))
        digest.update(b"\n")
    return digest.hexdigest()


def root_closure_summary(
        rendered: dict[str, str],
        imports: dict[str, tuple[str, ...]]) -> tuple[int, int, int, str, str]:
    return (
        len(rendered),
        sum(len(dependencies) for dependencies in imports.values()),
        sum(len(payload.encode("utf-8")) for payload in rendered.values()),
        generator.root_closure_digest(rendered),
        root_module_names_digest(rendered),
    )


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


class RootValidationTest(unittest.TestCase):
    module = f"{generator.PREFIX}RootFixture"

    def payload(self, declaration: str =
                "theorem root_fixture_certificate : True := by trivial"
                ) -> str:
        return generator.module_text([], [declaration])

    def test_heartbeat_parser_accepts_whitespace_and_underscores(self) -> None:
        original = "set_option maxHeartbeats 20000000"
        for directive in (
                "set_option\tmaxHeartbeats\t20_000_000",
                "  set_option maxHeartbeats 1 in  "):
            with self.subTest(directive=directive):
                payload = self.payload().replace(original, directive)
                self.assertEqual(
                    generator.root_module_declarations(self.module, payload),
                    (("theorem", "root_fixture_certificate"),),
                )

    def test_heartbeat_parser_rejects_every_unbounded_or_unparsed_form(
            self) -> None:
        original = "set_option maxHeartbeats 20000000"
        for directive in (
                "set_option maxHeartbeats 0",
                "set_option maxHeartbeats 20_000_001",
                "set_option maxHeartbeats 20__000_000",
                "set_option maxHeartbeats heartbeatBudget",
                "set_option maxHeartbeats (20000000)",
                "set_option maxHeartbeats 20000000.0",
                "example : True := by set_option maxHeartbeats 1 in trivial",
                "def quoted := `(set_option maxHeartbeats 1 in true)"):
            with self.subTest(directive=directive):
                payload = self.payload().replace(original, directive)
                with self.assertRaisesRegex(
                        RuntimeError, "finite heartbeat"):
                    generator.root_module_declarations(self.module, payload)

    def test_heartbeat_directive_outside_code_is_rejected(self) -> None:
        original = "set_option maxHeartbeats 20000000"
        for replacement in (
                f"-- {original}",
                f"{original} -- maxHeartbeats",
                f"/- {original} -/",
                f'def heartbeatText : String := "{original}"'):
            with self.subTest(replacement=replacement):
                payload = self.payload().replace(original, replacement)
                with self.assertRaisesRegex(
                        RuntimeError, "unsupported comments or strings"):
                    generator.root_module_declarations(self.module, payload)

    def test_direct_trust_tokens_are_rejected(self) -> None:
        for token in (
                "sorry", "admit", "axiom", "constant", "unsafe",
                "partial", "native_decide", "sorryAx", "ofReduceBool",
                "Lean.ofReduceBool", "implemented_by"):
            with self.subTest(token=token):
                with self.assertRaisesRegex(
                        RuntimeError, "untrusted root proof"):
                    generator.root_module_declarations(
                        self.module, self.payload() + f"\n{token}\n")

    def test_declaration_kind_and_camel_case_support_references_are_pinned(
            self) -> None:
        theorem = "root_fixture_certificate"
        with patch.object(
                generator, "expected_root_key_declarations",
                return_value={self.module: (("theorem", theorem),)}):
            changed_kind = self.payload().replace(
                f"theorem {theorem}", f"def {theorem}", 1)
            with self.assertRaisesRegex(
                    RuntimeError, "declarations changed"):
                generator.validate_root_rendered_text(
                    {self.module: changed_kind})

            support = generator.ROOT_RAW_MUL_APPEND_LEFT_CERTIFICATE
            undeclared = self.payload(
                f"theorem {theorem} : True := by exact {support}")
            with self.assertRaisesRegex(RuntimeError, support):
                generator.validate_root_rendered_text(
                    {self.module: undeclared})

            for malformed in (
                    "thetaPolynomial_bad_certificate",
                    "thetaPolynomial_0_certificat"):
                with self.subTest(malformed=malformed):
                    undeclared = self.payload(
                        f"theorem {theorem} : True := by exact {malformed}")
                    with self.assertRaisesRegex(RuntimeError, malformed):
                        generator.validate_root_rendered_text(
                            {self.module: undeclared})

    def test_duplicate_imports_are_rejected(self) -> None:
        aggregate = f"{generator.PREFIX}s"
        rendered = {
            self.module: self.payload(),
            aggregate: generator.module_text([], []),
        }
        imports = {
            self.module: ("ComputableDummitCoefficientsCore",),
            aggregate: (
                self.module,
                self.module,
                *(generator.root_table_final_module(index)
                  for index in range(4)),
            ),
        }
        with patch.object(
                generator, "expected_root_modules",
                return_value=tuple(rendered)):
            with self.assertRaisesRegex(
                    RuntimeError, "duplicate generated root imports"):
                generator.validate_root_closure(rendered, imports)


class RootClosureTest(unittest.TestCase):
    rendered: dict[str, str] | None = None
    imports: dict[str, tuple[str, ...]] | None = None

    @classmethod
    def closure(cls) -> tuple[dict[str, str],
                              dict[str, tuple[str, ...]]]:
        if cls.rendered is None or cls.imports is None:
            cls.rendered, cls.imports = generator.render_root_closure()
        return cls.rendered, cls.imports

    def test_exact_closure_tuple_and_module_names(self) -> None:
        rendered, imports = self.closure()
        expected_summary = (
            ROOT_MODULE_COUNT,
            ROOT_IMPORT_COUNT,
            ROOT_UTF8_BYTES,
            ROOT_CLOSURE_DIGEST,
            ROOT_MODULE_NAMES_DIGEST,
        )
        self.assertEqual(root_closure_summary(rendered, imports),
                         expected_summary)
        self.assertEqual(tuple(rendered), generator.expected_root_modules())
        self.assertEqual(len(set(rendered)), ROOT_MODULE_COUNT)

    def test_render_is_identical_in_normal_and_optimized_python(self) -> None:
        rendered, imports = self.closure()
        expected = "|".join(map(str, root_closure_summary(
            rendered, imports)))
        tools_dir = Path(__file__).resolve().parent
        code = (
            "import hashlib; "
            "import generate_dummit_kernel_certificates as g; "
            "r,i=g.render_root_closure(); "
            "h=hashlib.sha256(); "
            "[(h.update(n.encode()),h.update(b'\\n')) for n in sorted(r)]; "
            "print(len(r),sum(map(len,i.values())),"
            "sum(len(p.encode()) for p in r.values()),"
            "g.root_closure_digest(r),h.hexdigest(),sep='|')"
        )
        opposite_mode = [] if sys.flags.optimize else ["-O"]
        environment = os.environ.copy()
        environment.pop("PYTHONOPTIMIZE", None)
        actual = subprocess.check_output(
            [sys.executable, *opposite_mode, "-c", code],
            cwd=tools_dir, env=environment, text=True)
        self.assertEqual(actual.strip(), expected)

    def test_trust_envelope_and_key_declarations_are_pinned(self) -> None:
        rendered, _ = self.closure()
        expected = generator.expected_root_key_declarations()
        self.assertEqual(len(expected), 55)
        for module, declarations in expected.items():
            self.assertEqual(
                generator.root_module_declarations(
                    module, rendered[module]),
                declarations,
            )
        support = generator.ROOT_NORMALIZE_SUPPORT_MODULE
        self.assertEqual(
            expected[support],
            tuple(("theorem", name) for name in (
                generator.ROOT_RAW_MUL_APPEND_LEFT_CERTIFICATE,
                generator.ROOT_RAW_MUL_SINGLETON_APPEND_RIGHT_CERTIFICATE,
                generator.ROOT_FLATTEN_BUCKETS_APPEND_CERTIFICATE,
                generator.ROOT_FLATTEN_BUCKETS_SINGLETON_CERTIFICATE,
            )),
        )
        aggregate = f"{generator.PREFIX}s"
        self.assertEqual(expected[aggregate], ())
        for index, word in enumerate(("zero", "one", "two", "three")):
            final = f"{generator.PREFIX}Root{index}Final"
            self.assertEqual(
                expected[final],
                (
                    ("def", f"rootCoefficient{index}Candidate"),
                    ("theorem",
                     f"root_coefficient_{word}_final_certificate"),
                    ("theorem",
                     f"sparseRootCoefficient_{word}_certificate"),
                ),
            )

        payload = rendered[support]
        for heartbeat in ("0", "20000001"):
            changed = payload.replace(
                "set_option maxHeartbeats 20000000",
                f"set_option maxHeartbeats {heartbeat}",
                1,
            )
            with self.assertRaisesRegex(RuntimeError, "finite heartbeat"):
                generator.root_module_declarations(support, changed)
        with self.assertRaisesRegex(RuntimeError, "untrusted root proof"):
            generator.root_module_declarations(
                support, payload + "\naxiom untrustedRootFixture : True\n")
        rendered_copy = dict(rendered)
        rendered_copy[support] = payload.replace(
            generator.ROOT_RAW_MUL_APPEND_LEFT_CERTIFICATE,
            "root_missing_declaration_certificate",
            1,
        )
        with self.assertRaisesRegex(RuntimeError, "declarations changed"):
            generator.validate_root_rendered_text(rendered_copy)


class RootFilesystemTest(unittest.TestCase):
    def fixture(self) -> tuple[dict[str, str],
                               dict[str, tuple[str, ...]]]:
        prefix = f"{generator.PREFIX}RootFixture"
        return (
            {
                f"{prefix}Data": "fixture-data\n",
                f"{prefix}Certificate": "fixture-certificate\n",
            },
            {},
        )

    def patched_root(self, rendered: dict[str, str],
                     imports: dict[str, tuple[str, ...]]) -> tuple[object, ...]:
        return (
            patch.object(
                generator, "render_root_closure",
                return_value=(rendered, imports)),
            patch.object(
                generator, "expected_root_modules",
                return_value=tuple(rendered)),
        )

    def write_inputs(self, directory: Path) -> None:
        for path in generator.required_root_input_paths(directory):
            path.write_text("input\n")

    def materialize(self, directory: Path,
                    rendered: dict[str, str]) -> None:
        for module, payload in rendered.items():
            (directory / f"{module}.lean").write_text(payload)

    def test_missing_stale_and_unexpected_fail_closed(self) -> None:
        rendered, imports = self.fixture()
        patches = self.patched_root(rendered, imports)
        with TemporaryDirectory() as directory:
            lean_dir = Path(directory)
            self.write_inputs(lean_dir)
            with patches[0], patches[1]:
                with self.assertRaisesRegex(RuntimeError, r"missing \(2\)"):
                    generator.check_root_closure(lean_dir)

                self.materialize(lean_dir, rendered)
                stale = next(iter(rendered))
                (lean_dir / f"{stale}.lean").write_text("stale\n")
                with self.assertRaisesRegex(
                        RuntimeError, r"stale-content \(1\)"):
                    generator.check_root_closure(lean_dir)
                (lean_dir / f"{stale}.lean").write_text(rendered[stale])

                unexpected = (
                    f"{generator.PREFIX}RootUnexpected.lean")
                (lean_dir / unexpected).write_text("unexpected\n")
                with self.assertRaisesRegex(
                        RuntimeError, r"unexpected \(1\)"):
                    generator.write_root_closure(lean_dir)

        patches = self.patched_root(rendered, imports)
        with TemporaryDirectory() as directory:
            lean_dir = Path(directory)
            self.write_inputs(lean_dir)
            self.materialize(lean_dir, rendered)
            unexpected = f"{generator.PREFIX}sLegacy.lean"
            (lean_dir / unexpected).write_text("not-owned\n")
            with patches[0], patches[1]:
                self.assertEqual(
                    generator.check_root_closure(lean_dir),
                    generator.root_closure_digest(rendered),
                )

    def test_write_changes_only_stale_or_missing_files(self) -> None:
        rendered, imports = self.fixture()
        patches = self.patched_root(rendered, imports)
        with TemporaryDirectory() as directory:
            lean_dir = Path(directory)
            self.write_inputs(lean_dir)
            self.materialize(lean_dir, rendered)
            fixed_time = 1_700_000_000_000_000_000
            filenames = [f"{module}.lean" for module in rendered]
            for filename in filenames:
                os.utime(lean_dir / filename, ns=(fixed_time, fixed_time))
            with patches[0], patches[1]:
                digest = generator.write_root_closure(lean_dir)
                self.assertEqual(
                    digest, generator.root_closure_digest(rendered))
                self.assertTrue(all(
                    (lean_dir / filename).stat().st_mtime_ns == fixed_time
                    for filename in filenames))

                changed, unchanged = filenames
                (lean_dir / changed).write_text("changed\n")
                os.utime(lean_dir / changed, ns=(fixed_time, fixed_time))
                generator.write_root_closure(lean_dir)
                self.assertNotEqual(
                    (lean_dir / changed).stat().st_mtime_ns, fixed_time)
                self.assertEqual(
                    (lean_dir / unchanged).stat().st_mtime_ns, fixed_time)
                for module, payload in rendered.items():
                    self.assertEqual(
                        (lean_dir / f"{module}.lean").read_text(), payload)

                (lean_dir / unchanged).unlink()
                generator.write_root_closure(lean_dir)
                self.assertEqual(
                    (lean_dir / unchanged).read_text(),
                    rendered[unchanged.removesuffix(".lean")],
                )

    def test_symlink_and_nonregular_paths_are_refused_before_writes(
            self) -> None:
        rendered, imports = self.fixture()
        patches = self.patched_root(rendered, imports)
        expected = f"{next(iter(rendered))}.lean"
        with TemporaryDirectory() as directory:
            lean_dir = Path(directory)
            self.write_inputs(lean_dir)
            target = lean_dir / "target"
            target.write_text("target\n")
            (lean_dir / expected).symlink_to(target)
            with patches[0], patches[1]:
                with self.assertRaisesRegex(RuntimeError, "non-regular"):
                    generator.write_root_closure(lean_dir)
            self.assertEqual(target.read_text(), "target\n")
            self.assertEqual(
                {path.name for path in lean_dir.iterdir()},
                {
                    *(path.name for path in
                      generator.required_root_input_paths(lean_dir)),
                    "target",
                    expected,
                },
            )

        patches = self.patched_root(rendered, imports)
        with TemporaryDirectory() as directory:
            lean_dir = Path(directory)
            self.write_inputs(lean_dir)
            (lean_dir / expected).mkdir()
            with patches[0], patches[1]:
                with self.assertRaisesRegex(RuntimeError, "non-regular"):
                    generator.write_root_closure(lean_dir)

        patches = self.patched_root(rendered, imports)
        with TemporaryDirectory() as directory:
            lean_dir = Path(directory)
            self.write_inputs(lean_dir)
            unexpected = f"{generator.PREFIX}RootUnexpected.lean"
            (lean_dir / unexpected).mkdir()
            with patches[0], patches[1]:
                with self.assertRaisesRegex(RuntimeError, "non-regular"):
                    generator.write_root_closure(lean_dir)

    def test_all_external_inputs_must_be_regular_nonsymlink_files(
            self) -> None:
        rendered, imports = self.fixture()
        input_names = tuple(
            path.name for path in generator.required_root_input_paths(
                Path("/root-input-fixture")))
        self.assertEqual(
            input_names,
            (
                "ComputableDummitCoefficientsCore.lean",
                *(f"{generator.root_table_final_module(index)}.lean"
                  for index in range(4)),
            ),
        )
        for operation in (
                generator.check_root_closure,
                generator.write_root_closure):
            for missing_name in input_names:
                with self.subTest(operation=operation.__name__,
                                  missing=missing_name):
                    patches = self.patched_root(rendered, imports)
                    with TemporaryDirectory() as directory:
                        lean_dir = Path(directory)
                        self.write_inputs(lean_dir)
                        (lean_dir / missing_name).unlink()
                        with patches[0], patches[1]:
                            with self.assertRaisesRegex(
                                    RuntimeError, missing_name):
                                operation(lean_dir)
                        self.assertFalse(any(
                            (lean_dir / f"{module}.lean").exists()
                            for module in rendered))

        for operation in (
                generator.check_root_closure,
                generator.write_root_closure):
            for input_name in input_names:
                for path_kind in ("symlink", "directory"):
                    with self.subTest(operation=operation.__name__,
                                      input=input_name,
                                      path_kind=path_kind):
                        patches = self.patched_root(rendered, imports)
                        with TemporaryDirectory() as directory:
                            lean_dir = Path(directory)
                            self.write_inputs(lean_dir)
                            input_path = lean_dir / input_name
                            input_path.unlink()
                            if path_kind == "symlink":
                                target = lean_dir / "external-input-target"
                                target.write_text("target\n")
                                input_path.symlink_to(target)
                            else:
                                input_path.mkdir()
                            with patches[0], patches[1]:
                                with self.assertRaisesRegex(
                                        RuntimeError, input_name):
                                    operation(lean_dir)
                            self.assertFalse(any(
                                (lean_dir / f"{module}.lean").exists()
                                for module in rendered))


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
