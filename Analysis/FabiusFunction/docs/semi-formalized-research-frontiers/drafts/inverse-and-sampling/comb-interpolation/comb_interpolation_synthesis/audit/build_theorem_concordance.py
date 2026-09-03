#!/usr/bin/env python3
"""Build the reviewed, source-pinned theorem concordance.

The first nine columns are an immutable projection of the four source
manuscripts at ``SOURCE_REVISION``.  The remaining columns record the
editorial disposition in the canonical volume.  Directly retained labels are
discovered rather than hard coded.  ``ALIASES`` is deliberately explicit: it
is the reviewable list of results that were deduplicated into a stronger
canonical statement, or whose source environment did not carry a label.

This script is safe to rerun after editorial changes.  In particular, when a
previously omitted result is restored with its prefixed source label, the
direct label automatically wins over the fallback alias.
"""

from __future__ import annotations

import argparse
import csv
import io
import re
import subprocess
from collections import Counter
from pathlib import Path

from extract_source_results import (
    ALL_FIELDS,
    EDITORIAL_FIELDS,
    SOURCE_FIELDS,
    inventory_revision,
    projection_sha256,
)


PACKAGE = Path(__file__).resolve().parents[1]
PIN = PACKAGE / "audit" / "SOURCE_REVISION"
OUTPUT = PACKAGE / "theorem_concordance.csv"
EXPECTED_SOURCE_ROWS = 232
EXPECTED_SOURCE_PROJECTION = (
    "a065b161c80786829033f1efd39bb5d1e4c521b9b9c4446959a73729a55718e0"
)

PREFIX = {
    "dyadic": "",
    "geometric": "g1:",
    "geometric_3": "g2:",
    "geometric_q_fabius": "gq:",
}

# Each value is ordered from the most exact/strongest preferred target to a
# still-valid fallback that exists before the final restoration pass.  The
# first label present in the canonical volume is selected.
ALIASES: dict[str, tuple[str, ...]] = {
    # Unlabelled additive-dyadic source environments.
    "dyadic:unlabelled-example-001": ("thm:dyadic-values",),
    "dyadic:unlabelled-observation-001": ("sec:ordinary-numerics",),
    "dyadic:unlabelled-problem-004": ("sec:conjectures-interp",),
    "dyadic:unlabelled-question-005": ("sec:conjectures-interp",),

    # The first geometric report's finite algebra is subsumed by the stronger
    # affine/q-Jackson spine.  The genuinely independent later sections retain
    # their g1 labels directly.
    "geometric:unlabelled-definition-001": ("gq:chap:q-newton",),
    "geometric:unlabelled-definition-002": ("gq:eq:real-normalization",),
    "geometric:unlabelled-proposition-001": ("gq:chap:scope",),
    "geometric:eq:vandermonde": ("gq:thm:geometric-vandermonde",),
    "geometric:eq:bary-denominator": ("gq:thm:geometric-barycentric",),
    "geometric:eq:lambda": ("gq:prop:richardson-weights",),
    "geometric:eq:arbitrary-residual": ("gq:thm:monomial-residual",),
    "geometric:eq:all-moments": ("gq:prop:richardson-weights",),
    "geometric:eq:sharp-majorant": (
        "g1:eq:sharp-majorant",
        "gq:thm:analytic-newton-convergence",
    ),
    "geometric:eq:divdiff-Jackson": ("gq:thm:Dq-divided-difference",),
    "geometric:eq:Newton-Jackson": ("gq:cor:q-taylor-interpolant",),
    "geometric:eq:newton-to-monomial": ("gq:thm:gaussian-pascal-basis",),
    "geometric:eq:infinite-Newton": ("gq:thm:analytic-newton-convergence",),
    "geometric:eq:operator-factorization": (
        "g1:eq:operator-factorization",
        "g1:eq:mode-polynomial",
    ),
    "geometric:eq:weight-recursion": (
        "g1:eq:weight-recursion",
        "gq:prop:richardson-weights",
    ),
    "geometric:eq:pure-power": (
        "g1:eq:pure-power",
        "g2:thm:mellin-symbol",
    ),
    "geometric:eq:log-power": ("g2:prop:log-powers",),
    "geometric:unlabelled-proposition-002": ("g1:eq:mode-polynomial",),
    "geometric:unlabelled-theorem-011": ("g1:eq:mode-polynomial",),
    "geometric:unlabelled-problem-001": ("g1:sec:modal",),
    "geometric:unlabelled-theorem-019": ("g1:eq:B-density",),
    "geometric:unlabelled-algorithm-001": ("g1:sec:algorithms",),
    "geometric:unlabelled-problem-002": ("g1:sec:frontiers",),
    "geometric:unlabelled-problem-003": ("g1:sec:frontiers",),
    "geometric:unlabelled-problem-004": ("g1:sec:frontiers",),
    "geometric:unlabelled-problem-005": ("g1:sec:frontiers",),

    # Repeated algebra in the third geometric report is represented by the
    # stronger q/Fabius spine.  Its Mellin, summability, probability, and
    # reciprocal-product extensions retain their g2 labels directly.
    "geometric_3:prop:nodal-polynomial": ("gq:eq:nodal-polynomial",),
    "geometric_3:thm:pascal-factorization": (
        "gq:thm:gaussian-pascal-basis",
    ),
    "geometric_3:thm:basis-change": ("gq:thm:gaussian-pascal-basis",),
    "geometric_3:cor:formal-newton-coefficients": (
        "gq:prop:taylor-newton-transform",
    ),
    "geometric_3:thm:barycentric": ("gq:thm:geometric-barycentric",),
    "geometric_3:unlabelled-algorithm-001": (
        "gq:thm:geometric-barycentric",
    ),
    "geometric_3:thm:filter-characteristic": (
        "g1:eq:operator-factorization",
        "g1:eq:mode-polynomial",
    ),
    "geometric_3:thm:row-norm": ("gq:thm:endpoint-lebesgue",),
    "geometric_3:thm:universal-residual": ("gq:thm:monomial-residual",),
    "geometric_3:cor:analytic-residual": ("gq:cor:analytic-residual",),
    "geometric_3:cor:disk-bound": (
        "g1:eq:sharp-majorant",
        "gq:thm:analytic-newton-convergence",
    ),
    "geometric_3:thm:jackson-divided": ("gq:thm:Dq-divided-difference",),
    "geometric_3:cor:finite-jackson-newton": (
        "gq:cor:q-taylor-interpolant",
    ),
    "geometric_3:thm:infinite-jackson-newton": (
        "gq:thm:analytic-newton-convergence",
    ),

    # Unlabelled environments in the strongest spine are located by the
    # nearest stable labelled theorem/section that owns them.
    "geometric_q_fabius:unlabelled-definition-001": (
        "gq:eq:real-normalization",
    ),
    "geometric_q_fabius:unlabelled-proposition-001": ("gq:chap:scope",),
    "geometric_q_fabius:unlabelled-example-001": (
        "gq:thm:gaussian-pascal-basis",
    ),
    "geometric_q_fabius:unlabelled-example-002": (
        "gq:thm:monomial-residual",
    ),
    "geometric_q_fabius:unlabelled-observation-001": ("gq:fig:fabius-gap",),
}

LEAN_PROOFS = {
    "thm:weight-valuation": (
        "FabiusFunction.PrimePowerBinomialValuation",
        "Fabius.twoPowChoose_padicValNat",
    ),
    "gq:thm:up-polynomial-synthesis": (
        "FabiusFunction.RvachevPolynomialSynthesis",
        "Fabius.normalized_sum_Ioo_"
        "rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp",
    ),
    "gq:cor:interpolation-up-factorization": (
        "FabiusFunction.LagrangeRvachevSynthesis",
        "Fabius.sum_Ioo_lagrangeRvachevAtomCoefficient_"
        "mul_shifted_rvachevUp",
    ),
}

# These declarations verify exact generic scalar ingredients of compound
# manuscript results without upgrading the whole source row to Lean-proved.
# In particular, the Gaussian closed forms and Matrix-level packaging in the
# paper are stronger than the declarations named here.
LEAN_SUPPORT: dict[str, tuple[str, tuple[str, ...], str]] = {
    "thm:weight-valuation": (
        "FabiusFunction.PrimePowerBinomialValuation",
        (
            "Fabius.primePowerSubOneChoose_padicValNat",
            "Fabius.primePowerSubTwoChoose_padicValNat",
            "Fabius.twoPowSubTwoChoose_padicValNat",
        ),
        "Lean also proves the full generic-prime unit row p^m - 1, the exact "
        "generic-prime companion valuation in row p^m - 2 for 0 < j < p^m, "
        "and its dyadic specialization.",
    ),
    "gq:thm:gaussian-Appell-decoder": (
        "FabiusFunction.LagrangeRvachevSynthesis",
        (
            "Fabius.normalized_sum_Ioo_lagrangeRvachevDecoder_"
            "mul_shifted_rvachevUp",
        ),
        "Lean proves the generic finite scalar decoder synthesis; the "
        "geometric Gaussian closed form, elementary-symmetric formula, and "
        "prefactor in this compound theorem remain manuscript-only.",
    ),
    "gq:cor:interpolation-up-factorization": (
        "FabiusFunction.LagrangeRvachevSynthesis",
        (
            "Fabius.lagrangeRvachevAtomCoefficient_"
            "eq_deconvolved_interpolate",
            "Fabius.sum_Ioo_lagrangeRvachevAtomCoefficient_"
            "mul_shifted_rvachevUp",
        ),
        "Lean proves both the generic scalar coefficient/deconvolution "
        "factorization and the full finite interpolation loop; the latter "
        "is the exact compiled crosswalk recorded in this row.",
    ),
    "gq:thm:gaussian-Appell-biorthogonality": (
        "FabiusFunction.LagrangeRvachevSynthesis",
        (
            "Fabius.normalized_sum_Ioo_lagrangeRvachevDecoder_eval_node",
            "Fabius.sum_lagrangeRvachevDecoder_eq_one",
        ),
        "Lean proves componentwise node biorthogonality and the unnormalized "
        "decoder row-sum law; no Matrix wrapper or row-stochastic encoder "
        "package is formalized.",
    ),
}

LEAN_DISPOSITION_NOTES = {
    "thm:weight-valuation": (
        "Exact Lean counterpart for the strict-interior dyadic formula. The "
        "same module proves the arbitrary-prime p^m identity including the "
        "positive right endpoint, the full p^m - 1 unit row "
        "Fabius.primePowerSubOneChoose_padicValNat, the generic companion "
        "identity Fabius.primePowerSubTwoChoose_padicValNat for "
        "0 < j < p^m, and its exact dyadic wrapper "
        "Fabius.twoPowSubTwoChoose_padicValNat."
    ),
}

PROVED_KINDS = {"theorem", "proposition", "lemma", "corollary", "identity"}
OPEN_KINDS = {"conjecture", "problem", "question"}


def strip_comments(text: str) -> str:
    """Remove TeX comments while retaining line positions."""

    output: list[str] = []
    for line in text.splitlines(keepends=True):
        cut = len(line)
        for index, character in enumerate(line):
            if character != "%":
                continue
            backslashes = 0
            cursor = index - 1
            while cursor >= 0 and line[cursor] == "\\":
                backslashes += 1
                cursor -= 1
            if backslashes % 2 == 0:
                cut = index
                break
        newline = "\n" if line.endswith("\n") else ""
        output.append(line[:cut].rstrip("\r\n") + newline)
    return "".join(output)


def canonical_tex_files() -> list[Path]:
    return [PACKAGE / "comb_interpolation_synthesis.tex", *sorted((PACKAGE / "chapters").glob("*.tex"))]


def canonical_labels() -> set[str]:
    labels: set[str] = set()
    for path in canonical_tex_files():
        text = strip_comments(path.read_text(encoding="utf-8"))
        labels.update(re.findall(r"\\label\{([^{}]+)\}", text))
    return labels


def choose_label(row: dict[str, str], labels: set[str]) -> tuple[str, str]:
    source_label = row["source_label"]
    if source_label:
        direct = PREFIX[row["source_package"]] + source_label
        if direct in labels:
            return direct, "Retained under its canonical prefixed label."

    choices = ALIASES.get(row["source_key"], ())
    for label in choices:
        if label in labels:
            if source_label:
                return (
                    label,
                    "Deduplicated into the cited stronger canonical result; "
                    "the source statement remains recoverable at SOURCE_REVISION.",
                )
            return (
                label,
                "The source environment had no label; this stable canonical "
                "label identifies the retained result or its owning section.",
            )
    candidates = ", ".join(choices) if choices else "no alias registered"
    raise ValueError(
        f"no canonical mapping for {row['source_key']} "
        f"(tried {candidates})"
    )


def status_for(row: dict[str, str], label: str) -> tuple[str, str, str]:
    kind = row["source_kind"]
    if label in LEAN_PROOFS:
        if kind not in PROVED_KINDS:
            raise ValueError(f"Lean proof attached to non-theorem row {row['source_key']}")
        module, declaration = LEAN_PROOFS[label]
        return "Lean-proved", module, declaration
    if kind in PROVED_KINDS:
        return "human-proved frontier result", "", ""
    if kind == "conjecture":
        return "conjecture", "", ""
    if kind in {"problem", "question"}:
        return "open problem", "", ""
    return "not applicable", "", ""


def build_rows(revision: str) -> tuple[str, list[dict[str, str]], Counter[str]]:
    commit, source_rows = inventory_revision(revision)
    if len(source_rows) != EXPECTED_SOURCE_ROWS:
        raise ValueError(
            f"source inventory drift: expected {EXPECTED_SOURCE_ROWS}, "
            f"found {len(source_rows)}"
        )
    digest = projection_sha256(source_rows)
    if digest != EXPECTED_SOURCE_PROJECTION:
        raise ValueError(
            "source projection drift: "
            f"expected {EXPECTED_SOURCE_PROJECTION}, found {digest}"
        )

    labels = canonical_labels()
    rows: list[dict[str, str]] = []
    modes: Counter[str] = Counter()
    for source in source_rows:
        label, note = choose_label(source, labels)
        if label in LEAN_SUPPORT:
            note = f"{note} {LEAN_SUPPORT[label][2]}"
        direct = bool(
            source["source_label"]
            and label == PREFIX[source["source_package"]] + source["source_label"]
        )
        modes["direct" if direct else "deduplicated-or-unlabelled"] += 1
        status, module, declaration = status_for(source, label)
        note = LEAN_DISPOSITION_NOTES.get(label, note)
        row = dict(source)
        row.update(
            {
                "canonical_label": label,
                "canonical_status": status,
                "lean_module": module,
                "lean_declaration": declaration,
                "disposition_notes": note,
            }
        )
        rows.append(row)
    return commit, rows, modes


def csv_bytes(rows: list[dict[str, str]]) -> bytes:
    stream = io.StringIO(newline="")
    writer = csv.DictWriter(stream, fieldnames=ALL_FIELDS, lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
    return stream.getvalue().encode("utf-8")


def repository_root() -> Path:
    completed = subprocess.run(
        ["git", "-C", str(PACKAGE), "rev-parse", "--show-toplevel"],
        check=True,
        stdout=subprocess.PIPE,
    )
    return Path(completed.stdout.decode("utf-8").strip())


def verify_lean_declarations(rows: list[dict[str, str]]) -> None:
    root = repository_root()
    completed = subprocess.run(
        ["git", "-C", str(root), "ls-files", "--", "*.lean"],
        check=True,
        stdout=subprocess.PIPE,
    )
    lean_files = [Path(line) for line in completed.stdout.decode("utf-8").splitlines()]
    entries = [
        (row["lean_module"], row["lean_declaration"])
        for row in rows
        if row["lean_module"]
    ]
    for module, declarations, _note in LEAN_SUPPORT.values():
        entries.extend((module, declaration) for declaration in declarations)

    checked: set[tuple[str, str]] = set()
    for module, declaration in entries:
        key = (module, declaration)
        if key in checked:
            continue
        checked.add(key)
        suffix = Path(*module.split(".")).with_suffix(".lean")
        candidates = [
            root / path
            for path in lean_files
            if path.as_posix().endswith(suffix.as_posix())
        ]
        if len(candidates) != 1:
            raise ValueError(
                f"expected one file for Lean module {module}, found {len(candidates)}"
            )
        text = candidates[0].read_text(encoding="utf-8")
        short = declaration.rsplit(".", 1)[-1]
        if not re.search(rf"\b(?:theorem|lemma)\s+{re.escape(short)}\b", text):
            raise ValueError(f"Lean declaration not found: {declaration} in {module}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument(
        "--check",
        action="store_true",
        help="compare the generated bytes with --output instead of writing",
    )
    args = parser.parse_args()

    revision = PIN.read_text(encoding="utf-8").strip()
    commit, rows, modes = build_rows(revision)
    verify_lean_declarations(rows)
    payload = csv_bytes(rows)

    if args.check:
        if not args.output.exists():
            print(f"FAILED: missing concordance: {args.output}")
            return 1
        actual = args.output.read_bytes()
        if actual != payload:
            print(f"FAILED: concordance is stale: {args.output}")
            return 1
        print(f"theorem concordance: PASS ({len(rows)} rows)")
    else:
        args.output.write_bytes(payload)
        print(f"wrote: {args.output}")

    print(f"source revision: {commit}")
    print(f"source projection sha256: {EXPECTED_SOURCE_PROJECTION}")
    for key, count in sorted(modes.items()):
        print(f"  {key}: {count}")
    for key, count in sorted(Counter(row["canonical_status"] for row in rows).items()):
        print(f"  {key}: {count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
