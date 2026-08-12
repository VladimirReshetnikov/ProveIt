#!/usr/bin/env python3
"""Generate bounded coefficient certificates for modular product rows 146--158.

The generated Lean file never asks the kernel to normalize a quotient-backed
polynomial equality.  It checks each explicit product support once, checks
coefficient coordinates in chunks of twelve, and reconstructs the full
132-coordinate row by finite division/modulus case analysis.
"""

from __future__ import annotations

from pathlib import Path
import argparse

N = 6
TARGET = 7


def weak_compositions(slots: int, total: int) -> list[tuple[int, ...]]:
    if slots == 0:
        return [()] if total == 0 else []
    result: list[tuple[int, ...]] = []
    for first in range(total + 1):
        for tail in weak_compositions(slots - 1, total - first):
            result.append((first,) + tail)
    return result


def rotate(exponent: tuple[int, ...], shift: int) -> tuple[int, ...]:
    return tuple(exponent[(index + shift) % N] for index in range(N))


def code(exponent: tuple[int, ...]) -> int:
    return sum(value * 8**index for index, value in enumerate(exponent))


def orbit(exponent: tuple[int, ...]) -> list[tuple[int, ...]]:
    seen: set[tuple[int, ...]] = set()
    result: list[tuple[int, ...]] = []
    for shift in range(N):
        value = rotate(exponent, shift)
        if value not in seen:
            seen.add(value)
            result.append(value)
    return result


def representatives(degree: int) -> list[tuple[int, ...]]:
    seen: set[tuple[int, ...]] = set()
    result: list[tuple[int, ...]] = []
    for exponent in weak_compositions(N, degree):
        candidate = min(orbit(exponent), key=code)
        if candidate not in seen:
            seen.add(candidate)
            result.append(candidate)
    return result


def elementary_exponents(degree: int) -> list[tuple[int, ...]]:
    return [
        exponent
        for exponent in weak_compositions(N, degree)
        if all(value <= 1 for value in exponent)
    ]


def rows() -> list[tuple[int, tuple[int, ...], int]]:
    result: list[tuple[int, tuple[int, ...], int]] = []
    for degree in range(1, N + 1):
        for source in representatives(TARGET - degree):
            result.append((degree, source, len(result)))
    return result


def product_monomials(source: tuple[int, ...], degree: int) -> list[tuple[int, ...]]:
    return [
        tuple(left + right for left, right in zip(orbit_source, elementary))
        for orbit_source in orbit(source)
        for elementary in elementary_exponents(degree)
    ]


def vec(exponent: tuple[int, ...]) -> str:
    return "![" + ",".join(str(value) for value in exponent) + "]"


def row_header(index: int) -> str:
    return f"row{index}"


def emit_row(lines: list[str], index: int, degree: int, source: tuple[int, ...]) -> None:
    name = row_header(index)
    monomials = product_monomials(source, degree)
    lines += [f"def {name}ProductMonomials : List Exponent := ["]
    for position, exponent in enumerate(monomials):
        suffix = "," if position + 1 < len(monomials) else ""
        lines.append(f"  {vec(exponent)}{suffix}")
    lines += ["]", ""]
    lines += [
        "set_option maxRecDepth 200000 in",
        "set_option maxHeartbeats 40000000 in",
        f"theorem {name}ProductMonomials_eq_chunked :",
        f"    productMonomials (degreeSevenProductSource ⟨{index}, by decide⟩).2",
        f"      (degreeSevenProductSource ⟨{index}, by decide⟩).1 =",
        f"      {name}ProductMonomials := by",
        "  decide",
        "",
    ]
    for chunk in range(11):
        start = chunk * 12
        lines += [
            "set_option maxRecDepth 200000 in",
            "set_option maxHeartbeats 40000000 in",
            f"theorem {name}_product_coefficients_chunk{chunk} :",
            "    ∀ j : Fin 12,",
            f"      degreeSevenProductRow ⟨{index}, by decide⟩ ⟨{start} + j.1, by omega⟩ =",
            f"        productCoefficient (degreeSevenProductSource ⟨{index}, by decide⟩).2",
            f"          (degreeSevenProductSource ⟨{index}, by decide⟩).1",
            f"          (degreeSevenRepresentative ⟨{start} + j.1, by omega⟩) := by",
            "  intro j",
            "  unfold productCoefficient",
            f"  rw [{name}ProductMonomials_eq_chunked]",
            "  revert j",
            "  decide",
            "",
        ]
    lines += [
        "set_option maxRecDepth 300000 in",
        "set_option maxHeartbeats 80000000 in",
        f"theorem {name}_product_coefficients_reconstructed :",
        "    ∀ j : Fin 132,",
        f"      degreeSevenProductRow ⟨{index}, by decide⟩ j =",
        f"        productCoefficient (degreeSevenProductSource ⟨{index}, by decide⟩).2",
        f"          (degreeSevenProductSource ⟨{index}, by decide⟩).1",
        "          (degreeSevenRepresentative j) := by",
        "  intro j",
        "  generalize hqdef : j.1 / 12 = q",
        "  generalize hrdef : j.1 % 12 = r",
        "  have hq : q < 11 := by",
        "    rw [← hqdef]",
        "    omega",
        "  have hr : r < 12 := by",
        "    rw [← hrdef]",
        "    exact Nat.mod_lt _ (by decide)",
        "  have hj : j = ⟨q * 12 + r, by omega⟩ := by",
        "    apply Fin.ext",
        "    simp only [← hqdef, ← hrdef]",
        "    exact (Nat.div_add_mod' j.1 12).symm",
        "  have hchunk :",
        f"      degreeSevenProductRow ⟨{index}, by decide⟩ ⟨q * 12 + r, by omega⟩ =",
        f"        productCoefficient (degreeSevenProductSource ⟨{index}, by decide⟩).2",
        f"          (degreeSevenProductSource ⟨{index}, by decide⟩).1",
        "          (degreeSevenRepresentative ⟨q * 12 + r, by omega⟩) := by",
        "    interval_cases q <;>",
        "      first",
    ]
    for chunk in range(11):
        marker = "      |" if chunk else "      |"
        lines.append(
            f"      | simpa using {name}_product_coefficients_chunk{chunk} ⟨r, hr⟩"
        )
    lines += [
        "  simpa [hj] using hchunk",
        "",
        f"theorem {name}_literalProduct_eq_encoded_direct :",
        f"    degreeSevenLiteralProduct ⟨{index}, by decide⟩ =",
        f"      degreeSevenEncodedProduct ⟨{index}, by decide⟩ := by",
        "  apply degreeSevenLiteralProduct_eq_encoded_of_productCoefficients",
        f"  exact {name}_product_coefficients_reconstructed",
        "",
    ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", type=int, default=146)
    parser.add_argument("--end", type=int, default=158)
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()
    if not (146 <= args.start <= args.end <= 158):
        raise SystemExit("the generated tail must stay within rows 146..158")
    output = args.output or Path(
        "Algebra/PolynomialFormulas/Lean/PolynomialFormulas/"
        f"LazardInvariantModularProductBridgeRows{args.start}To{args.end}"
        "ChunkedCertificate.lean"
    )
    lines = [
        "import PolynomialFormulas.LazardInvariantModularProductBridgeAdapter",
        "",
        "namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge",
        "",
        "open LazardInvariantModularCounterexample",
        "open LazardInvariantModularDualCertificate",
        "open LazardInvariantModularOrbitCoordinates",
        "",
        "set_option autoImplicit false",
        "",
    ]
    for degree, source, index in rows():
        if args.start <= index <= args.end:
            emit_row(lines, index, degree, source)
    lines += ["end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge", ""]
    output.write_text("\n".join(lines), encoding="utf-8")
    print(output)


if __name__ == "__main__":
    main()
