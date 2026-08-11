#!/usr/bin/env python3
"""Emit the memory-bounded sparse certificates for Lazard's P2 numerator.

The polynomial variables are x0,x1,x2,x3,omega.  We eliminate x4 by the
depressed relation and split every substantial check by omega coefficient.
Lean independently checks the generated integer-polynomial identities.  The
Rocq backend additionally folds omega exponents modulo five and emits bounded
data/certificate leaves for the certified cyclic sparse evaluator.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from pathlib import Path

import generate_lazard_root_projection_i_sparse as sparse


LEAN_DIR = Path("Algebra/PolynomialFormulas/Lean/PolynomialFormulas")
COQ_DIR = Path("Algebra/PolynomialFormulas/Coq")
PREFIX = "LazardQuinticRootFourierNumeratorP2Sparse"
NAMESPACE = (
    "LeanProofs.PolynomialFormulas.LazardQuintic."
    "RootFourierNumeratorP2Sparse"
)


def omega_free_coefficients(poly: sparse.Polynomial) -> dict[int, sparse.Polynomial]:
    result: dict[int, dict[sparse.Exponent, int]] = {}
    for exponent, coefficient in poly.items():
        degree = exponent[4]
        root_exponent = exponent[:4] + (0,)
        result.setdefault(degree, {})[root_exponent] = coefficient
    return result


def with_omega_degree(poly: sparse.Polynomial, degree: int) -> sparse.Polynomial:
    return {
        exponent[:4] + (degree,): coefficient
        for exponent, coefficient in poly.items()
    }


def root_difference_cycle(indices: list[tuple[int, int]]) -> sparse.Polynomial:
    return sparse.product(*(
        [1] + [sparse.add(sparse.ROOTS[i], sparse.neg(sparse.ROOTS[j]))
               for i, j in indices]
    ))


T_PRIME = root_difference_cycle([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)])
U_PRIME = root_difference_cycle([(0, 2), (1, 3), (2, 4), (3, 0), (4, 1)])
ROOT_E = sparse.neg(sparse.add(
    sparse.power(T_PRIME, 2), sparse.power(U_PRIME, 2)))

P21 = sparse.scale(5, sparse.add(
    sparse.scale(3, sparse.I4),
    sparse.scale(2, sparse.power(sparse.P, 2)),
    sparse.scale(-16, sparse.R),
))
# This is Reshetnikov's corrected P22: the two printed terms `8 p^3` and
# `70 q^3 q` are respectively `8 p^3 q` and `70 q^3`.
P22 = sparse.scale(25, sparse.add(
    sparse.product(-10, sparse.Q, sparse.I6),
    sparse.mul(sparse.add(
        sparse.scale(8, sparse.power(sparse.P, 2)),
        sparse.scale(-50, sparse.R)), sparse.I5),
    sparse.mul(sparse.add(
        sparse.product(-2, sparse.P, sparse.Q),
        sparse.scale(-25, sparse.S)), sparse.I4),
    sparse.product(8, sparse.power(sparse.P, 3), sparse.Q),
    sparse.scale(70, sparse.power(sparse.Q, 3)),
    sparse.product(-20, sparse.power(sparse.P, 2), sparse.S),
    sparse.product(-26, sparse.P, sparse.Q, sparse.R),
    sparse.product(50, sparse.R, sparse.S),
))
P23 = sparse.scale(25, sparse.add(
    sparse.product(-4, sparse.P, sparse.I7),
    sparse.product(-1, sparse.Q, sparse.I6),
    sparse.product(4, sparse.R, sparse.I5),
    sparse.mul(sparse.add(
        sparse.product(-3, sparse.P, sparse.Q),
        sparse.scale(15, sparse.S)), sparse.I4),
    sparse.product(26, sparse.power(sparse.P, 2), sparse.S),
    sparse.product(-26, sparse.P, sparse.Q, sparse.R),
    sparse.scale(7, sparse.power(sparse.Q, 3)),
    sparse.product(-40, sparse.R, sparse.S),
))
P24 = sparse.scale(25, sparse.add(
    sparse.product(3, sparse.P, sparse.I7),
    sparse.product(-18, sparse.Q, sparse.I6),
    sparse.product(22, sparse.R, sparse.I5),
    sparse.mul(sparse.add(
        sparse.product(-14, sparse.P, sparse.Q),
        sparse.scale(20, sparse.S)), sparse.I4),
    sparse.product(18, sparse.power(sparse.P, 2), sparse.S),
    sparse.product(-33, sparse.P, sparse.Q, sparse.R),
    sparse.scale(21, sparse.power(sparse.Q, 3)),
    sparse.product(30, sparse.R, sparse.S),
))

OMEGA = sparse.OMEGA
ROOT_T = sparse.add(
    sparse.mul(sparse.add(OMEGA, sparse.neg(sparse.power(OMEGA, 4))), T_PRIME),
    sparse.mul(sparse.add(sparse.power(OMEGA, 2),
                          sparse.neg(sparse.power(OMEGA, 3))), U_PRIME),
)
ROOT_FORMULA_U = sparse.add(
    sparse.neg(sparse.mul(sparse.add(
        sparse.power(OMEGA, 2), sparse.neg(sparse.power(OMEGA, 3))), T_PRIME)),
    sparse.mul(sparse.add(OMEGA, sparse.neg(sparse.power(OMEGA, 4))), U_PRIME),
)

FOURIER_QUARTIC = sparse.mul(
    sparse.power(sparse.fourier(1), 3), sparse.fourier(2))
FOURIER_QUARTIC_COEFF = omega_free_coefficients(FOURIER_QUARTIC)

EPSILON_T = sparse.mul(sparse.EPSILON, ROOT_T)
EPSILON_FORMULA_U = sparse.mul(sparse.EPSILON, ROOT_FORMULA_U)
EPSILON_T_COEFF = omega_free_coefficients(EPSILON_T)
EPSILON_FORMULA_U_COEFF = omega_free_coefficients(EPSILON_FORMULA_U)

EPSILON_E_CORE = sparse.mul(sparse.EPSILON_PRODUCT, ROOT_E)
EPSILON_COEFF = omega_free_coefficients(sparse.EPSILON_COEFFICIENT)

NUMERATOR = sparse.add(
    sparse.product(5, sparse.EPSILON, ROOT_E, P21),
    sparse.product(5, ROOT_E, P22),
    sparse.product(2, sparse.EPSILON, P23, ROOT_T),
    sparse.product(2, sparse.EPSILON, P24, ROOT_FORMULA_U),
    sparse.product(-20, sparse.EPSILON, ROOT_E, FOURIER_QUARTIC),
)
QUOTIENT, REMAINDER = sparse.divide_by_phi5(NUMERATOR)
assert not REMAINDER
NUMERATOR_COEFF = omega_free_coefficients(NUMERATOR)


def cyclic_coefficients(poly: sparse.Polynomial) -> list[sparse.Polynomial]:
    """Fold omega exponents modulo five, as the Rocq cyclic algebra does."""
    result: list[dict[sparse.Exponent, int]] = [dict() for _ in range(5)]
    for exponent, coefficient in poly.items():
        root_exponent = exponent[:4] + (0,)
        row = result[exponent[4] % 5]
        row[root_exponent] = row.get(root_exponent, 0) + coefficient
        if row[root_exponent] == 0:
            del row[root_exponent]
    return result


CYCLIC_COEFFICIENTS = cyclic_coefficients(NUMERATOR)
assert all(row == CYCLIC_COEFFICIENTS[0]
           for row in CYCLIC_COEFFICIENTS[1:])
COQ_COMMON = CYCLIC_COEFFICIENTS[0]
COQ_DATA_PART_SIZE = 150


def polynomial_chunks(poly: sparse.Polynomial, size: int = 30) -> list[sparse.Polynomial]:
    items = sorted(poly.items())
    return [dict(items[index:index + size]) for index in range(0, len(items), size)]


COQ_DATA_PARTS = polynomial_chunks(COQ_COMMON, COQ_DATA_PART_SIZE)


# Keep every generated patch well below the tool transport limit as well as
# every Lean declaration small enough to elaborate predictably.
NORMAL_PART_SIZE = 400


def normal_parts(poly: sparse.Polynomial) -> list[sparse.Polynomial]:
    return polynomial_chunks(poly, NORMAL_PART_SIZE)


P22_CHUNKS = polynomial_chunks(P22, 30)
# The largest 50-row products below contain at most 12,800 raw pairs.  The
# independently measured 14,060-row direct product remains below 9 GiB RSS.
P23_CHUNKS = polynomial_chunks(P23, 50)
P24_CHUNKS = polynomial_chunks(P24, 50)


def direct_product_specs() -> dict[str, tuple[str, str, sparse.Polynomial]]:
    specs: dict[str, tuple[str, str, sparse.Polynomial]] = {
        "EpsilonEP21": (
            "epsilonECoreNormal", "p21Normal",
            sparse.mul(EPSILON_E_CORE, P21)),
    }
    for degree in range(17):
        specs[f"EpsilonEFourierW{degree}"] = (
            "epsilonECoreNormal", f"fourierQuarticNormalW{degree}",
            sparse.mul(EPSILON_E_CORE, FOURIER_QUARTIC_COEFF.get(degree, {})))
    return specs


def chunked_product_specs() -> dict[
        str, tuple[str, sparse.Polynomial, str, list[sparse.Polynomial], sparse.Polynomial]]:
    specs = {
        "RootEP22": (
            "rootENormal", ROOT_E, "p22Chunk", P22_CHUNKS,
            sparse.mul(ROOT_E, P22)),
    }
    for degree in [2, 3, 4, 6, 7, 8]:
        specs[f"EpsilonTP23W{degree}"] = (
            f"epsilonTNormalW{degree}", EPSILON_T_COEFF[degree],
            "p23Chunk", P23_CHUNKS,
            sparse.mul(EPSILON_T_COEFF[degree], P23))
        specs[f"EpsilonFormulaUP24W{degree}"] = (
            f"epsilonFormulaUNormalW{degree}",
            EPSILON_FORMULA_U_COEFF[degree],
            "p24Chunk", P24_CHUNKS,
            sparse.mul(EPSILON_FORMULA_U_COEFF[degree], P24))
    return specs


DIRECT_PRODUCTS = direct_product_specs()
CHUNKED_PRODUCTS = chunked_product_specs()

DIRECT_FACTOR_CHUNK_SIZE = 8


def direct_factor_poly(key: str) -> sparse.Polynomial:
    if key == "EpsilonEP21":
        return P21
    prefix = "EpsilonEFourierW"
    assert key.startswith(prefix)
    return FOURIER_QUARTIC_COEFF[int(key[len(prefix):])]


def direct_factor_chunks(key: str) -> list[sparse.Polynomial]:
    return polynomial_chunks(direct_factor_poly(key), DIRECT_FACTOR_CHUNK_SIZE)


def direct_chunk_normal_poly(key: str, chunk: int) -> sparse.Polynomial:
    return sparse.mul(EPSILON_E_CORE, direct_factor_chunks(key)[chunk])


def module(imports: list[str], declarations: list[str]) -> str:
    import_text = "\n".join(f"import PolynomialFormulas.{name}" for name in imports)
    return "\n\n".join([
        import_text,
        f"namespace {NAMESPACE}",
        "open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients",
        "open LeanProofs.PolynomialFormulas.LazardQuintic.RootInvariantSparse",
        "open LeanProofs.PolynomialFormulas.LazardQuintic.RootInvariantSparse.ReductionE",
        "open LeanProofs.PolynomialFormulas.LazardQuintic.RootProjectionISparse",
        "set_option maxRecDepth 300000",
        *declarations,
        f"end {NAMESPACE}",
    ]) + "\n"


def emit_file(filename: str, imports: list[str], declarations: list[str]) -> str:
    return sparse.patch_for_file(
        LEAN_DIR / filename, module(imports, declarations))


def fourier_source_declaration(degree: int) -> str:
    p1_degrees = [0, 1, 2, 3, 4]
    p2_degrees = [0, 2, 4, 1, 3]
    terms = []
    for i, left_degree in enumerate(p1_degrees):
        for j, right_degree in enumerate(p1_degrees):
            for k, third_degree in enumerate(p1_degrees):
                for ell, fourth_degree in enumerate(p2_degrees):
                    if (left_degree + right_degree + third_degree +
                            fourth_degree == degree):
                        terms.append(
                            f"SP.term 1 [rootVariables {i}, rootVariables {j}, "
                            f"rootVariables {k}, rootVariables {ell}]")
    rows = ",\n      ".join(terms)
    return (
        f"def fourierQuarticSourceW{degree} : SparsePolynomial :=\n"
        f"  SparsePolynomial.sum\n    [{rows}]")


def epsilon_t_source_declarations() -> list[str]:
    # Coefficients of (w + w^4 - w^2 - w^3) * rootT/rootFormulaU.
    t_expr = {
        2: "tRaw",
        3: "SparsePolynomial.sum [uRaw, tRaw.neg]",
        4: "SparsePolynomial.sum [tRaw.neg, SP.smul (-2) uRaw]",
        5: "SparsePolynomial.const 0",
        6: "SparsePolynomial.sum [tRaw, SP.smul 2 uRaw]",
        7: "SparsePolynomial.sum [tRaw, uRaw.neg]",
        8: "tRaw.neg",
    }
    u_expr = {
        2: "uRaw",
        3: "SparsePolynomial.sum [tRaw.neg, uRaw.neg]",
        4: "SparsePolynomial.sum [SP.smul 2 tRaw, uRaw.neg]",
        5: "SparsePolynomial.const 0",
        6: "SparsePolynomial.sum [SP.smul (-2) tRaw, uRaw]",
        7: "SparsePolynomial.sum [tRaw, uRaw]",
        8: "uRaw.neg",
    }
    result = []
    for degree in range(2, 9):
        result.append(
            f"def epsilonTSourceW{degree} : SparsePolynomial :=\n"
            f"  epsilonProductNormal.mul ({t_expr[degree]})")
        result.append(
            f"def epsilonFormulaUSourceW{degree} : SparsePolynomial :=\n"
            f"  epsilonProductNormal.mul ({u_expr[degree]})")
    return result


def emit_base() -> str:
    declarations = [
        "/-- Root-specialized `E`, represented by the already certified "
        "cyclic products. -/\n"
        "def rootESource : SparsePolynomial :=\n"
        "  (tRaw.pow 2).add (uRaw.pow 2) |>.neg",
        "def p21Source : SparsePolynomial :=\n"
        "  SP.smul 5 <| SparsePolynomial.sum\n"
        "    [SP.smul 3 i4, SP.smul 2 (p.pow 2), SP.smul (-16) r]",
        "def p22Source : SparsePolynomial :=\n"
        "  SP.smul 25 <| SparsePolynomial.sum\n"
        "    [SP.term (-10) [q, i6],\n"
        "     SP.term 1 [SparsePolynomial.sum [SP.smul 8 (p.pow 2),\n"
        "       SP.smul (-50) r], i5],\n"
        "     SP.term 1 [SparsePolynomial.sum [SP.term (-2) [p, q],\n"
        "       SP.smul (-25) s], i4],\n"
        "     SP.term 8 [p.pow 3, q], SP.smul 70 (q.pow 3),\n"
        "     SP.term (-20) [p.pow 2, s], SP.term (-26) [p, q, r],\n"
        "     SP.term 50 [r, s]]",
        "def p23Source : SparsePolynomial :=\n"
        "  SP.smul 25 <| SparsePolynomial.sum\n"
        "    [SP.term (-4) [p, i7], SP.term (-1) [q, i6],\n"
        "     SP.term 4 [r, i5],\n"
        "     SP.term 1 [SparsePolynomial.sum [SP.term (-3) [p, q],\n"
        "       SP.smul 15 s], i4],\n"
        "     SP.term 26 [p.pow 2, s], SP.term (-26) [p, q, r],\n"
        "     SP.smul 7 (q.pow 3), SP.term (-40) [r, s]]",
        "def p24Source : SparsePolynomial :=\n"
        "  SP.smul 25 <| SparsePolynomial.sum\n"
        "    [SP.term 3 [p, i7], SP.term (-18) [q, i6],\n"
        "     SP.term 22 [r, i5],\n"
        "     SP.term 1 [SparsePolynomial.sum [SP.term (-14) [p, q],\n"
        "       SP.smul 20 s], i4],\n"
        "     SP.term 18 [p.pow 2, s], SP.term (-33) [p, q, r],\n"
        "     SP.smul 21 (q.pow 3), SP.term 30 [r, s]]",
    ]
    declarations += epsilon_t_source_declarations()
    return emit_file(
        f"{PREFIX}.lean",
        ["LazardQuinticRootProjectionISparseEpsilonProductCertificate",
         "LazardQuinticRootReductionEBase"], declarations)


ATOM_DATA = {
    "RootE": ("rootENormal", ROOT_E),
    "P21": ("p21Normal", P21),
    "P22": ("p22Normal", P22),
    "P23": ("p23Normal", P23),
    "P24": ("p24Normal", P24),
}


def emit_atom_data(key: str) -> str:
    if key == "EpsilonECore":
        declarations = [
            "def epsilonECoreSource : SparsePolynomial :=\n"
            "  epsilonProductNormal.mul rootENormal",
            sparse.lean_polynomial("epsilonECoreNormal", EPSILON_E_CORE),
        ]
        imports = [f"{PREFIX}RootEData"]
    else:
        name, poly = ATOM_DATA[key]
        declarations = [sparse.lean_polynomial(name, poly)]
        imports = [f"{PREFIX}"]
    return emit_file(f"{PREFIX}{key}Data.lean", imports, declarations)


def emit_fourier_data(degree: int) -> str:
    declarations = [
        fourier_source_declaration(degree),
        sparse.lean_polynomial(
            f"fourierQuarticNormalW{degree}",
            FOURIER_QUARTIC_COEFF.get(degree, {})),
    ]
    return emit_file(
        f"{PREFIX}FourierW{degree}Data.lean", [f"{PREFIX}"], declarations)


def emit_epsilon_tu_data(degree: int) -> str:
    declarations = [
        sparse.lean_polynomial(
            f"epsilonTNormalW{degree}",
            EPSILON_T_COEFF.get(degree, {})),
        sparse.lean_polynomial(
            f"epsilonFormulaUNormalW{degree}",
            EPSILON_FORMULA_U_COEFF.get(degree, {})),
    ]
    return emit_file(
        f"{PREFIX}EpsilonTUW{degree}Data.lean", [f"{PREFIX}"], declarations)


def emit_intermediate_data() -> str:
    imports = [f"{PREFIX}{key}Data" for key in
               ["RootE", "P21", "P22", "P23", "P24", "EpsilonECore"]]
    imports += [f"{PREFIX}FourierW{degree}Data" for degree in range(17)]
    imports += [f"{PREFIX}EpsilonTUW{degree}Data" for degree in range(2, 9)]
    return emit_file(f"{PREFIX}IntermediateData.lean", imports, [])


def certificate(name: str, source: str, normal: str) -> str:
    return (
        "set_option maxRecDepth 300000 in\n"
        "set_option maxHeartbeats 20000000 in\n"
        f"theorem {name} :\n"
        f"    SparsePolynomial.normalize ({source}) =\n"
        f"      SparsePolynomial.normalize {normal} := by\n"
        "  decide")


def emit_algebra_certificates() -> str:
    declarations = [
        certificate("rootE_normal_certificate", "rootESource", "rootENormal"),
        certificate("p21_normal_certificate", "p21Source", "p21Normal"),
        certificate("p22_normal_certificate", "p22Source", "p22Normal"),
        certificate("p23_normal_certificate", "p23Source", "p23Normal"),
        certificate("p24_normal_certificate", "p24Source", "p24Normal"),
        certificate("epsilonE_core_normal_certificate",
                    "epsilonECoreSource", "epsilonECoreNormal"),
    ]
    return emit_file(
        f"{PREFIX}AlgebraCertificates.lean",
        [f"{PREFIX}IntermediateData"], declarations)


def emit_fourier_certificates() -> str:
    declarations = [
        certificate(
            f"fourier_quartic_w{degree}_certificate",
            f"fourierQuarticSourceW{degree}",
            f"fourierQuarticNormalW{degree}")
        for degree in range(17)
    ]
    return emit_file(
        f"{PREFIX}FourierCertificates.lean",
        [f"{PREFIX}IntermediateData"], declarations)


def emit_epsilon_tu_certificates() -> str:
    declarations = []
    for degree in range(2, 9):
        declarations.append(certificate(
            f"epsilon_t_w{degree}_certificate",
            f"epsilonTSourceW{degree}", f"epsilonTNormalW{degree}"))
        declarations.append(certificate(
            f"epsilon_formula_u_w{degree}_certificate",
            f"epsilonFormulaUSourceW{degree}",
            f"epsilonFormulaUNormalW{degree}"))
    return emit_file(
        f"{PREFIX}EpsilonTUCoefficientCertificates.lean",
        [f"{PREFIX}IntermediateData"], declarations)


def candidate_coefficient_declaration(degree: int) -> str:
    def lean_integer(value: int) -> str:
        return f"({value})" if value < 0 else str(value)

    terms: list[str] = []
    if degree == 0:
        terms.append("SP.term 5 [rootENormal, p22Normal]")
    if degree in EPSILON_COEFF:
        sign = next(iter(EPSILON_COEFF[degree].values()))
        terms.append(
            f"SP.term {lean_integer(5 * sign)} "
            "[epsilonECoreNormal, p21Normal]")
    if degree in range(2, 9) and degree != 5:
        terms.append(f"SP.term 2 [epsilonTNormalW{degree}, p23Normal]")
        terms.append(
            f"SP.term 2 [epsilonFormulaUNormalW{degree}, p24Normal]")
    for epsilon_degree, epsilon_poly in sorted(EPSILON_COEFF.items()):
        fourier_degree = degree - epsilon_degree
        if 0 <= fourier_degree <= 16:
            sign = next(iter(epsilon_poly.values()))
            terms.append(
                f"SP.term {lean_integer(-20 * sign)} [epsilonECoreNormal, "
                f"fourierQuarticNormalW{fourier_degree}]")
    rows = ",\n      ".join(terms)
    return (
        f"def numeratorP2CandidateW{degree} : SparsePolynomial :=\n"
        f"  SparsePolynomial.sum\n    [{rows}]")


def emit_components() -> str:
    declarations = [
        "def epsilonENormalSource : SparsePolynomial :=\n"
        "  rawSum [shiftOmega 1 epsilonECoreNormal,\n"
        "    shiftOmega 2 epsilonECoreNormal.neg,\n"
        "    shiftOmega 3 epsilonECoreNormal.neg,\n"
        "    shiftOmega 4 epsilonECoreNormal]",
        "def epsilonTNormalSource : SparsePolynomial :=\n"
        "  rawSum [shiftOmega 2 epsilonTNormalW2,\n"
        "    shiftOmega 3 epsilonTNormalW3,\n"
        "    shiftOmega 4 epsilonTNormalW4,\n"
        "    shiftOmega 5 epsilonTNormalW5,\n"
        "    shiftOmega 6 epsilonTNormalW6,\n"
        "    shiftOmega 7 epsilonTNormalW7,\n"
        "    shiftOmega 8 epsilonTNormalW8]",
        "def epsilonFormulaUNormalSource : SparsePolynomial :=\n"
        "  rawSum [shiftOmega 2 epsilonFormulaUNormalW2,\n"
        "    shiftOmega 3 epsilonFormulaUNormalW3,\n"
        "    shiftOmega 4 epsilonFormulaUNormalW4,\n"
        "    shiftOmega 5 epsilonFormulaUNormalW5,\n"
        "    shiftOmega 6 epsilonFormulaUNormalW6,\n"
        "    shiftOmega 7 epsilonFormulaUNormalW7,\n"
        "    shiftOmega 8 epsilonFormulaUNormalW8]",
        "def fourierQuarticNormalSource : SparsePolynomial :=\n"
        "  rawSum [" + ",\n    ".join(
            f"shiftOmega {degree} fourierQuarticNormalW{degree}"
            for degree in range(17)) + "]",
        "def numeratorP2Candidate : SparsePolynomial :=\n"
        "  SparsePolynomial.sum\n"
        "    [SP.term 5 [epsilonENormalSource, p21Normal],\n"
        "     SP.term 5 [rootENormal, p22Normal],\n"
        "     SP.term 2 [epsilonTNormalSource, p23Normal],\n"
        "     SP.term 2 [epsilonFormulaUNormalSource, p24Normal],\n"
        "     SP.term (-20) [epsilonENormalSource, fourierQuarticNormalSource]]",
    ]
    declarations += [candidate_coefficient_declaration(degree)
                     for degree in range(21)]
    return emit_file(
        f"{PREFIX}Components.lean",
        [f"{PREFIX}AlgebraCertificates",
         f"{PREFIX}FourierCertificates",
         f"{PREFIX}EpsilonTUCoefficientCertificates"], declarations)


def emit_product_factor_chunks() -> str:
    declarations = []
    for prefix, chunks in [("p22Chunk", P22_CHUNKS),
                           ("p23Chunk", P23_CHUNKS),
                           ("p24Chunk", P24_CHUNKS)]:
        declarations += [
            sparse.lean_polynomial(f"{prefix}{index}", chunk)
            for index, chunk in enumerate(chunks)
        ]
    return emit_file(
        f"{PREFIX}ProductFactorChunks.lean",
        [f"{PREFIX}IntermediateData"], declarations)


def emit_product_factor_chunks_certificate() -> str:
    declarations = []
    for normal, prefix, chunks in [
            ("p22Normal", "p22Chunk", P22_CHUNKS),
            ("p23Normal", "p23Chunk", P23_CHUNKS),
            ("p24Normal", "p24Chunk", P24_CHUNKS)]:
        rows = ", ".join(f"{prefix}{index}" for index in range(len(chunks)))
        raw = f"{prefix}Raw"
        declarations.append(
            f"def {raw} : SparsePolynomial := rawSum [{rows}]")
        declarations.append(certificate(
            f"{prefix}_partition_certificate", normal, raw))
    return emit_file(
        f"{PREFIX}ProductFactorChunksCertificate.lean",
        [f"{PREFIX}ProductFactorChunks"], declarations)


def product_final_normal_name(key: str) -> str:
    return key[0].lower() + key[1:] + "Normal"


def emit_direct_product_data(key: str) -> str:
    _, _, normal = DIRECT_PRODUCTS[key]
    normal_name = product_final_normal_name(key)
    parts = normal_parts(normal)
    imports = [f"{PREFIX}Product{key}Part{part}Data"
               for part in range(len(parts))]
    declaration = (
        f"def {normal_name} : SparsePolynomial :=\n"
        f"  rawSum [{', '.join(f'{normal_name}Part{part}' for part in range(len(parts)))}]")
    return emit_file(
        f"{PREFIX}Product{key}Data.lean", imports, [declaration])


def emit_direct_product_part_data(key: str, part: int) -> str:
    _, _, normal = DIRECT_PRODUCTS[key]
    parts = normal_parts(normal)
    normal_name = product_final_normal_name(key)
    declaration = sparse.lean_polynomial(f"{normal_name}Part{part}", parts[part])
    return emit_file(
        f"{PREFIX}Product{key}Part{part}Data.lean",
        [f"{PREFIX}IntermediateData"], [declaration])


def emit_direct_product_certificate(key: str) -> str:
    normal = product_final_normal_name(key)
    chunks = direct_factor_chunks(key)
    chunk_names = [f"{normal}Chunk{chunk}" for chunk in range(len(chunks))]
    raw_name = f"{normal}ChunkRaw"
    imports = [f"{PREFIX}Product{key}Data",
               f"{PREFIX}Product{key}FactorChunksCertificate"]
    imports += [f"{PREFIX}Product{key}Chunk{chunk}Certificate"
                for chunk in range(len(chunks))]
    declarations = [
        f"def {raw_name} : SparsePolynomial :=\n"
        f"  rawSum [{', '.join(chunk_names)}]",
        certificate(f"{normal}_merge_certificate", raw_name, normal),
    ]
    return emit_file(
        f"{PREFIX}Product{key}Certificate.lean", imports, declarations)


def direct_factor_chunk_name(key: str, chunk: int) -> str:
    return f"{product_final_normal_name(key)}FactorChunk{chunk}"


def direct_chunk_normal_name(key: str, chunk: int) -> str:
    return f"{product_final_normal_name(key)}Chunk{chunk}"


def emit_direct_product_factor_chunks(key: str) -> str:
    declarations = [
        sparse.lean_polynomial(direct_factor_chunk_name(key, chunk), poly)
        for chunk, poly in enumerate(direct_factor_chunks(key))
    ]
    return emit_file(
        f"{PREFIX}Product{key}FactorChunks.lean",
        [f"{PREFIX}IntermediateData"], declarations)


def emit_direct_product_factor_chunks_certificate(key: str) -> str:
    _, right, _ = DIRECT_PRODUCTS[key]
    chunks = direct_factor_chunks(key)
    raw_name = f"{product_final_normal_name(key)}FactorChunkRaw"
    declarations = [
        f"def {raw_name} : SparsePolynomial :=\n"
        f"  rawSum [{', '.join(direct_factor_chunk_name(key, chunk) for chunk in range(len(chunks)))}]",
        certificate(
            f"{product_final_normal_name(key)}_factor_partition_certificate",
            right, raw_name),
    ]
    return emit_file(
        f"{PREFIX}Product{key}FactorChunksCertificate.lean",
        [f"{PREFIX}Product{key}FactorChunks"], declarations)


def emit_direct_product_chunk_part_data(key: str, chunk: int, part: int) -> str:
    parts = normal_parts(direct_chunk_normal_poly(key, chunk))
    normal_name = direct_chunk_normal_name(key, chunk)
    declaration = sparse.lean_polynomial(f"{normal_name}Part{part}", parts[part])
    return emit_file(
        f"{PREFIX}Product{key}Chunk{chunk}Part{part}Data.lean",
        [f"{PREFIX}Product{key}FactorChunks"], [declaration])


def emit_direct_product_chunk_data(key: str, chunk: int) -> str:
    parts = normal_parts(direct_chunk_normal_poly(key, chunk))
    normal_name = direct_chunk_normal_name(key, chunk)
    imports = [f"{PREFIX}Product{key}Chunk{chunk}Part{part}Data"
               for part in range(len(parts))]
    declaration = (
        f"def {normal_name} : SparsePolynomial :=\n"
        f"  rawSum [{', '.join(f'{normal_name}Part{part}' for part in range(len(parts)))}]")
    return emit_file(
        f"{PREFIX}Product{key}Chunk{chunk}Data.lean", imports, [declaration])


def emit_direct_product_chunk_certificate(key: str, chunk: int) -> str:
    left, _, _ = DIRECT_PRODUCTS[key]
    normal_name = direct_chunk_normal_name(key, chunk)
    declaration = certificate(
        f"{normal_name}_certificate",
        f"{left}.mul {direct_factor_chunk_name(key, chunk)}", normal_name)
    return emit_file(
        f"{PREFIX}Product{key}Chunk{chunk}Certificate.lean",
        [f"{PREFIX}Product{key}Chunk{chunk}Data"], [declaration])


def chunk_normal_name(key: str, chunk: int) -> str:
    base = key[0].lower() + key[1:]
    return f"{base}Chunk{chunk}Normal"


def emit_chunked_product_final_data(key: str) -> str:
    _, _, _, _, normal_poly = CHUNKED_PRODUCTS[key]
    normal_name = product_final_normal_name(key)
    parts = normal_parts(normal_poly)
    imports = [f"{PREFIX}Product{key}Part{part}Data"
               for part in range(len(parts))]
    declaration = (
        f"def {normal_name} : SparsePolynomial :=\n"
        f"  rawSum [{', '.join(f'{normal_name}Part{part}' for part in range(len(parts)))}]")
    return emit_file(
        f"{PREFIX}Product{key}Data.lean", imports, [declaration])


def emit_chunked_product_part_data(key: str, part: int) -> str:
    _, _, _, _, normal_poly = CHUNKED_PRODUCTS[key]
    parts = normal_parts(normal_poly)
    normal_name = product_final_normal_name(key)
    declaration = sparse.lean_polynomial(f"{normal_name}Part{part}", parts[part])
    return emit_file(
        f"{PREFIX}Product{key}Part{part}Data.lean",
        [f"{PREFIX}IntermediateData"], [declaration])


def emit_chunked_product_chunk_data(key: str, chunk: int) -> str:
    _, left_poly, _, chunks, _ = CHUNKED_PRODUCTS[key]
    normal_poly = sparse.mul(left_poly, chunks[chunk])
    normal_name = chunk_normal_name(key, chunk)
    parts = normal_parts(normal_poly)
    imports = [f"{PREFIX}Product{key}Chunk{chunk}Part{part}Data"
               for part in range(len(parts))]
    declaration = (
        f"def {normal_name} : SparsePolynomial :=\n"
        f"  rawSum [{', '.join(f'{normal_name}Part{part}' for part in range(len(parts)))}]")
    return emit_file(
        f"{PREFIX}Product{key}Chunk{chunk}Data.lean", imports, [declaration])


def emit_chunked_product_chunk_part_data(key: str, chunk: int, part: int) -> str:
    _, left_poly, _, chunks, _ = CHUNKED_PRODUCTS[key]
    normal_poly = sparse.mul(left_poly, chunks[chunk])
    parts = normal_parts(normal_poly)
    normal_name = chunk_normal_name(key, chunk)
    declaration = sparse.lean_polynomial(f"{normal_name}Part{part}", parts[part])
    return emit_file(
        f"{PREFIX}Product{key}Chunk{chunk}Part{part}Data.lean",
        [f"{PREFIX}ProductFactorChunks"], [declaration])


def emit_chunked_product_chunk_certificate(key: str, chunk: int) -> str:
    left, _, factor_prefix, _, _ = CHUNKED_PRODUCTS[key]
    normal = chunk_normal_name(key, chunk)
    declaration = certificate(
        f"{normal}_certificate", f"{left}.mul {factor_prefix}{chunk}", normal)
    return emit_file(
        f"{PREFIX}Product{key}Chunk{chunk}Certificate.lean",
        [f"{PREFIX}Product{key}Chunk{chunk}Data"], [declaration])


def emit_chunked_product_certificate(key: str) -> str:
    _, _, _, chunks, _ = CHUNKED_PRODUCTS[key]
    imports = [f"{PREFIX}Product{key}Data"]
    imports += [f"{PREFIX}Product{key}Chunk{chunk}Certificate"
                for chunk in range(len(chunks))]
    chunk_names = [chunk_normal_name(key, chunk)
                   for chunk in range(len(chunks))]
    raw_name = key[0].lower() + key[1:] + "ChunkRaw"
    normal_name = product_final_normal_name(key)
    declarations = [
        f"def {raw_name} : SparsePolynomial :=\n"
        f"  rawSum [{', '.join(chunk_names)}]",
        certificate(f"{normal_name}_merge_certificate", raw_name, normal_name),
    ]
    return emit_file(
        f"{PREFIX}Product{key}Certificate.lean", imports, declarations)


def combine_patches(patches: list[str]) -> str:
    bodies = []
    for patch in patches:
        lines = patch.strip().splitlines()
        assert lines[0] == "*** Begin Patch" and lines[-1] == "*** End Patch"
        bodies.extend(lines[1:-1])
    return "*** Begin Patch\n" + "\n".join(bodies) + "\n*** End Patch\n"


def emit_chunked_product_bundle(key: str) -> str:
    chunks = CHUNKED_PRODUCTS[key][3]
    patches = [emit_chunked_product_final_data(key)]
    for chunk in range(len(chunks)):
        patches.append(emit_chunked_product_chunk_data(key, chunk))
        patches.append(emit_chunked_product_chunk_certificate(key, chunk))
    patches.append(emit_chunked_product_certificate(key))
    return combine_patches(patches)


def emit_product_normals() -> str:
    keys = list(DIRECT_PRODUCTS) + list(CHUNKED_PRODUCTS)
    imports = [f"{PREFIX}Product{key}Data" for key in keys]
    return emit_file(f"{PREFIX}ProductNormals.lean", imports, [])


def emit_product_certificates() -> str:
    imports = [f"{PREFIX}ProductFactorChunksCertificate"]
    imports += [f"{PREFIX}Product{key}Certificate"
                for key in list(DIRECT_PRODUCTS) + list(CHUNKED_PRODUCTS)]
    return emit_file(f"{PREFIX}ProductCertificates.lean", imports, [])


def eval_product_helper(chunk_count: int) -> str:
    b_names = [f"b{index}" for index in range(chunk_count)]
    c_names = [f"c{index}" for index in range(chunk_count)]
    polynomial_args = " ".join(["a", "b", *b_names, "c", *c_names])
    raw_b = ", ".join(b_names)
    raw_c = ", ".join(c_names)
    hypotheses = []
    for index, (b_name, c_name) in enumerate(zip(b_names, c_names)):
        hypotheses.append(
            f"    (h{index} : SparsePolynomial.normalize (a.mul {b_name}) =\n"
            f"      SparsePolynomial.normalize {c_name})")
    have_lines = "\n".join(
        f"  have h{index}' := SparsePolynomial.eval_eq_of_normalize_eq h{index} v"
        for index in range(chunk_count))
    rewrites = ", ".join(
        [*(f"← h{index}'" for index in range(chunk_count)), "hb'"])
    return (
        f"theorem eval_product_of_{chunk_count}_chunks\n"
        "    {R : Type*} [CommRing R]\n"
        f"    ({polynomial_args} : SparsePolynomial)\n"
        "    (hb : SparsePolynomial.normalize b =\n"
        f"      SparsePolynomial.normalize (rawSum [{raw_b}]))\n"
        + "\n".join(hypotheses) + "\n"
        "    (hc : SparsePolynomial.normalize "
        f"(rawSum [{raw_c}]) =\n"
        "      SparsePolynomial.normalize c)\n"
        "    (v : Fin 5 → R) :\n"
        "    SparsePolynomial.eval c v =\n"
        "      SparsePolynomial.eval a v * SparsePolynomial.eval b v := by\n"
        "  have hb' := SparsePolynomial.eval_eq_of_normalize_eq hb v\n"
        f"{have_lines}\n"
        "  have hc' := SparsePolynomial.eval_eq_of_normalize_eq hc v\n"
        "  rw [← hc']\n"
        "  simp only [eval_rawSum, List.map_cons, List.map_nil,\n"
        "    List.sum_cons, List.sum_nil]\n"
        f"  rw [{rewrites}]\n"
        "  simp only [SparsePolynomial.eval_mul, eval_rawSum, List.map_cons,\n"
        "    List.map_nil, List.sum_cons, List.sum_nil]\n"
        "  ring")


def emit_product_evaluation_helpers() -> str:
    declarations = [eval_product_helper(count) for count in [1, 2, 3, 4, 5, 8]]
    return emit_file(
        f"{PREFIX}ProductEvaluationHelpers.lean",
        [f"{PREFIX}ProductCertificates"], declarations)


def direct_product_evaluation(key: str) -> str:
    left, right, _ = DIRECT_PRODUCTS[key]
    normal = product_final_normal_name(key)
    count = len(direct_factor_chunks(key))
    factor_chunks = [direct_factor_chunk_name(key, chunk)
                     for chunk in range(count)]
    product_chunks = [direct_chunk_normal_name(key, chunk)
                      for chunk in range(count)]
    arguments = "\n    ".join([
        f"eval_product_of_{count}_chunks {left} {right}",
        " ".join(factor_chunks + [normal]),
        " ".join(product_chunks),
        f"{normal}_factor_partition_certificate",
        " ".join(f"{chunk}_certificate" for chunk in product_chunks),
        f"{normal}_merge_certificate v",
    ])
    return (
        f"theorem eval_{normal}\n"
        "    {R : Type*} [CommRing R] (v : Fin 5 → R) :\n"
        f"    SparsePolynomial.eval {normal} v =\n"
        f"      SparsePolynomial.eval {left} v *\n"
        f"        SparsePolynomial.eval {right} v :=\n"
        f"  {arguments}")


def emit_direct_product_evaluation() -> str:
    declarations = [direct_product_evaluation(key) for key in DIRECT_PRODUCTS]
    return emit_file(
        f"{PREFIX}ProductEvaluationDirect.lean",
        [f"{PREFIX}ProductEvaluationHelpers"], declarations)


def chunked_product_evaluation(key: str) -> str:
    left, _, factor_prefix, chunks, _ = CHUNKED_PRODUCTS[key]
    right = factor_prefix.replace("Chunk", "Normal")
    normal = product_final_normal_name(key)
    count = len(chunks)
    factor_chunks = [f"{factor_prefix}{chunk}" for chunk in range(count)]
    product_chunks = [chunk_normal_name(key, chunk) for chunk in range(count)]
    arguments = "\n    ".join([
        f"eval_product_of_{count}_chunks {left} {right}",
        " ".join(factor_chunks + [normal]),
        " ".join(product_chunks),
        f"{factor_prefix}_partition_certificate",
        " ".join(f"{chunk}_certificate" for chunk in product_chunks),
        f"{normal}_merge_certificate v",
    ])
    return (
        f"theorem eval_{normal}\n"
        "    {R : Type*} [CommRing R] (v : Fin 5 → R) :\n"
        f"    SparsePolynomial.eval {normal} v =\n"
        f"      SparsePolynomial.eval {left} v *\n"
        f"        SparsePolynomial.eval {right} v :=\n"
        f"  {arguments}")


def emit_chunked_product_evaluation() -> str:
    declarations = [chunked_product_evaluation(key) for key in CHUNKED_PRODUCTS]
    return emit_file(
        f"{PREFIX}ProductEvaluationChunked.lean",
        [f"{PREFIX}ProductEvaluationHelpers"], declarations)


def emit_product_evaluation() -> str:
    return emit_file(
        f"{PREFIX}ProductEvaluation.lean",
        [f"{PREFIX}ProductEvaluationDirect",
         f"{PREFIX}ProductEvaluationChunked"], [])


def lean_integer(value: int) -> str:
    return f"({value})" if value < 0 else str(value)


def staged_candidate_terms(
        degree: int) -> list[tuple[str, sparse.Polynomial]]:
    """Lean summands and their exact sparse values for one omega row."""
    terms: list[tuple[str, sparse.Polynomial]] = []
    if degree == 0:
        terms.append((
            "SP.smul 5 rootEP22Normal",
            sparse.scale(5, CHUNKED_PRODUCTS["RootEP22"][4])))
    if degree in EPSILON_COEFF:
        sign = next(iter(EPSILON_COEFF[degree].values()))
        coefficient = 5 * sign
        terms.append((
            f"SP.smul {lean_integer(coefficient)} epsilonEP21Normal",
            sparse.scale(coefficient, DIRECT_PRODUCTS["EpsilonEP21"][2])))
    if degree in [2, 3, 4, 6, 7, 8]:
        t_key = f"EpsilonTP23W{degree}"
        u_key = f"EpsilonFormulaUP24W{degree}"
        terms.append((
            f"SP.smul 2 epsilonTP23W{degree}Normal",
            sparse.scale(2, CHUNKED_PRODUCTS[t_key][4])))
        terms.append((
            f"SP.smul 2 epsilonFormulaUP24W{degree}Normal",
            sparse.scale(2, CHUNKED_PRODUCTS[u_key][4])))
    for epsilon_degree, epsilon_poly in sorted(EPSILON_COEFF.items()):
        fourier_degree = degree - epsilon_degree
        if 0 <= fourier_degree <= 16:
            sign = next(iter(epsilon_poly.values()))
            coefficient = -20 * sign
            key = f"EpsilonEFourierW{fourier_degree}"
            terms.append((
                f"SP.smul {lean_integer(coefficient)} "
                f"epsilonEFourierW{fourier_degree}Normal",
                sparse.scale(coefficient, DIRECT_PRODUCTS[key][2])))
    return terms


def staged_candidate_coefficient_declaration(degree: int) -> str:
    terms = [expression for expression, _ in staged_candidate_terms(degree)]
    return (
        f"def numeratorP2StagedCandidateW{degree} : SparsePolynomial :=\n"
        "  SparsePolynomial.sum\n    [" + ",\n      ".join(terms) + "]")


def emit_staged_components() -> str:
    imports = [f"{PREFIX}StagedW{degree}" for degree in range(21)]
    declarations = [
        "def numeratorP2StagedCandidate : SparsePolynomial :=\n"
        "  rawSum [" + ",\n    ".join(
            f"shiftOmega {degree} numeratorP2StagedCandidateW{degree}"
            for degree in range(21)) + "]"]
    return emit_file(
        f"{PREFIX}StagedComponents.lean",
        imports, declarations)


def staged_degree_product_keys(degree: int) -> list[str]:
    keys: list[str] = []
    if degree == 0:
        keys.append("RootEP22")
    if degree in EPSILON_COEFF:
        keys.append("EpsilonEP21")
    if degree in [2, 3, 4, 6, 7, 8]:
        keys += [f"EpsilonTP23W{degree}",
                 f"EpsilonFormulaUP24W{degree}"]
    for epsilon_degree in sorted(EPSILON_COEFF):
        fourier_degree = degree - epsilon_degree
        if 0 <= fourier_degree <= 16:
            keys.append(f"EpsilonEFourierW{fourier_degree}")
    return keys


def emit_staged_degree(degree: int) -> str:
    imports = [f"{PREFIX}Product{key}Data"
               for key in staged_degree_product_keys(degree)]
    return emit_file(
        f"{PREFIX}StagedW{degree}.lean", imports,
        [staged_candidate_coefficient_declaration(degree)])


def source_degree_poly(degree: int) -> sparse.Polynomial:
    return with_omega_degree(NUMERATOR_COEFF.get(degree, {}), degree)


def emit_source_data(degree: int) -> str:
    parts = normal_parts(source_degree_poly(degree))
    imports = [f"{PREFIX}SourceW{degree}Part{part}Data"
               for part in range(len(parts))]
    declaration = (
        f"def numeratorP2SourceW{degree} : SparsePolynomial :=\n"
        f"  rawSum [{', '.join(f'numeratorP2SourceW{degree}Part{part}' for part in range(len(parts)))}]")
    return emit_file(
        f"{PREFIX}SourceW{degree}Data.lean", imports, [declaration])


def emit_source_part_data(degree: int, part: int) -> str:
    parts = normal_parts(source_degree_poly(degree))
    declaration = sparse.lean_polynomial(
        f"numeratorP2SourceW{degree}Part{part}", parts[part])
    return emit_file(
        f"{PREFIX}SourceW{degree}Part{part}Data.lean",
        [f"{PREFIX}"], [declaration])


# A direct seven-summand W4 normalization reached 10.25 GiB RSS.  Keep every
# remaining source-row leaf at three summands or fewer, then merge at most
# three already-normalized group polynomials.
SOURCE_GROUP_SIZE = 3


def source_groups(
        degree: int) -> list[list[tuple[str, sparse.Polynomial]]]:
    terms = staged_candidate_terms(degree)
    return [terms[index:index + SOURCE_GROUP_SIZE]
            for index in range(0, len(terms), SOURCE_GROUP_SIZE)]


def source_group_poly(degree: int, group: int) -> sparse.Polynomial:
    poly = sparse.add(*(value for _, value in source_groups(degree)[group]))
    return with_omega_degree(poly, degree)


def source_group_raw_name(degree: int, group: int) -> str:
    return f"numeratorP2SourceW{degree}Group{group}Raw"


def source_group_normal_name(degree: int, group: int) -> str:
    return f"numeratorP2SourceW{degree}Group{group}Normal"


def emit_source_group_part_data(degree: int, group: int, part: int) -> str:
    parts = normal_parts(source_group_poly(degree, group))
    normal = source_group_normal_name(degree, group)
    declaration = sparse.lean_polynomial(f"{normal}Part{part}", parts[part])
    return emit_file(
        f"{PREFIX}SourceW{degree}Group{group}Part{part}Data.lean",
        [f"{PREFIX}"], [declaration])


def emit_source_group_data(degree: int, group: int) -> str:
    terms = source_groups(degree)[group]
    parts = normal_parts(source_group_poly(degree, group))
    normal = source_group_normal_name(degree, group)
    raw = source_group_raw_name(degree, group)
    imports = [f"{PREFIX}StagedW{degree}"]
    imports += [f"{PREFIX}SourceW{degree}Group{group}Part{part}Data"
                for part in range(len(parts))]
    declarations = [
        f"def {raw} : SparsePolynomial :=\n"
        "  rawSum [" + ",\n    ".join(
            f"shiftOmega {degree} ({expression})"
            for expression, _ in terms) + "]",
        f"def {normal} : SparsePolynomial :=\n"
        f"  rawSum [{', '.join(f'{normal}Part{part}' for part in range(len(parts)))}]",
    ]
    return emit_file(
        f"{PREFIX}SourceW{degree}Group{group}Data.lean",
        imports, declarations)


def emit_source_group_certificate(degree: int, group: int) -> str:
    raw = source_group_raw_name(degree, group)
    normal = source_group_normal_name(degree, group)
    declaration = certificate(
        f"numeratorP2_source_w{degree}_group{group}_certificate",
        raw, normal)
    return emit_file(
        f"{PREFIX}SourceW{degree}Group{group}Certificate.lean",
        [f"{PREFIX}SourceW{degree}Group{group}Data"], [declaration])


def emit_bounded_source_certificate(degree: int) -> str:
    groups = source_groups(degree)
    grouped = f"numeratorP2SourceW{degree}Grouped"
    imports = [f"{PREFIX}SourceW{degree}Data"]
    imports += [f"{PREFIX}SourceW{degree}Group{group}Certificate"
                for group in range(len(groups))]
    declarations = [
        f"def {grouped} : SparsePolynomial :=\n"
        "  rawSum [" + ", ".join(
            source_group_normal_name(degree, group)
            for group in range(len(groups))) + "]",
        certificate(
            f"numeratorP2_source_w{degree}_merge_certificate",
            grouped, f"numeratorP2SourceW{degree}"),
    ]
    haves = "\n".join(
        f"  have h{group} := SparsePolynomial.eval_eq_of_normalize_eq\n"
        f"    numeratorP2_source_w{degree}_group{group}_certificate v"
        for group in range(len(groups)))
    rewrites = ", ".join(f"← h{group}" for group in range(len(groups)))
    group_raw_names = ", ".join(
        source_group_raw_name(degree, group) for group in range(len(groups)))
    declarations.append(
        f"theorem eval_numeratorP2SourceW{degree}_eq_staged\n"
        "    {R : Type*} [CommRing R] (v : Fin 5 → R) :\n"
        f"    SparsePolynomial.eval numeratorP2SourceW{degree} v =\n"
        f"      SparsePolynomial.eval (shiftOmega {degree} "
        f"numeratorP2StagedCandidateW{degree}) v := by\n"
        f"{haves}\n"
        "  have hm := SparsePolynomial.eval_eq_of_normalize_eq\n"
        f"    numeratorP2_source_w{degree}_merge_certificate v\n"
        "  rw [← hm]\n"
        f"  simp only [{grouped}, eval_rawSum, List.map_cons, List.map_nil,\n"
        "    List.sum_cons, List.sum_nil]\n"
        f"  rw [{rewrites}]\n"
        f"  simp only [{group_raw_names}, numeratorP2StagedCandidateW{degree},\n"
        "    eval_rawSum, eval_shiftOmega, SparsePolynomial.eval_sum,\n"
        "    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]\n"
        "  ring")
    return emit_file(
        f"{PREFIX}SourceW{degree}Certificate.lean", imports, declarations)


def quotient_degree_poly(degree: int) -> sparse.Polynomial:
    return sparse.omega_slice(QUOTIENT, degree)


def emit_quotient_data(degree: int) -> str:
    parts = normal_parts(quotient_degree_poly(degree))
    imports = [f"{PREFIX}QuotientW{degree}Part{part}Data"
               for part in range(len(parts))]
    declaration = (
        f"def numeratorP2QuotientW{degree} : SparsePolynomial :=\n"
        f"  rawSum [{', '.join(f'numeratorP2QuotientW{degree}Part{part}' for part in range(len(parts)))}]")
    return emit_file(
        f"{PREFIX}QuotientW{degree}Data.lean", imports, [declaration])


def emit_quotient_part_data(degree: int, part: int) -> str:
    parts = normal_parts(quotient_degree_poly(degree))
    declaration = sparse.lean_polynomial(
        f"numeratorP2QuotientW{degree}Part{part}", parts[part])
    return emit_file(
        f"{PREFIX}QuotientW{degree}Part{part}Data.lean",
        [f"{PREFIX}"], [declaration])


QUOTIENT_GROUP_SIZE = 3


def quotient_convolution_terms(
        degree: int) -> list[tuple[str, sparse.Polynomial]]:
    indices = [degree - offset for offset in range(5)
               if 0 <= degree - offset <= 16]
    return [(
        f"shiftOmega {degree - index} numeratorP2QuotientW{index}",
        with_omega_degree(quotient_degree_poly(index), degree))
        for index in indices]


def quotient_groups(
        degree: int) -> list[list[tuple[str, sparse.Polynomial]]]:
    terms = quotient_convolution_terms(degree)
    return [terms[index:index + QUOTIENT_GROUP_SIZE]
            for index in range(0, len(terms), QUOTIENT_GROUP_SIZE)]


def quotient_group_poly(degree: int, group: int) -> sparse.Polynomial:
    return sparse.add(*(value for _, value in quotient_groups(degree)[group]))


def quotient_group_raw_name(degree: int, group: int) -> str:
    return f"numeratorP2QuotientW{degree}Group{group}Raw"


def quotient_group_normal_name(degree: int, group: int) -> str:
    return f"numeratorP2QuotientW{degree}Group{group}Normal"


def emit_quotient_group_part_data(degree: int, group: int, part: int) -> str:
    parts = normal_parts(quotient_group_poly(degree, group))
    normal = quotient_group_normal_name(degree, group)
    declaration = sparse.lean_polynomial(f"{normal}Part{part}", parts[part])
    return emit_file(
        f"{PREFIX}QuotientW{degree}Group{group}Part{part}Data.lean",
        [f"{PREFIX}"], [declaration])


def emit_quotient_group_data(degree: int, group: int) -> str:
    terms = quotient_groups(degree)[group]
    parts = normal_parts(quotient_group_poly(degree, group))
    normal = quotient_group_normal_name(degree, group)
    raw = quotient_group_raw_name(degree, group)
    indices = [degree - next(index for index in range(5)
        if expression.startswith(f"shiftOmega {index} "))
        for expression, _ in terms]
    imports = [f"{PREFIX}QuotientW{index}Data" for index in indices]
    imports += [f"{PREFIX}QuotientW{degree}Group{group}Part{part}Data"
                for part in range(len(parts))]
    declarations = [
        f"def {raw} : SparsePolynomial :=\n"
        "  rawSum [" + ", ".join(expression for expression, _ in terms) + "]",
        f"def {normal} : SparsePolynomial :=\n"
        f"  rawSum [{', '.join(f'{normal}Part{part}' for part in range(len(parts)))}]",
    ]
    return emit_file(
        f"{PREFIX}QuotientW{degree}Group{group}Data.lean",
        imports, declarations)


def emit_quotient_group_certificate(degree: int, group: int) -> str:
    raw = quotient_group_raw_name(degree, group)
    normal = quotient_group_normal_name(degree, group)
    declaration = certificate(
        f"numeratorP2_quotient_w{degree}_group{group}_certificate",
        raw, normal)
    return emit_file(
        f"{PREFIX}QuotientW{degree}Group{group}Certificate.lean",
        [f"{PREFIX}QuotientW{degree}Group{group}Data"], [declaration])


def emit_bounded_quotient_certificate(degree: int) -> str:
    groups = quotient_groups(degree)
    convolution = f"numeratorP2QuotientConvolutionW{degree}"
    grouped = f"numeratorP2QuotientW{degree}Grouped"
    imports = [f"{PREFIX}SourceW{degree}Data"]
    imports += [f"{PREFIX}QuotientW{degree}Group{group}Certificate"
                for group in range(len(groups))]
    declarations = [
        f"def {convolution} : SparsePolynomial :=\n"
        "  rawSum [" + ", ".join(
            expression for expression, _ in quotient_convolution_terms(degree)) + "]",
        f"def {grouped} : SparsePolynomial :=\n"
        "  rawSum [" + ", ".join(
            quotient_group_normal_name(degree, group)
            for group in range(len(groups))) + "]",
        certificate(
            f"numeratorP2_quotient_w{degree}_merge_certificate",
            grouped, f"numeratorP2SourceW{degree}"),
    ]
    haves = "\n".join(
        f"  have h{group} := SparsePolynomial.eval_eq_of_normalize_eq\n"
        f"    numeratorP2_quotient_w{degree}_group{group}_certificate v"
        for group in range(len(groups)))
    rewrites = ", ".join(f"← h{group}" for group in range(len(groups)))
    group_raw_names = ", ".join(
        quotient_group_raw_name(degree, group) for group in range(len(groups)))
    declarations.append(
        f"theorem eval_numeratorP2SourceW{degree}_eq_quotientConvolution\n"
        "    {R : Type*} [CommRing R] (v : Fin 5 → R) :\n"
        f"    SparsePolynomial.eval numeratorP2SourceW{degree} v =\n"
        f"      SparsePolynomial.eval {convolution} v := by\n"
        f"{haves}\n"
        "  have hm := SparsePolynomial.eval_eq_of_normalize_eq\n"
        f"    numeratorP2_quotient_w{degree}_merge_certificate v\n"
        "  rw [← hm]\n"
        f"  simp only [{grouped}, eval_rawSum, List.map_cons, List.map_nil,\n"
        "    List.sum_cons, List.sum_nil]\n"
        f"  rw [{rewrites}]\n"
        f"  simp only [{group_raw_names}, {convolution}, eval_rawSum,\n"
        "    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]\n"
        "  ring")
    return emit_file(
        f"{PREFIX}QuotientW{degree}Certificate.lean", imports, declarations)


def emit_source_certificate(degree: int) -> str:
    if degree >= 4:
        return emit_bounded_source_certificate(degree)
    declarations = [certificate(
        f"numeratorP2_source_w{degree}_certificate",
        f"shiftOmega {degree} numeratorP2StagedCandidateW{degree}",
        f"numeratorP2SourceW{degree}")]
    return emit_file(
        f"{PREFIX}SourceW{degree}Certificate.lean",
        [f"{PREFIX}SourceW{degree}Data", f"{PREFIX}StagedW{degree}"],
        declarations)


def emit_quotient_certificate(degree: int) -> str:
    if 10 <= degree <= 16:
        return emit_bounded_quotient_certificate(degree)
    q_indices = [degree - offset for offset in range(5)
                 if 0 <= degree - offset <= 16]
    imports = [f"{PREFIX}SourceW{degree}Data"]
    imports += [f"{PREFIX}QuotientW{index}Data" for index in q_indices]
    convolution_terms = [
        f"shiftOmega {degree - index} numeratorP2QuotientW{index}"
        for index in q_indices
    ]
    declarations = [
        f"def numeratorP2QuotientConvolutionW{degree} : SparsePolynomial :=\n"
        f"  rawSum [{', '.join(convolution_terms)}]",
        certificate(
            f"numeratorP2_quotient_w{degree}_certificate",
            f"numeratorP2SourceW{degree}",
            f"numeratorP2QuotientConvolutionW{degree}"),
    ]
    return emit_file(
        f"{PREFIX}QuotientW{degree}Certificate.lean", imports, declarations)


def emit_aggregate() -> str:
    imports = [f"{PREFIX}SourceW{degree}Certificate" for degree in range(21)]
    imports += [f"{PREFIX}QuotientW{degree}Certificate" for degree in range(21)]
    source_names = ",\n    ".join(
        f"numeratorP2SourceW{degree}" for degree in range(21))
    quotient_names = ",\n    ".join(
        f"numeratorP2QuotientW{degree}" for degree in range(17))
    declarations = [
        "def numeratorP2SourceRows : List SparsePolynomial :=\n"
        f"  [{source_names}]",
        "def numeratorP2Normal : SparsePolynomial :=\n"
        "  rawSum numeratorP2SourceRows",
        "def numeratorP2QuotientRows : List SparsePolynomial :=\n"
        f"  [{quotient_names}]",
        "def numeratorP2Quotient : SparsePolynomial :=\n"
        "  rawSum numeratorP2QuotientRows",
    ]
    return emit_file(f"{PREFIX}Certificate.lean", imports, declarations)


# ---------------------------------------------------------------------------
# Rocq output
# ---------------------------------------------------------------------------

COQ_NAMESPACE = "PolynomialFormulasLazardQuinticRootFourierNumeratorP2Sparse"
COQ_DATA_NAMESPACE = COQ_NAMESPACE + "Data"


def coq_integer(value: int) -> str:
    if value < 0:
        return f"(- {-value}%:Z)"
    return f"{value}%:Z"


def coq_polynomial(name: str, poly: sparse.Polynomial) -> str:
    rows = []
    for exponent, coefficient in sorted(poly.items()):
        # Rocq reuses the sextic sparse carrier.  The first four entries are
        # independent depressed roots; the last two coordinates are unused.
        powers = "; ".join(str(value) for value in
                           (*exponent[:4], 0, 0))
        rows.append(
            f"  ({coq_integer(coefficient)}, [tuple {powers}]%N)")
    if not rows:
        body = "[::]"
    else:
        body = "[::\n" + ";\n".join(rows) + "\n]"
    return f"Definition {name} : SP.sparse_polynomial := {body}."


def coq_module(module_name: str, imports: list[str], body: list[str]) -> str:
    direct_imports = list(dict.fromkeys([
        "SexticSparsePolynomials", *imports,
    ]))
    import_text = "\n".join(
        "From PolynomialFormulas Require Import " + name + "."
        for name in direct_imports)
    return "\n\n".join([
        "From mathcomp Require Import all_ssreflect all_fingroup all_algebra.",
        import_text,
        "Set Implicit Arguments.\n"
        "Unset Strict Implicit.\n"
        "Unset Printing Implicit Defensive.",
        f"Module {module_name}.",
        "Module SP := PolynomialFormulasSexticSparsePolynomials.",
        "Local Open Scope ring_scope.",
        *body,
        f"End {module_name}.",
    ]) + "\n"


def emit_coq_file(filename: str, contents: str) -> str:
    return sparse.patch_for_file(COQ_DIR / filename, contents)


def emit_coq_data_part(part: int) -> str:
    module_name = COQ_DATA_NAMESPACE + f"Part{part}"
    contents = coq_module(
        module_name, [PREFIX],
        [coq_polynomial(f"p2_common_part{part}", COQ_DATA_PARTS[part])])
    return emit_coq_file(f"{PREFIX}DataPart{part}.v", contents)


def emit_coq_data() -> str:
    imports = [f"{PREFIX}DataPart{part}"
               for part in range(len(COQ_DATA_PARTS))]
    aliases = [
        f"Module P{part} := {COQ_DATA_NAMESPACE}Part{part}."
        for part in range(len(COQ_DATA_PARTS))]
    pieces = " ++\n    ".join(
        f"P{part}.p2_common_part{part}"
        for part in range(len(COQ_DATA_PARTS)))
    body = aliases + [
        "(** The common cyclic coefficient.  The generator independently\n"
        "    folds the 30,282-term integer numerator modulo [omega^5 = 1]. *)\n"
        "Definition p2_common_normal : SP.sparse_polynomial :=\n"
        f"  {pieces}."
    ]
    contents = coq_module(COQ_DATA_NAMESPACE, imports, body)
    return emit_coq_file(f"{PREFIX}Data.v", contents)


def emit_coq_coefficient_certificate(coefficient: int) -> str:
    module_name = COQ_NAMESPACE + f"Coefficient{coefficient}Certificate"
    body = [
        f"Module S := {COQ_NAMESPACE}.",
        f"Module D := {COQ_DATA_NAMESPACE}.",
        "(** Kernel-checked sparse normalization of one cyclic row. *)\n"
        f"Lemma p2_sparse_coefficient{coefficient}_certificate :\n"
        f"  S.sparse_cyclic{coefficient} S.sparse_p2_numerator_difference =\n"
        "    D.p2_common_normal.\n"
        "Proof. vm_compute. Qed."
    ]
    contents = coq_module(
        module_name, [PREFIX, f"{PREFIX}Data"], body)
    return emit_coq_file(
        f"{PREFIX}Coefficient{coefficient}Certificate.v", contents)


def emit_coq_certificates() -> str:
    imports = [f"{PREFIX}Coefficient{coefficient}Certificate"
               for coefficient in range(5)]
    aliases = [
        f"Module C{coefficient} := "
        f"{COQ_NAMESPACE}Coefficient{coefficient}Certificate."
        for coefficient in range(5)]
    theorem_rows = []
    for coefficient in range(4):
        successor = coefficient + 1
        theorem_rows.append(
            f"Theorem p2_sparse_coefficient{coefficient}{successor}\n"
            "    {F : fieldType} (roots : 5.-tuple F)\n"
            "    (hsum : lazard_root_esymm1 roots = 0) :\n"
            f"  lazard_cyclic{coefficient} "
            "(P2C.lazard_cyclic_p2_numerator_difference roots) =\n"
            f"    lazard_cyclic{successor} "
            "(P2C.lazard_cyclic_p2_numerator_difference roots).\n"
            "Proof.\n"
            "have hbridge := S.eval_sparse_p2_numerator_difference "
            "(roots := roots) hsum.\n"
            f"have hleft := congrArg lazard_cyclic{coefficient} hbridge.\n"
            f"have hright := congrArg lazard_cyclic{successor} hbridge.\n"
            "rewrite /S.eval_sparse_cyclic /= in hleft hright.\n"
            "rewrite -hleft -hright\n"
            f"  C{coefficient}.p2_sparse_coefficient{coefficient}_certificate\n"
            f"  C{successor}.p2_sparse_coefficient{successor}_certificate.\n"
            "reflexivity.\n"
            "Qed."
        )
    body = [
        f"Module S := {COQ_NAMESPACE}.",
        "Module P2C := "
        "PolynomialFormulasLazardQuinticRootFourierNumeratorP2Common.",
        *aliases,
        *theorem_rows,
    ]
    contents = coq_module(COQ_NAMESPACE + "Certificates", imports, body)
    return emit_coq_file(f"{PREFIX}Certificates.v", contents)


def emit_coq_manifest() -> str:
    files = [f"{PREFIX}.v"]
    files += [f"{PREFIX}DataPart{part}.v"
              for part in range(len(COQ_DATA_PARTS))]
    files += [f"{PREFIX}Data.v"]
    files += [f"{PREFIX}Coefficient{coefficient}Certificate.v"
              for coefficient in range(5)]
    files += [f"{PREFIX}Certificates.v"]
    order = "\n".join(f"{index + 1}. `{name}`"
                      for index, name in enumerate(files))
    text = f"""# P2 sparse Rocq certificate manifest

Generated data and certificate shards:

```text
python3 Algebra/PolynomialFormulas/Tools/generate_lazard_root_fourier_numerator_p2_sparse.py --kind coq-bundle
```

The bundle folds a {len(NUMERATOR):,}-term source numerator into five cyclic
rows.  Each row is independently checked against the same
{len(COQ_COMMON):,}-term normal form.  Data declarations are bounded at
{COQ_DATA_PART_SIZE} terms and the expensive reductions are isolated into
five separately compiled coefficient leaves.  The first file below is the
handwritten semantic checker and is intentionally not overwritten by the
generator.

Dependency order:

{order}
"""
    return emit_coq_file(f"{PREFIX}Manifest.md", text)


def emit_coq_bundle() -> str:
    patches = [emit_coq_data_part(part)
               for part in range(len(COQ_DATA_PARTS))]
    patches.append(emit_coq_data())
    patches += [emit_coq_coefficient_certificate(coefficient)
                for coefficient in range(5)]
    patches.append(emit_coq_certificates())
    patches.append(emit_coq_manifest())
    return combine_patches(patches)


def stats() -> str:
    return "\n".join([
        f"source terms: {len(NUMERATOR)}",
        f"quotient terms: {len(QUOTIENT)}",
        f"source omega degree: {max(e[4] for e in NUMERATOR)}",
        f"quotient omega degree: {max(e[4] for e in QUOTIENT)}",
        "source slices: " + repr([
            len(NUMERATOR_COEFF.get(degree, {})) for degree in range(21)]),
        "quotient slices: " + repr([
            len(sparse.omega_slice(QUOTIENT, degree)) for degree in range(17)]),
        f"Rocq cyclic common terms: {len(COQ_COMMON)}",
        f"Rocq data parts: {len(COQ_DATA_PARTS)}",
    ]) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--kind", required=True, choices=[
        "base", "atom-data", "fourier-data", "epsilon-tu-data",
        "intermediate-data", "algebra-certificates", "fourier-certificates",
        "epsilon-tu-certificates", "components", "source-data",
        "source-part-data", "quotient-data", "quotient-part-data",
        "source-group-part-data", "source-group-data",
        "source-group-certificate", "source-certificate", "quotient-certificate",
        "quotient-group-part-data", "quotient-group-data",
        "quotient-group-certificate",
        "product-factor-chunks", "product-factor-chunks-certificate",
        "direct-product-data", "direct-product-part-data",
        "direct-product-factor-chunks",
        "direct-product-factor-chunks-certificate",
        "direct-product-chunk-part-data", "direct-product-chunk-data",
        "direct-product-chunk-certificate", "direct-product-certificate",
        "chunked-product-data", "chunked-product-part-data",
        "chunked-product-chunk-data", "chunked-product-chunk-part-data",
        "chunked-product-chunk-certificate", "chunked-product-certificate",
        "chunked-product-bundle",
        "product-normals", "product-certificates", "staged-components",
        "product-evaluation-helpers", "direct-product-evaluation",
        "chunked-product-evaluation", "product-evaluation",
        "staged-degree",
        "aggregate", "coq-data-part", "coq-data",
        "coq-coefficient-certificate", "coq-certificates",
        "coq-manifest", "coq-bundle", "stats"])
    parser.add_argument("--degree", type=int)
    parser.add_argument("--key")
    parser.add_argument("--chunk", type=int)
    parser.add_argument("--part", type=int)
    parser.add_argument("--group", type=int)
    args = parser.parse_args()
    if args.kind == "stats":
        print(stats(), end="")
        return
    if args.kind in {"fourier-data", "epsilon-tu-data", "source-data",
                     "source-part-data", "quotient-data",
                     "quotient-part-data", "source-certificate",
                     "quotient-certificate", "staged-degree",
                     "source-group-part-data", "source-group-data",
                     "source-group-certificate", "quotient-group-part-data",
                     "quotient-group-data", "quotient-group-certificate"}:
        if args.degree is None:
            parser.error("--degree is required")
    if args.kind == "coq-coefficient-certificate" and args.degree is None:
        parser.error("--degree is required")
    emitters = {
        "base": emit_base,
        "intermediate-data": emit_intermediate_data,
        "algebra-certificates": emit_algebra_certificates,
        "fourier-certificates": emit_fourier_certificates,
        "epsilon-tu-certificates": emit_epsilon_tu_certificates,
        "components": emit_components,
        "product-factor-chunks": emit_product_factor_chunks,
        "product-factor-chunks-certificate": emit_product_factor_chunks_certificate,
        "product-normals": emit_product_normals,
        "product-certificates": emit_product_certificates,
        "product-evaluation-helpers": emit_product_evaluation_helpers,
        "direct-product-evaluation": emit_direct_product_evaluation,
        "chunked-product-evaluation": emit_chunked_product_evaluation,
        "product-evaluation": emit_product_evaluation,
        "staged-components": emit_staged_components,
        "aggregate": emit_aggregate,
        "coq-data": emit_coq_data,
        "coq-certificates": emit_coq_certificates,
        "coq-manifest": emit_coq_manifest,
        "coq-bundle": emit_coq_bundle,
    }
    if args.kind == "coq-data-part":
        if args.part is None or not 0 <= args.part < len(COQ_DATA_PARTS):
            parser.error("--part is out of range")
        output = emit_coq_data_part(args.part)
    elif args.kind == "coq-coefficient-certificate":
        if not 0 <= args.degree < 5:
            parser.error("--degree must be between 0 and 4")
        output = emit_coq_coefficient_certificate(args.degree)
    elif args.kind == "atom-data":
        if args.key not in set(ATOM_DATA) | {"EpsilonECore"}:
            parser.error("--key must name an atom-data module")
        output = emit_atom_data(args.key)
    elif args.kind == "fourier-data":
        if not 0 <= args.degree <= 16:
            parser.error("--degree must be between 0 and 16")
        output = emit_fourier_data(args.degree)
    elif args.kind == "epsilon-tu-data":
        if not 2 <= args.degree <= 8:
            parser.error("--degree must be between 2 and 8")
        output = emit_epsilon_tu_data(args.degree)
    elif args.kind in {"source-data", "source-part-data"}:
        if not 0 <= args.degree <= 20:
            parser.error("--degree must be between 0 and 20")
        if args.kind == "source-part-data":
            parts = normal_parts(source_degree_poly(args.degree))
            if args.part is None or not 0 <= args.part < len(parts):
                parser.error("--part is out of range")
            output = emit_source_part_data(args.degree, args.part)
        else:
            output = emit_source_data(args.degree)
    elif args.kind in {"quotient-data", "quotient-part-data"}:
        if not 0 <= args.degree <= 16:
            parser.error("--degree must be between 0 and 16")
        if args.kind == "quotient-part-data":
            parts = normal_parts(quotient_degree_poly(args.degree))
            if args.part is None or not 0 <= args.part < len(parts):
                parser.error("--part is out of range")
            output = emit_quotient_part_data(args.degree, args.part)
        else:
            output = emit_quotient_data(args.degree)
    elif args.kind == "source-certificate":
        output = emit_source_certificate(args.degree)
    elif args.kind in {"source-group-part-data", "source-group-data",
                       "source-group-certificate"}:
        groups = source_groups(args.degree)
        if args.group is None or not 0 <= args.group < len(groups):
            parser.error("--group is out of range")
        if args.kind == "source-group-part-data":
            parts = normal_parts(source_group_poly(args.degree, args.group))
            if args.part is None or not 0 <= args.part < len(parts):
                parser.error("--part is out of range")
            output = emit_source_group_part_data(
                args.degree, args.group, args.part)
        elif args.kind == "source-group-data":
            output = emit_source_group_data(args.degree, args.group)
        else:
            output = emit_source_group_certificate(args.degree, args.group)
    elif args.kind == "quotient-certificate":
        output = emit_quotient_certificate(args.degree)
    elif args.kind in {"quotient-group-part-data", "quotient-group-data",
                       "quotient-group-certificate"}:
        groups = quotient_groups(args.degree)
        if args.group is None or not 0 <= args.group < len(groups):
            parser.error("--group is out of range")
        if args.kind == "quotient-group-part-data":
            parts = normal_parts(quotient_group_poly(args.degree, args.group))
            if args.part is None or not 0 <= args.part < len(parts):
                parser.error("--part is out of range")
            output = emit_quotient_group_part_data(
                args.degree, args.group, args.part)
        elif args.kind == "quotient-group-data":
            output = emit_quotient_group_data(args.degree, args.group)
        else:
            output = emit_quotient_group_certificate(args.degree, args.group)
    elif args.kind == "staged-degree":
        output = emit_staged_degree(args.degree)
    elif args.kind in {"direct-product-data", "direct-product-part-data",
                       "direct-product-factor-chunks",
                       "direct-product-factor-chunks-certificate",
                       "direct-product-chunk-part-data",
                       "direct-product-chunk-data",
                       "direct-product-chunk-certificate",
                       "direct-product-certificate"}:
        if args.key not in DIRECT_PRODUCTS:
            parser.error("--key must name a direct product")
        if args.kind in {"direct-product-chunk-part-data",
                         "direct-product-chunk-data",
                         "direct-product-chunk-certificate"}:
            chunks = direct_factor_chunks(args.key)
            if args.chunk is None or not 0 <= args.chunk < len(chunks):
                parser.error("--chunk is out of range")
            if args.kind == "direct-product-chunk-part-data":
                parts = normal_parts(direct_chunk_normal_poly(args.key, args.chunk))
                if args.part is None or not 0 <= args.part < len(parts):
                    parser.error("--part is out of range")
                output = emit_direct_product_chunk_part_data(
                    args.key, args.chunk, args.part)
            elif args.kind == "direct-product-chunk-data":
                output = emit_direct_product_chunk_data(args.key, args.chunk)
            else:
                output = emit_direct_product_chunk_certificate(args.key, args.chunk)
        elif args.kind == "direct-product-part-data":
            parts = normal_parts(DIRECT_PRODUCTS[args.key][2])
            if args.part is None or not 0 <= args.part < len(parts):
                parser.error("--part is out of range")
            output = emit_direct_product_part_data(args.key, args.part)
        elif args.kind == "direct-product-data":
            output = emit_direct_product_data(args.key)
        elif args.kind == "direct-product-factor-chunks":
            output = emit_direct_product_factor_chunks(args.key)
        elif args.kind == "direct-product-factor-chunks-certificate":
            output = emit_direct_product_factor_chunks_certificate(args.key)
        else:
            output = emit_direct_product_certificate(args.key)
    elif args.kind in {"chunked-product-data", "chunked-product-part-data",
                       "chunked-product-certificate",
                       "chunked-product-bundle"}:
        if args.key not in CHUNKED_PRODUCTS:
            parser.error("--key must name a chunked product")
        if args.kind == "chunked-product-part-data":
            parts = normal_parts(CHUNKED_PRODUCTS[args.key][4])
            if args.part is None or not 0 <= args.part < len(parts):
                parser.error("--part is out of range")
            output = emit_chunked_product_part_data(args.key, args.part)
        elif args.kind == "chunked-product-data":
            output = emit_chunked_product_final_data(args.key)
        elif args.kind == "chunked-product-certificate":
            output = emit_chunked_product_certificate(args.key)
        else:
            output = emit_chunked_product_bundle(args.key)
    elif args.kind in {"chunked-product-chunk-data",
                       "chunked-product-chunk-part-data",
                       "chunked-product-chunk-certificate"}:
        if args.key not in CHUNKED_PRODUCTS or args.chunk is None:
            parser.error("--key and --chunk are required for a chunked product")
        chunks = CHUNKED_PRODUCTS[args.key][3]
        if not 0 <= args.chunk < len(chunks):
            parser.error("--chunk is out of range")
        if args.kind == "chunked-product-chunk-part-data":
            _, left_poly, _, chunks, _ = CHUNKED_PRODUCTS[args.key]
            parts = normal_parts(sparse.mul(left_poly, chunks[args.chunk]))
            if args.part is None or not 0 <= args.part < len(parts):
                parser.error("--part is out of range")
            output = emit_chunked_product_chunk_part_data(
                args.key, args.chunk, args.part)
        elif args.kind == "chunked-product-chunk-data":
            output = emit_chunked_product_chunk_data(args.key, args.chunk)
        else:
            output = emit_chunked_product_chunk_certificate(args.key, args.chunk)
    else:
        output = emitters[args.kind]()
    print(output, end="")


if __name__ == "__main__":
    main()
