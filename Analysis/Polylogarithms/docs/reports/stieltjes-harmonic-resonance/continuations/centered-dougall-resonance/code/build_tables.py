#!/usr/bin/env python3
"""Regenerate exact truncation tables and a TeX-linked identity index.

The table entries are rational strings, never floating-point approximations.
The identity index preserves the actual displayed formula from article.tex;
it is an index for integration, not a CAS or proof-assistant representation.
"""
from __future__ import annotations
import json
from pathlib import Path
import re
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]


def formula_for_label(text: str, label: str) -> str:
    target = r"\label{" + label + "}"
    pos = text.find(target)
    if pos < 0:
        raise ValueError(f"Missing equation label: {label}")
    starts = list(re.finditer(r"\\begin\{(equation|align|gather|multline)\*?\}", text[:pos]))
    if not starts:
        raise ValueError(f"No displayed environment before {label}")
    start = starts[-1]
    env = start.group(0)[len(r"\begin{"):-1]
    end_marker = r"\end{" + env + "}"
    end = text.find(end_marker, pos)
    if end < 0:
        raise ValueError(f"Unclosed environment for {label}")
    return text[start.start():end + len(end_marker)]


def main() -> None:
    y = sp.Symbol("y")
    rows = []
    for N in range(13):
        for family, roots in (
            ("integer", [(sp.Rational(2*r-1, 2))**2 for r in range(1, N+1)]),
            ("half_integer", [sp.Integer(r)**2 for r in range(1, N+1)]),
        ):
            poly = sp.Poly(sp.prod(1-root*y for root in roots), y)
            rows.append({
                "family": family, "N": N,
                "u": str(-sp.Integer(N) if family == "integer" else -sp.Integer(N)-sp.Rational(1,2)),
                "leading_power_of_x": 2*N-1 if family == "integer" else 2*N,
                "A_j_from_j_0_through_N_plus_3": [str(poly.nth(j)) for j in range(N+4)],
                "roots_in_squared_coordinate": [str(root) for root in roots],
                "minimal_subtraction_K": N+1,
                "subtracted_remainder": "0",
                "equation_label": "dr:eq:integer-product" if family == "integer" else "dr:eq:half-product",
            })
    data = {
        "schema_version": 1,
        "parameters": {"kappa": "1/2", "b": "1/2", "c": "1/2", "d0": "1"},
        "convention": "W_n(u) = x^leading_power_of_x * sum_j A_j*x^(-2*j), x=n+1/2",
        "warning": "These are special-point coefficients. Specializing before differentiating in u loses transverse jets.",
        "generation": "Exact products in SymPy; code/verify_exact.py independently compares the Bernoulli recurrence.",
        "rows": rows,
    }
    out = ROOT / "results" / "half_parameter_coefficients.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")

    specs = [
        ("dougall_sum", "dr:eq:dougall", "Classical normalized Rogers-Dougall summation", "kappa,b,c,d0>0; 0<Re(u)<d0", "classical_input", "dr:sec:family"),
        ("coefficient_recursion", "dr:eq:recursion", "Centered even-step Bernoulli coefficient recursion", "Formal coefficient identity; j>=1", "proved_continuation", "dr:lem:parity"),
        ("normal_subtraction", "dr:eq:subtraction", "Ordinary normally convergent Gamma-Hurwitz subtraction", "K>=1; -K<Re(u)<d0; fixed parameters satisfy the main domain", "proved_continuation", "dr:thm:subtraction"),
        ("residue_coefficient", "dr:eq:rho", "Polar-counterterm coefficient rho_N (twice the Gamma-product residue)", "N>=0 integer; fixed parameters satisfy the main domain", "proved_continuation", "dr:thm:coefficient-law"),
        ("coefficient_differential_law", "dr:eq:law", "Differential law responsible for all-resonance cancellation", "Polynomial identity; N>=0; D=partial_kappa+partial_b+partial_c", "proved_continuation", "dr:thm:coefficient-law"),
        ("collapsed_integral_resonance", "dr:eq:collapse", "Digamma collapse of the full minimal subtraction", "N>=0 integer; kappa,b,c,d0>0, including reciprocal-Gamma zeros", "proved_continuation", "dr:thm:collapse"),
        ("zero_safe_all_jet_germ", "dr:eq:jet-generator", "Holomorphic all-jet identity without division by rho_N", "Taylor germ t=0; N>=0; kappa,b,c,d0>0", "proved_continuation", "dr:thm:jets"),
        ("all_jet_coefficients", "dr:eq:all-jets", "Finite Stieltjes and negative-odd Hurwitz-zeta closure", "N,m>=0 integer; ordinary Taylor coefficients, not derivatives", "proved_continuation", "dr:thm:jets"),
        ("zero_excess_bell", "dr:eq:zero-jets", "All zero-excess spectral derivatives in Bell form", "m>=0 integer; kappa,b,c,d0>0", "derived_specialization", "dr:sec:jets"),
        ("half_integer_tower", "dr:eq:half", "Interlaced regular tower at nonpositive even zeta arguments", "N>=0; u=-N-1/2; kappa,b,c,d0>0", "proved_continuation", "dr:thm:half"),
        ("integer_symmetric_product", "dr:eq:integer-product", "Exact finite product at symmetric integer resonance", "kappa=b=c=1/2; N>=0; u=-N", "derived_specialization", "dr:sec:half"),
        ("half_integer_symmetric_product", "dr:eq:half-product", "Exact finite product at symmetric half-integer resonance", "kappa=b=c=1/2; N>=0; u=-N-1/2", "derived_specialization", "dr:sec:half"),
        ("integer_b_polynomial_locus", "dr:eq:integer-b", "Additional exact polynomial truncation locus", "N>=1; b=m in {1,...,N}; main parameter domain", "proved_continuation", "dr:prop:integer-b"),
        ("all_order_harmonic_identity", "dr:eq:general-harmonic", "Gamma-weighted generalized-harmonic identities", "m>=0; main parameter domain; Bell convention as in article", "derived_specialization", "dr:sec:harmonic"),
        ("harmonic_stieltjes_first", "dr:eq:harmonic-one", "First unweighted harmonic-Stieltjes identity", "n>=0 sum, H_0=0; gamma_m=gamma_m(1)", "derived_specialization", "dr:sec:harmonic"),
        ("harmonic_stieltjes_second", "dr:eq:harmonic-two", "Quadratic harmonic-Stieltjes identity", "n>=0 sum, H_0=0; A=gamma+2*log(2)", "derived_specialization", "dr:sec:harmonic"),
        ("first_resonance_harmonic", "dr:eq:first-resonance-harmonic", "Harmonic identity with zeta'(-1) and revived initial term 1/6", "n>=1 in displayed sum; initial 1/6 is essential", "derived_specialization", "dr:cor:first-resonance"),
        ("continuous_shift_harmonic", "dr:eq:S1-general", "Continuous-shift first harmonic identity", "a>0; S_1 defined by the ordinary bracketed convergent sum", "derived_specialization", "dr:thm:Sp"),
        ("all_harmonic_euler_endpoints", "dr:eq:Sp-general", "All higher harmonic endpoint values in single zeta derivatives and products", "a>0; integer p>=2; empty finite sums are zero", "derived_specialization", "dr:thm:Sp"),
        ("half_harmonic_euler_endpoints", "dr:eq:Sp-half", "Riemann-zeta-only specialization of all positive primitive orders", "integer p>=2; a=1/2; L=log(2)", "derived_specialization", "dr:thm:Sp"),
        ("endpoint_lifting", "dr:eq:endpoint", "Endpoint continuation with every spectral derivative", "K>=1; -K<Re(u)<d0; m>=0; closed unit disk", "proved_continuation", "dr:thm:endpoint"),
        ("polylog_root_filter", "dr:eq:root-filter", "Finite polylogarithm representation of rational-center counterterms", "1<=p<=q integer, kappa=p/q; initially 0<z<1, then consistent analytic continuation", "classical_filter_applied", "dr:sec:polylog"),
        ("polylog_root_filter_jets", "dr:eq:root-jets", "All spectral derivatives with required log(q) terms", "Root-filter domain; s=s0+2u; m>=0 integer", "derived_specialization", "dr:sec:polylog"),
        ("all_first_jet_primitive_endpoints", "dr:eq:all-primitive-endpoints", "Every normalized Euler primitive of the first symmetric harmonic jet", "kappa=b=c=1/2; r>=0 integer; endpoint z=1", "proved_continuation", "dr:sec:polylog"),
        ("negative_polygamma_ladder", "dr:eq:P-ladder", "Normalized Hurwitz-zeta primitive ladder", "x>0; j>=1 in second relation; P_j as defined in article", "classical_framework", "dr:sec:kappa-primitives"),
        ("all_center_parameter_primitives", "dr:eq:all-kappa-primitives", "Finite center-parameter antiderivative at every integer resonance", "b,c,N fixed; kappa varies with kappa,d0>0; additive constant arbitrary", "proved_continuation", "dr:thm:primitive"),
    ]
    text = (ROOT / "article.tex").read_text(encoding="utf-8")
    entries = []
    for ident, label, title, domain, provenance, proof in specs:
        entries.append({"id": ident, "title": title, "equation_label": label,
                        "proof_or_section_label": proof, "domain": domain,
                        "status": "proved_in_article_or_explicitly_credited_classical_input",
                        "provenance_class": provenance,
                        "latex_display": formula_for_label(text, label)})
    index = {"schema_version": 1, "source": "article.tex", "title": "Centered Dougall Resonance",
             "index_role": "Equation-level navigation for manuscript integration; not a proof-assistant certificate.",
             "global_priority": "not_established", "entries": entries}
    (ROOT / "identities.json").write_text(json.dumps(index, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {len(rows)} exact coefficient rows and {len(entries)} identity entries.")


if __name__ == "__main__":
    main()
