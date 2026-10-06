#!/usr/bin/env python3
"""Replay exact Report147 checks and emit a deterministic rational JSON certificate."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys

import diagonal_euler as de
import fixtures as fx
import crossover

SOURCE_SHA256 = {
    "Report147.tex": "cb246370b1dcaa0b6ed92cab1f1cceed8464525520df095ef5d1dabd15bbf1cc",
}
PUBLIC_SOURCE_URLS = (
    "https://oeis.org/A252782",
    "https://oeis.org/A270917",
    "https://oeis.org/A144048",
)


class CertificateError(RuntimeError):
    """A mathematical expectation failed; active under python -O as well."""


def require(condition, message):
    if not condition:
        raise CertificateError(message)


def equal(actual, expected, message):
    if actual != expected:
        raise CertificateError(f"{message}: got {actual!r}, expected {expected!r}")


def encode_exact(value):
    """No floats or stringified rationals: JSON objects carry reduced integer pairs."""
    if type(value) is Fraction:
        return {"numerator": value.numerator, "denominator": value.denominator}
    if type(value) in (str, int, bool) or value is None:
        return value
    if type(value) in (list, tuple):
        return [encode_exact(item) for item in value]
    if type(value) is dict:
        if any(type(key) is not str for key in value):
            raise TypeError("JSON certificate keys must be strings")
        return {key: encode_exact(item) for key, item in value.items()}
    raise TypeError(f"non-exact certificate value: {type(value).__name__}")


def fixture_types():
    for prefix in (fx.PLUS_PREFIX, fx.MINUS_PREFIX):
        require(type(prefix) is tuple and all(type(n) is int for n in prefix),
                "sequence fixtures must contain typed integers")
    for f in fx.COMMON + fx.DIFFERENCE:
        require(type(f.residue) is int and type(f.profile_count) is int
                and type(f.degree_exclusive) is int, "integer fixture type")
        require(type(f.relative_floor) is Fraction and type(f.absolute_floor) is Fraction,
                "phase fixtures must be exact Fraction values")
        for atom in f.eligible_atoms:
            require(type(atom) is tuple and len(atom) == 2
                    and all(type(v) is int for v in atom), "atom fixture types")
        for term in f.terms:
            require(type(term.beta) is Fraction and type(term.coefficient) is Fraction
                    and type(term.falling_degree) is int, "term fixture types")


def sector_certificate(fixture, difference):
    r = fixture.residue
    result = de.enumerate_sectors(r, fixture.absolute_floor, odd_only=difference)
    equal(result.degree_exclusive, fixture.degree_exclusive, "exclusive degree bound")
    equal(tuple((a.j, a.k) for a in result.atoms), fixture.eligible_atoms, "eligible atom list")
    equal(len(result.profiles), fixture.profile_count, "qualifying profile count")
    expected = {(t.beta, t.falling_degree): t.coefficient for t in fixture.terms}
    terms = de.grouped_terms(result, difference=difference)
    equal(terms, expected, "all displayed phases and exact coefficients")
    equal(fixture.absolute_floor, fixture.relative_floor * de.LEADING_PHASE[r],
          "absolute/relative phase conversion")
    if not difference:
        equal(de.grouped_terms(result, -1), terms, "common signs agree")
        require(all(p.sign_exponent == 0 for p in result.profiles), "common profiles contain k>=2")
    else:
        require(all(p.sign_exponent % 2 == 1 for p in result.profiles), "difference profiles are odd")
        require(all(p.phase == fixture.absolute_floor for p in result.profiles),
                "unexpected larger sign-difference phase")
    d0 = result.degree_exclusive
    target = fixture.absolute_floor ** 6
    require(Fraction(9 ** r) * de.Q6 ** d0 < target, "degree endpoint must be strict")
    require(Fraction(9 ** r) * de.Q6 ** (d0 - 1) >= target, "degree bound must be minimal")
    B = target / 9 ** r
    profiles = []
    for p in result.profiles:
        equal(p.loss6, p.phase ** 6 / 9 ** r, "profile sixth-power identity")
        require(p.loss6 >= B and p.degree < d0 and p.degree % 3 == r, "invalid profile")
        profiles.append({
            "atoms": [{"j": a.j, "k": a.k, "multiplicity": b} for a, b in p.entries],
            "degree": p.degree, "falling_degree": p.ell,
            "absolute_phase": p.phase, "relative_phase": p.phase / de.LEADING_PHASE[r],
            "sign_exponent": p.sign_exponent, "unsigned_coefficient": p.coefficient,
            "plus_coefficient": p.signed_coefficient(1),
            "minus_coefficient": p.signed_coefficient(-1), "loss_sixth_power": p.loss6,
        })
    return {
        "residue": r, "relative_floor": fixture.relative_floor,
        "absolute_floor": fixture.absolute_floor, "odd_only": difference,
        "degree_exclusive": d0, "profile_count": len(result.profiles),
        "degree_bound_certificate": {
            "target_T_to_6": target, "at_D0": Fraction(9 ** r) * de.Q6 ** d0,
            "at_D0_minus_1": Fraction(9 ** r) * de.Q6 ** (d0 - 1),
            "atom_loss_floor": B,
        },
        "eligible_atoms": [{"j": a.j, "k": a.k, "degree": a.degree,
                            "loss_sixth_power": a.loss6} for a in result.atoms],
        "terms_A_over_Z": [{"relative_phase": beta, "falling_degree": ell,
                             "coefficient": c}
                            for (beta, ell), c in sorted(terms.items(), reverse=True)],
        "profiles": profiles,
    }


def check_relative_coefficients():
    for r, common in enumerate(fx.COMMON):
        terms = {(t.beta, t.falling_degree): t.coefficient for t in common.terms}
        for beta, relative in ((Fraction(8, 9), fx.FIRST_RELATIVE[r]),
                               (Fraction(64, 81), fx.SECOND_LADDER_RELATIVE[r])):
            c, shift, order = relative
            degree = order + (1 if r == 1 else 0)
            for m in range(1, 12):
                denominator = Fraction(3, 2) * m if r == 1 else Fraction(1)
                equal(terms[(beta, degree)] * de.falling(m, degree) / denominator,
                      c * de.falling(m - shift, order), "A/L relative common coefficient")
        term = fx.DIFFERENCE[r].terms[0]
        c, shift, order = fx.DIFFERENCE_RELATIVE[r]
        for m in range(1, 12):
            denominator = Fraction(3, 2) * m if r == 1 else Fraction(1)
            equal(term.coefficient * de.falling(m, term.falling_degree) / denominator,
                  c * de.falling(m - shift, order), "A/L first difference coefficient")


def inverse_algebra_certificate():
    equal(de.bernoulli_numbers(10), fx.BERNOULLI_PREFIX, "Bernoulli fixtures")
    equal(tuple(de.shifted_stirling_coefficient(r, 1) for r in range(3)), fx.G_FIRST,
          "shifted Stirling g_(r,1)")
    for m in range(1, 13):
        ratios = (de.leading_model(3 * m + 1) / de.leading_model(3 * m),
                  de.leading_model(3 * m + 2) / de.leading_model(3 * m + 1),
                  de.leading_model(3 * m + 3) / de.leading_model(3 * m + 2))
        expected = (2 * m * Fraction(64, 9) ** m,
                    Fraction(2, m) * Fraction(81, 8) ** m,
                    Fraction(27, 4 * (m + 1)) * Fraction(81, 8) ** m)
        equal(ratios, expected, "exact adjacent leading-model ratios")
    equal(Fraction(8, 9) ** 2, Fraction(64, 81), "inverse phase collision")
    return {
        "scope": "Exact algebraic ingredients only; no finite-threshold inverse or interval solver is supplied.",
        "bernoulli_B0_to_B10": de.bernoulli_numbers(10),
        "shifted_stirling_g_k1_to_k6": [
            {"residue": r, "coefficients": [de.shifted_stirling_coefficient(r, k)
                                             for k in range(1, 7)]} for r in range(3)],
        "adjacent_ratios_checked_m_inclusive": [1, 12],
        "phase_collision": {"factor": Fraction(8, 9), "square": Fraction(64, 81)},
    }


def build_certificate(max_n=24):
    de.integer(max_n, "max_n", 11)
    fixture_types()
    rows = []
    for epsilon, expected in ((1, fx.PLUS_PREFIX), (-1, fx.MINUS_PREFIX)):
        values = []
        for n in range(max_n + 1):
            # Compare full rows, not only diagonal entries: the exponent stays n.
            a = de.euler_row(n, n, epsilon)
            equal(de.direct_product_row(n, n, epsilon), a, f"direct product row n={n}, epsilon={epsilon}")
            equal(de.logarithmic_atom_row(n, n, epsilon), a, f"logarithmic atom row n={n}, epsilon={epsilon}")
            values.append(a[n])
        equal(tuple(values[:12]), expected, f"source prefix epsilon={epsilon}")
        for n in range(10):
            equal(de.profile_identity(n, epsilon), values[n], f"literal profile identity n={n}")
        rows.append({"epsilon": epsilon, "oeis": "A252782" if epsilon == 1 else "A270917",
                     "n_range_inclusive": [0, max_n], "values": values})
    check_relative_coefficients()
    onset = de.tail_onset_sixth_power(192)
    require(onset <= 1, "safe n=192 tail onset")
    require(de.Q6 ** 6 < Fraction(1, 2), "onset proof sixth-step inequality")
    # n^2*(8/9)^n decreases for n>=17 because n^2-16*n-8>0.
    equal(17 ** 2 - 16 * 17 - 8, 9, "onset monotonicity base")
    return {
        "schema": "report147-diagonal-euler-exact-v1", "status": "PASS",
        "arithmetic": "unbounded integers and reduced exact rationals; no floating point",
        "source_sha256": SOURCE_SHA256,
        "public_source_urls": PUBLIC_SOURCE_URLS,
        "scope": "Frozen forward-sector identities and exact inverse algebra; not a numerical proof of limits or operational integer-inverse onsets.",
        "coefficient_cross_checks": {
            "engines": ["Euler recurrence", "direct binomial product", "isolated-core logarithmic atom extraction"],
            "full_rows_checked": True, "literal_profile_identity_n_inclusive": [0, 9], "sequences": rows},
        "common_sectors": [sector_certificate(f, False) for f in fx.COMMON],
        "first_difference_sectors": [sector_certificate(f, True) for f in fx.DIFFERENCE],
        "uniform_tail_onset": {"safe_n": 192, "sixth_power_expression_at_safe_n": onset,
                               "required_upper_bound": 1, "monotonic_from_n": 17,
                               "monotonicity_polynomial_base": 9},
        "inverse_exact_algebra": inverse_algebra_certificate(),
        "crossover_exact_algebra": crossover.exact_crossover_certificate(),
    }


def dumps_certificate(max_n=24):
    return json.dumps(encode_exact(build_certificate(max_n)), indent=2, sort_keys=True) + "\n"


def validate_output_target(path):
    """Allow a new file only, beneath companion, with no symlinks or '..'."""
    if not isinstance(path, Path):
        raise TypeError("output path must be pathlib.Path")
    if ".." in path.parts:
        raise ValueError("--output must not contain '..' traversal")
    candidate = path if path.is_absolute() else Path.cwd() / path
    # Check the spelling before resolve(), which would erase symlink evidence.
    for component in (candidate, *candidate.parents):
        if component.is_symlink():
            raise ValueError("--output must not contain symlink components")
    root = Path(__file__).resolve().parent
    target = candidate.resolve()
    if not target.is_relative_to(root):
        raise ValueError("--output must remain inside the companion directory")
    if target.exists():
        raise FileExistsError("--output refuses to overwrite an existing path")
    if not target.parent.is_dir():
        raise ValueError("--output parent directory must already exist")
    return target


def cli(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=24,
                        help="compare all three engines on complete rows n=0..N (N>=11; default 24)")
    parser.add_argument("--output", type=Path,
                        help="write JSON inside this companion directory; otherwise use stdout")
    args = parser.parse_args(argv)
    try:
        if args.max_n < 11:
            parser.error("--max-n must be at least 11, so both frozen prefixes are checked")
        if args.output is not None:
            output = validate_output_target(args.output)
        payload = dumps_certificate(args.max_n)
        if args.output is None:
            sys.stdout.write(payload)
        else:
            # Exclusive creation also refuses a file/symlink created after validation.
            with output.open("x", encoding="utf-8") as stream:
                stream.write(payload)
    except (CertificateError, ValueError, TypeError, OSError) as exc:
        print(f"certificate failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(cli())
