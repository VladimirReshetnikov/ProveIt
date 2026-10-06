#!/usr/bin/env python3
"""Report171: bounded exact verification and explicitly non-certified diagnostics.

All validation is active under python -O. No network access and no import-time work.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from math import comb
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
FIXTURES = ROOT / "fixtures"
MAX_N = 1000
MAX_LAGRANGE = 81
CASES = {"general": (16, 4, 4), "quartic": (27, 6, 3)}
NOTICE = ("High-precision floating-point diagnostic only; not interval certification, "
          "not a certified finite-index error bound, and not an exact-ceiling rule.")


class ValidationError(ValueError):
    """A mathematical, fixture, or bounded-input check failed."""


def require(condition, message):
    if not condition:
        raise ValidationError(message)


def bounded(value, low, high, name):
    require(type(value) is int and low <= value <= high,
            f"{name} must be an integer in [{low}, {high}]")
    return value


def exact_div(numerator, denominator, context):
    require(type(numerator) is int and type(denominator) is int and denominator != 0,
            f"{context}: invalid integer division")
    quotient, remainder = divmod(numerator, denominator)
    require(remainder == 0, f"{context}: nonzero divisibility remainder {remainder}")
    return quotient


def conv(a, b, degree):
    result = [0] * (degree + 1)
    for i, ai in enumerate(a[:degree + 1]):
        if ai == 0:
            continue
        for j, bj in enumerate(b[:degree + 1 - i]):
            result[i + j] += ai * bj
    return result


def json_bytes(data):
    return (json.dumps(data, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def write_new(path, data):
    """Exclusive creation: an existing file, directory or symlink is never replaced."""
    path = Path(path)
    with path.open("xb") as stream:
        stream.write(data)


def check_fixtures(directory=FIXTURES):
    directory = Path(directory)
    expected = {"oeis_prefixes.json", "eulerian_coefficients.json",
                "local_sector_coefficients.json", "provenance.json"}
    manifest = json.loads((directory / "SHA256.json").read_text())
    require(set(manifest) == expected, "fixture manifest has unexpected membership")
    for name in sorted(expected):
        content = (directory / name).read_bytes()
        require(hashlib.sha256(content).hexdigest() == manifest[name],
                f"fixture SHA-256 mismatch: {name}")
    return manifest


def inverse_ode(case, max_m):
    """Integer inverse coefficients from R(cR-1)R'' = d*t*(R')^3."""
    require(case in CASES, "unknown case")
    bounded(max_m, 1, MAX_N + 2, "max_m")
    c, d, _ = CASES[case]
    r = [0] * (max_m + 1)
    r[1] = 1
    r2, p2 = [0] * (max_m + 1), [1] + [0] * max_m
    for n in range(2, max_m + 1):
        j = n - 1
        r2[j] = sum(r[i] * r[j - i] for i in range(1, j))
        j = n - 2
        p2[j] = sum((i + 1) * r[i + 1] * (j - i + 1) * r[j - i + 1]
                    for i in range(j + 1))
        rr = sum(r[i] * (n + 1 - i) * (n - i) * r[n + 1 - i]
                 for i in range(2, n))
        rrr = sum(r2[i] * (n + 1 - i) * (n - i) * r[n + 1 - i]
                  for i in range(2, n))
        ppp = sum((i + 1) * r[i + 1] * p2[n - 2 - i] for i in range(n - 1))
        r[n] = exact_div(c * rrr - rr - d * ppp, n * (n - 1), f"r_{n}")
    return r


def inverse_lagrange(case, max_m):
    """Independent generalized-binomial powers, never using the ODE recurrence."""
    require(case in CASES, "unknown case")
    bounded(max_m, 1, MAX_LAGRANGE, "Lagrange max_m")
    B = [0]
    for j in range(1, max_m):
        numerator = comb(2 * j, j) * (comb(2 * j, j) if case == "general" else comb(3 * j, j))
        B.append(exact_div(numerator, j + 1, "Omega/r coefficient"))
    powers = [[1] + [0] * (max_m - 1)]
    for _ in range(1, max_m):
        powers.append(conv(powers[-1], B, max_m - 1))
    r = [0]
    for m in range(1, max_m + 1):
        numerator = sum((-1) ** k * comb(m + k - 1, k) * powers[k][m - 1]
                        for k in range(m))
        r.append(exact_div(numerator, m, "Lagrange extraction"))
    return r


def check_ode_residual(case, r):
    """Full convolution residual formed separately from coefficient generation."""
    require(case in CASES and len(r) >= 3, "invalid residual input")
    require(r[:2] == [0, 1], "invalid inverse initial values")
    c, d, _ = CASES[case]
    M = len(r) - 1
    rp = [(j + 1) * r[j + 1] for j in range(M)]
    rpp = [(j + 2) * (j + 1) * r[j + 2] for j in range(M - 1)]
    r2 = conv(r, r, M - 1)
    lhs = conv([c * r2[j] - r[j] for j in range(M)], rpp, M - 1)
    rhs = conv(conv(rp, rp, M - 2), rp, M - 2)
    for j, value in enumerate(lhs):
        require(value == (d * rhs[j - 1] if j else 0), f"ODE residual at t^{j}")
    return M - 1


def check_oeis(general, quartic, directory=FIXTURES):
    fixtures = json.loads((Path(directory) / "oeis_prefixes.json").read_text())
    generated = {"A324312": general, "A324314": quartic,
                 "A277493": [1] + [2 * value for value in general]}
    checked = {}
    for name, record in fixtures["sequences"].items():
        want = list(map(int, record["terms"]))
        count = min(len(want), len(generated[name]))
        require(generated[name][:count] == want[:count], f"OEIS fixture mismatch: {name}")
        checked[name] = count
    return checked


def exact_results(n=1000, lagrange_m=81, fixture_dir=FIXTURES):
    bounded(n, 1, MAX_N, "n")
    bounded(lagrange_m, 1, MAX_LAGRANGE, "lagrange_m")
    hashes = check_fixtures(fixture_dir)
    result = {"schema": "Report171-exact-v1", "n_max": n, "fixtures_sha256": hashes,
              "description": "Exact integer counts; m=n+2. Sequence integers are decimal strings.",
              "cases": {}}
    all_counts = {}
    for name, (_, _, den) in CASES.items():
        r = inverse_ode(name, n + 2)
        counts = [exact_div(-r[j + 2], den, "count normalization") for j in range(1, n + 1)]
        require(all(value > 0 for value in counts), "nonpositive count")
        upto = min(lagrange_m, n + 2)
        independent = inverse_lagrange(name, upto)
        require(r[:upto + 1] == independent, f"independent Lagrange mismatch: {name}")
        all_counts[name] = counts
        result["cases"][name] = {
            "oeis_id": "A324312" if name == "general" else "A324314", "offset": 1,
            "counts": list(map(str, counts)), "inverse_r": list(map(str, r)),
            "lagrange_checked_through_m": upto,
            "ode_residual_zero_through_t_power": check_ode_residual(name, r)}
    result["oeis_prefix_terms_checked"] = check_oeis(all_counts["general"], all_counts["quartic"], fixture_dir)
    result["A277493"] = {"offset": 0, "counts": ["1"] + [str(2 * v) for v in all_counts["general"]],
                          "identity": "A277493(n)=2*A324312(n) for n>0"}
    return result


def symbolic_results(fixture_dir=FIXTURES):
    """Q through independent F inversion; U through direct equation substitution."""
    check_fixtures(fixture_dir)
    import sympy as s
    x, t, T, v = s.symbols("x t T v")
    degree = 6

    def series_log_one(p, N):
        require(p[0] == 1, "formal logarithm requires constant 1")
        a = list(p) + [0] * max(0, N + 1 - len(p))
        a[0] = 0
        power, out = [1] + [0] * N, [0] * (N + 1)
        for j in range(1, N + 1):
            power = conv(power, a, N)
            out = [s.expand(out[k] + s.Rational((-1) ** (j + 1), j) * power[k]) for k in range(N + 1)]
        return out

    def reciprocal(p, N):
        require(p[0] == 1, "formal reciprocal requires constant 1")
        out = [s.Integer(1)]
        for j in range(1, N + 1):
            out.append(s.expand(-sum(p[k] * out[j - k] for k in range(1, min(j + 1, len(p))))))
        return out

    # F=f/x obeys 1/F + x log F = 1 + x*t. At order k the new F_k has coefficient -1.
    F = [s.Integer(1)]
    for k in range(1, degree + 1):
        rec, log = reciprocal(F, k), series_log_one(F, k - 1)
        F.append(s.expand(rec[k] + log[k - 1] - (t if k == 1 else 0)))
    require(all(s.expand(reciprocal(F, degree)[k] + (series_log_one(F, degree)[k - 1] if k else 0)
                         - (1 if k == 0 else t if k == 1 else 0)) == 0 for k in range(degree + 1)),
            "formal F inversion residual")
    ell = [0, -s.EulerGamma] + [-s.zeta(k) / k for k in range(2, degree + 1)]
    exponential = [s.Integer(1)]
    for k in range(1, degree):
        exponential.append(s.expand(sum(j * ell[j] * exponential[k - j] for j in range(1, k + 1)) / k))
    gamma = [0] + [s.expand(exponential[k - 1] + (exponential[k - 2] if k >= 2 else 0))
                   for k in range(1, degree + 1)]
    derivative, H = sum(F[k] * x ** (k + 1) for k in range(len(F))), 0
    for k in range(1, degree + 1):
        derivative = s.expand(-x * x * s.diff(derivative, x) + x * s.diff(derivative, t))
        H += (-1) ** k * gamma[k] * derivative
    Q = {str(j): s.simplify(s.expand(H).coeff(x, j + 2).subs(t, T - s.EulerGamma)) for j in range(6)}
    claimed = json.loads((Path(fixture_dir) / "eulerian_coefficients.json").read_text())
    for j, value in Q.items():
        require(s.expand(value - s.sympify(claimed["Q"][j], locals={"T": T})) == 0, f"Q{j} fixture mismatch")
    sectors = json.loads((Path(fixture_dir) / "local_sector_coefficients.json").read_text())
    sector_out = {}
    for name, a in [("general", s.Rational(1, 2)), ("quartic", s.Rational(1, 3))]:
        U = [s.sympify(text, locals={"v": v}) for text in sectors[name]["U"]]
        require(len(U) == 4 and U[0] == 1 / v, "invalid U fixture shape")
        # u = xi*sum U_j xi^j; v*u/xi has constant 1.
        logcor = series_log_one([s.cancel(v * p) for p in U], 3)
        residual = [0] * 5
        u, power = [0] + U, [1, 0, 0, 0, 0]
        deltas = []
        for j in range(1, 5):
            power = conv(power, u, 4)
            delta = (2 * s.harmonic(j - 1) - sum(1 / (a + k) + 1 / (1 - a + k) for k in range(j - 1))
                     + s.Rational(1, j) - 1)
            deltas.append(delta)
            aj = s.rf(a, j - 1) * s.rf(1 - a, j - 1) / s.factorial(j - 1) ** 2
            term = conv(power, [v + delta] + [-q for q in logcor[1:]], 4)
            residual = [residual[k] + aj * term[k] / j for k in range(5)]
        residual[1] -= 1
        for j in range(1, 5):
            require(s.cancel(residual[j]) == 0, f"{name} U residual at xi^{j}")
        require([str(q) for q in deltas] == sectors[name]["deltas"], f"{name} delta mismatch")
        for value in U:
            denominator = s.denom(s.cancel(value))
            _, factors = s.factor_list(denominator, v)
            require(all(s.degree(p, v) == 1 and s.solve(p, v)[0] in [0, 1] for p, _ in factors),
                    f"unexpected U pole: {name}")
        sector_out[name] = {"U": list(map(str, U)), "deltas": list(map(str, deltas)),
                            "substitution_zero_through_xi_power": 4, "finite_poles_subset": [0, 1]}
    E1, E2 = Q["1"], s.expand(Q["2"] - Q["1"] ** 2 / 2)
    require(s.expand(E2 - (T ** 2 - 5 * T + s.Rational(3, 2) - s.pi ** 2 / 2)) == 0,
            "inverse E2 mismatch")
    return {"schema": "Report171-symbolic-v1", "arithmetic": "exact SymPy expressions",
            "Q": {k: str(q) for k, q in Q.items()}, "Q_fixture_equal": True,
            "gamma_coefficients": list(map(str, gamma)), "sectors": sector_out,
            "inverse_log_coefficients": {"E1": str(E1), "E2": str(E2)}}


def numeric_parameters(case, mp):
    require(case in CASES, "unknown numerical case")
    if case == "general":
        return 4 * mp.pi, 1 + mp.log(4), -mp.mpf(5) / 2, mp.mpf(1) / 16
    return 4 * mp.sqrt(3) * mp.pi, 1 + mp.log(6), -mp.mpf(3), mp.mpf(1) / 18


def lambert_coefficients(C, delta, M, mp):
    bounded(M, 3, MAX_N + 2, "Lambert M")
    v0 = mp.findroot(lambda v: v - mp.log(v) - C, (C + 1, C + 3))
    require(mp.isfinite(v0) and v0 > 1, "wrong Lambert germ")
    h = [1 / v0, -1 / (v0 - 1)]
    p, p2 = [h[1]], [h[1] ** 2]
    for n in range(M):
        p3n = mp.fsum(p[i] * p2[n - i] for i in range(n + 1))
        other = mp.fsum(h[i] * (n - i + 2) * (n - i + 1) * h[n - i + 2] for i in range(1, n + 1))
        hn = (-p3n - other) / (h[0] * (n + 2) * (n + 1))
        h.append(hn)
        p.append((n + 2) * hn)
        p2.append(mp.fsum(p[i] * p[n + 1 - i] for i in range(n + 2)))
    h2 = [mp.fsum(h[i] * h[n - i] for i in range(n + 1)) for n in range(M + 1)]
    k = [h2[n] - (delta + 1) * mp.fsum(h2[i] * p[n - i] for i in range(n + 1)) for n in range(M + 1)]
    return v0, h, k


def lambert_lagrange(v0, N, mp):
    bounded(N, 1, 60, "Lambert Lagrange prefix")
    h0, scale = 1 / v0, (v0 - 1) / v0
    B = [mp.mpf(0)] + [1 / (j * (j + 1) * (v0 - 1)) for j in range(1, N)]
    powers = [[mp.mpf(1)] + [mp.mpf(0)] * (N - 1)]
    for _ in range(1, N):
        prev = powers[-1]
        powers.append([mp.fsum(prev[i] * B[n - i] for i in range(n + 1)) for n in range(N)])
    h = [h0]
    for m in range(1, N + 1):
        numerator = mp.fsum((-1) ** j * comb(m + j - 1, j) * powers[j][m - 1] for j in range(m))
        h.append(-h0 * numerator / (m * scale ** m))
    return h


def diagnostic_results(n=1000, digits=110, prefix=60):
    bounded(n, 1, MAX_N, "n")
    bounded(digits, 50, 200, "digits")
    bounded(prefix, 1, 60, "prefix")
    check_fixtures()
    import mpmath as mp
    out = {"schema": "Report171-diagnostic-v1", "notice": NOTICE, "decimal_precision": digits, "cases": {}}
    with mp.workdps(digits):
        for case, (_, _, den) in CASES.items():
            mu, C, delta, kappa = numeric_parameters(case, mp)
            r = inverse_ode(case, n + 2)
            v0, h, k = lambert_coefficients(C, delta, n + 2, mp)
            upto = min(prefix, n + 2)
            other = lambert_lagrange(v0, upto, mp)
            discrepancy = max(abs(other[j] / h[j] - 1) for j in range(upto + 1))
            tolerance = mp.power(10, -(digits // 2))
            require(discrepancy < tolerance, f"Lambert independent-prefix mismatch: {case}")
            rows = []
            for index in sorted(set([p for p in [20, 50, 100, 200, 500, 1000] if p <= n] + [n])):
                m = index + 2
                exact = mp.mpf(exact_div(-r[m], den, "diagnostic exact count"))
                L, T = mp.log(m), mp.log(mp.log(m)) + C + mp.euler
                base = kappa * mu ** m / (m * m * L * L)
                values = {"leading": base,
                          "log1": base * (1 + (3 - 2 * T) / L),
                          "log2": base * (1 + (3 - 2 * T) / L + (3*T*T - 11*T + 6 - mp.pi**2/2) / L**2),
                          "model0": kappa * mu ** m * h[m],
                          "model01": kappa * mu ** m * (h[m] - k[m] / 2)}
                rows.append({"n": index, "relative_errors": {key: mp.nstr(value / exact - 1, 40) for key, value in values.items()},
                             "scaled_model01_residual": mp.nstr((values["model01"] / exact - 1) * m*m*L, 40)})
            out["cases"][case] = {"v0": mp.nstr(v0, 40), "lagrange_checked_through_m": upto,
                                  "max_relative_prefix_discrepancy": mp.nstr(discrepancy, 12),
                                  "prefix_check_tolerance": mp.nstr(tolerance, 12), "rows": rows}
    return out


def inverse_results(sequence, log_y, digits=80):
    bounded(digits, 50, 200, "digits")
    require(sequence in ["A277493", "A324312", "A324314"], "unknown sequence")
    require(isinstance(log_y, str) and len(log_y) <= 100, "log_y must be a decimal string of at most 100 characters")
    import mpmath as mp
    with mp.workdps(digits):
        target = mp.mpf(log_y)
        require(mp.isfinite(target) and 10 <= target <= 10**9, "log_y must be finite and in [10, 1e9]")
        mu, C, _, kappa = numeric_parameters("quartic" if sequence == "A324314" else "general", mp)
        if sequence == "A277493":
            kappa *= 2
        b = mp.log(mu)
        q = (target - mp.log(kappa)) / b
        L, T = mp.log(q), mp.log(mp.log(q)) + C + mp.euler
        x0 = q - 2 + 2 / b * (mp.log(q) + mp.log(mp.log(q)))
        x1 = x0 + (2 * T - 3) / (b * L)
        x2 = x1 + (-T*T + 5*T - mp.mpf(3)/2 + mp.pi**2/2) / (b * L**2)
        return {"schema": "Report171-inverse-v1", "notice": NOTICE,
                "sequence": sequence, "log_y": log_y, "decimal_precision": digits,
                "q": mp.nstr(q, 40), "x0": mp.nstr(x0, 40), "x1": mp.nstr(x1, 40), "x2": mp.nstr(x2, 40),
                "interpretation": "Smooth asymptotic charts only. Constants and starting indices in the rounding sandwich are not explicitly evaluated or certified here; no integer threshold is returned."}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ["exact", "symbolic", "diagnostics", "inverse", "verify"]:
        p = commands.add_parser(name)
        p.add_argument("--output", type=Path, help="new JSON file; existing paths are never overwritten (default stdout)")
        if name in ["exact", "diagnostics", "verify"]:
            p.add_argument("--n", type=int, default=1000, help="maximum count index, 1..1000")
        if name in ["exact", "verify"]:
            p.add_argument("--lagrange-m", type=int, default=81, help="independent exact inverse prefix, 1..81")
        if name in ["diagnostics", "inverse"]:
            p.add_argument("--digits", type=int, default=110, help="decimal precision, 50..200")
        if name == "diagnostics":
            p.add_argument("--prefix", type=int, default=60, help="independent numerical prefix, 1..60")
        if name == "inverse":
            p.add_argument("--sequence", choices=["A277493", "A324312", "A324314"], required=True)
            p.add_argument("--log-y", required=True, help="natural logarithm of target y, 10..1e9")
    args = parser.parse_args(argv)
    try:
        # Refuse before expensive work; exclusive creation below also prevents races.
        if args.output is not None and (args.output.exists() or args.output.is_symlink()):
            raise FileExistsError(f"refusing existing output: {args.output}")
        if args.command == "exact":
            result = exact_results(args.n, args.lagrange_m)
        elif args.command == "symbolic":
            result = symbolic_results()
        elif args.command == "diagnostics":
            result = diagnostic_results(args.n, args.digits, args.prefix)
        elif args.command == "inverse":
            result = inverse_results(args.sequence, args.log_y, args.digits)
        else:
            exact = exact_results(args.n, args.lagrange_m)
            symbolic = symbolic_results()
            result = {"schema": "Report171-verification-v1", "exact_n_max": exact["n_max"],
                      "oeis_prefix_terms_checked": exact["oeis_prefix_terms_checked"],
                      "Q_fixture_equal": symbolic["Q_fixture_equal"],
                      "local_substitution_checked_through_xi_power": 4, "status": "passed"}
        if args.output:
            write_new(args.output, json_bytes(result))
        else:
            sys.stdout.buffer.write(json_bytes(result))
        return 0
    except (ValueError, OSError, KeyError, TypeError, ImportError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
