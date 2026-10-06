#!/usr/bin/env python3
"""Reproducible exact checks and separately labeled marked-star diagnostics.

No third-party Python modules are imported. Output contains no clock readings,
platform paths, randomness, or host-specific metadata. Run with -O as well.
"""
import argparse
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True

from exact_checks import VerificationError, require, run_exact_checks
from symbolic_checks import run_symbolic_checks


def marked_star_exact(h, w):
    require(type(h) is int and type(w) is int and h >= 1 and w >= 1,
            "marked-star sum requires positive integer h,w")
    return 2*(h+1)**w + sum((h-m+3)*2**(h-m-1)*(m+1)**w
                             for m in range(1, h))


def critical_moments(t, maximum=7):
    L = math.log(2)
    values = [math.sqrt(math.pi/(2*L))*math.exp(t*t/(2*L))*math.erfc(t/math.sqrt(2*L))]
    values.append((1-t*values[0])/L)
    for j in range(1, maximum):
        values.append((j*values[j-1]-t*values[j])/L)
    return values


def critical_coefficients(t):
    L = math.log(2)
    moments = critical_moments(t)
    a = [t, L, -t/2, -L/3]
    b = [-L/2, t, L, -t/3, -L/4]
    aa = [0.0] * 7
    for i, u in enumerate(a):
        for j, v in enumerate(a):
            aa[i+j] += u*v/2
    integral = sum(3*u*moments[i] for i, u in enumerate(a))
    integral += sum(u*moments[i+1] for i, u in enumerate(b))
    integral += sum(u*moments[i+1] for i, u in enumerate(aa))
    g = moments[1]
    H = 4*moments[0]-moments[2]-t*moments[3]/6
    J_star = 29/12+integral
    return g, H, J_star, J_star+4*L*g


def marked_star_normalized(h, w):
    """Floating diagnostic for S(h,w)/h**w, never an algorithm for A(h,w)."""
    L = math.log(2)
    endpoint = 2*math.exp(w*math.log1p(1/h))
    summands = (math.exp(math.log(k+3)-L+k*L+w*math.log1p((1-k)/h))
                for k in range(1, h))
    return endpoint+math.fsum(summands)


def star_diagnostics(exact_result, extended):
    separate = []
    for row in exact_result["exact_rectangles"]:
        if row["h"] <= 4 and row["w"] <= 4:
            a = row["geometric_count"]
            s = marked_star_exact(row["h"], row["w"])
            separate.append({"h": row["h"], "w": row["w"], "true_kings_A": a,
                             "marked_star_S": s, "S_minus_A": s-a})
    require(any(row["S_minus_A"] for row in separate), "A and S must be distinct data series")
    critical = []
    for h in ((1000, 10000, 100000) if extended else (1000, 10000)):
        for target_t in (-1, 0, 1):
            w = math.floor(math.log(2)*h+target_t*math.sqrt(h))
            t = (w-math.log(2)*h)/math.sqrt(h)
            G, H, J_star, J_true = critical_coefficients(t)
            s = marked_star_normalized(h, w)
            residual = s-h*G-math.sqrt(h)*H-J_star
            require(math.isfinite(residual), "finite marked-star diagnostic")
            # Decimal strings make the approximate status visible. Last digits
            # can vary with the platform's libm; exact verification is separate.
            critical.append({"h": h, "w": w, "actual_t": format(t, ".10g"),
                             "S_over_h_power_w": format(s, ".10g"),
                             "J_star": format(J_star, ".10g"),
                             "J_true_A_formula_not_evaluated_A": format(J_true, ".10g"),
                             "S_residual_after_J_star": format(residual, ".8g")})
    return {"warning": "S is a marked-run proxy, not the true king count A; numerical residuals do not verify the asymptotic theorem or its error bounds",
            "small_exact_separation": separate,
            "critical_scalar_only": critical}


def guard_self_check():
    try:
        require(False, "intentional guard probe")
    except VerificationError:
        return "executable guards remain active with python -O"
    raise RuntimeError("correctness guard did not reject false input")


def run(extended=False, diagnostics=True):
    exact = run_exact_checks(extended)
    result = {"schema": "Report174.verification.v1", "mode": "extended" if extended else "default",
              "passed": True, "guard_self_check": guard_self_check(),
              "exact": exact, "symbolic": run_symbolic_checks(16 if extended else 12)}
    if diagnostics:
        result["marked_star_diagnostics"] = star_diagnostics(exact, extended)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--extended", action="store_true", help="larger, still bounded finite checks")
    parser.add_argument("--no-diagnostics", action="store_true", help="exact integer/rational checks only")
    parser.add_argument("--output", type=Path, help="create JSON file exclusively; default prints JSON")
    args = parser.parse_args()
    try:
        result = run(args.extended, not args.no_diagnostics)
        data = json.dumps(result, indent=2, sort_keys=True)+"\n"
        if args.output:
            with args.output.open("x", encoding="utf-8", newline="\n") as stream:
                stream.write(data)
        else:
            sys.stdout.write(data)
    except (VerificationError, ValueError, OSError, RuntimeError) as exc:
        print(f"verification failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
