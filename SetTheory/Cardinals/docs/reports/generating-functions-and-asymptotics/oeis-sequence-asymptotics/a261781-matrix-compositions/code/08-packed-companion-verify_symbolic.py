#!/usr/bin/env python3
"""Optional exact rational-function identity check over Q(q,R), using SymPy.

No decimal evaluation, network, downloads, or installation is performed here.
No Python assert statements are used, so -O has the same checks.
"""
import argparse
import sys
from pathlib import Path
import packed_matrix as pm


def verify():
    try:
        import sympy as sp
        from sympy.polys.fields import field
        from sympy.polys.domains import QQ
    except ImportError as exc:
        raise RuntimeError("Optional dependency missing: install requirements-optional.txt to run this check") from exc
    F, q, R = field("q,R", QQ)
    derived = pm._morse_coefficients(q, R)
    frozen = pm._frozen_coefficients(q, R)
    matches = [left == right for left, right in zip(derived, frozen)]
    if len(matches) != 4 or not all(matches):
        raise ArithmeticError("An exact C0-C3 rational-function identity failed")
    t = 2*q
    stated_C1 = t/(48*(t-1)**3)*(2*R**2*t**4-9*R**2*t**3+12*R**2*t**2-5*R**2*t
               -6*R*t**3+6*R*t**2+12*R*t-12*R-2*t**3-3*t**2+24*t-24)
    if derived[0] != 1 or derived[1] != stated_C1:
        raise ArithmeticError("C0=1 or the independently stated C1 formula failed")
    return {"arithmetic": "exact rational-function field Q(q,R)",
            "method": "Morse substitution and Lagrange residue coefficient extraction",
            "identity_orders": list(range(4)), "all_frozen_identities_match": True,
            "C0_equals_one": True, "C1_matches_displayed_t_formula": True,
            "sympy_version": sp.__version__,
            "scope": "Symbolic coefficient identities only; not a proof of analytic error bounds"}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="optional new directory for symbolic_checks.json and manifest")
    args = parser.parse_args(argv)
    try:
        if args.output:
            target = Path(args.output)
            if target.exists() or target.is_symlink():
                raise FileExistsError("Output already exists; choose a new directory")
            if not target.parent.is_dir():
                raise FileNotFoundError("Output parent directory must exist")
        result = verify()
        if args.output:
            pm.write_bundle(args.output, {"symbolic_checks.json": result})
        print(pm.json_text(result), end="")
    except (RuntimeError, ValueError, TypeError, ArithmeticError, OSError) as exc:
        parser.error(str(exc))
    return 0


if __name__ == "__main__":
    sys.exit(main())
