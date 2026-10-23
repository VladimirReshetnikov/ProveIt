# Fourteen-integer Diophantine Con(ZFC) equation

Selected artifacts:

| Domain | Variables | Equations | Degree | Binary operations |
|---|---:|---:|---:|---:|
| unrestricted integers | 14 | 1 | 813056*5^32+2152 | 1586 |
| unrestricted integers | 15 | 1 | 406528*5^32+2528 | 1594 |

The lower-variable form is `signed14.json`; the lower-degree form is
`signed15_linear.json`. `SIGNED_FAMILY_PROOF.md` gives the full mathematical
proof, polynomial definitions, scope, and exact leading coefficients.
The reference17-integer package29 used20607 operations and degree
424296*5^33+53824. The new constructions combine package29's intersective
divisibility merger with the31-variable quartic and new optimized evaluator,
a linear-prefix Pell guard stack, smaller signed separation weights,
cofinal parity calibration, square canonical w, and signed Pell-index
reflection that releases the j guard.

The statements are equivalences provable in ZFC, not consistency proofs.
There is no new Lean/Rocq certificate and no global minimality claim.
Do not interpret either equation over another domain without a fresh proof.

## Reproduction

Python3.10+ standard library only:

    python3 build_signed_forms.py
    python3 check_signed_forms.py

These are newly authored programs. They read received mathematical data,
not execute received programs. The builder writes the two selected circuits
and ledger; the checker writes `SIGNED_CHECKS.json`. Run in a scratch copy if
checking an immutable release. The six `.lean.txt` files named in
`SOURCE_LEDGER.json` are inert source evidence, authenticated against their
Git blob hashes at commit8c6eec9d19ef80538c8e61ff6e0180040583446a.

The checker verifies240 signed source assignments per candidate across
three primes (6720 named register comparisons each),240 independent8×8
multiplication-matrix norm determinants per candidate,1400 guard-stack
checks, intersectivity through modulus500,46200 signed divisibility cases,
and60 additional actual-fixed-tuple norm checks. Exact leading coefficients
are also checked against all402 coefficient recipes and actual payloads at
three primes. Finite tests supplement, rather than replace, the proof.

## Coefficients

`SIGNED_BINDING.json` binds every source port together to the new whole tuple
in `../coefficients/payloads/COEFFICIENT_BINDING.json`; those raw files must
remain present. `INDEX_CONSTANTS.json` records the402 weighted coefficients,
with z=2^4259933. Aliases and literal folding reduce each circuit to80 live
nonliteral fixed leaves. No mixture with the previous T4 or Wang943 tuple is
allowed. The parent normalized quartic and index proof are shared with the
archive's nine-variable construction.

For the14-integer form, the live huge base-floor leaf is the exact integer
2^[1+4259934(5^32+1)], replacing the y leaf. It is a compact bounded recipe,
not a materialized binary string. The15-integer form uses the bounded finite
sum y=e_*(2z), also not materialized. Neither recipe hides an unspecified
recursively enumerable index or an existential choice of coefficients.

New text/code is AI-assisted mathematical work intended for incorporation
under the repository's MIT-0 terms; inherited source attribution and notices
are preserved by the enclosing archive. No independent human review is
represented by this package.
