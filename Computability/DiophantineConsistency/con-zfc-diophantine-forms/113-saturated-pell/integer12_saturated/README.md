# Twelve unrestricted integers, 123 operations, degree 1084

`rational.json` is the primary equation. Its name describes the cleared
norm used in its derivation; the delivered equation is an ordinary
integer polynomial and its literal graph contains no division or radical.

The graph has twelve unrestricted integer unknowns and all six fixed
coefficients instantiated by the complete included payloads and finite
source34 recipe. Under the same ordinary native/compiler/refutation
calibration as the retained ProveIt parent, it has an integer zero exactly
when a finite syntactic ZFC refutation exists. The proof is in `PROOF.md`.
This is an ordinary arithmetic reduction, not a new Lean endpoint or an
independently encoded object-ZFC derivation of the entire calibration.

| Equation | Domain | Binary operations | Exact degree | Role |
|---|---|---:|---:|---|
| `rational.json` | Z^12 | 123 | 1084 | Primary candidate |
| `integral.json` | Z^12 | 123 | 1280 | Dominated companion and control |
| Retained parent rational | Z^12 | 145 | 1200 | Unchanged source |
| Retained parent integral | Z^12 | 141 | 1456 | Unchanged source |

The new idea at this interface is to replace the first and strong Pell
roots by the single product root

    sqrt(E*(1+Delta*U^2*E)),  U=s*r*c^2,

then use coprimality to split the square. The proof-only original strong
ordinate is `I=U*tau`, where `tau^2=E`. The auxiliary term must be
`4*U*E*T`, so that `T_old=tau*T` restores the original source equality.
The scalar carrier uses the quotient coordinate T and modulus U. The
full-residue interpolation theorem, applied with `N=s*tau`, is what makes
these choices simultaneously complete. The cubic Y scale, signed guards,
three-adic root separation, and scalar carrier from the parent remain.

To reproduce with only Python 3:

```sh
python3 -B build.py --check
python3 -B verify.py --output CHECKS.json
python3 -B -O verify.py --output CHECKS_OPTIMIZED.json
```

The independent verifier imports no candidate producer. It checks every
polynomial register, all 35 free coefficients of the eight-conjugate norm,
the source-restoration identities, exact cancellation and leading terms,
live operation counts, all fixed coefficient bytes, and the full finite
coefficient recipe. Five classes of corruptions are rejected for each
chart. The exact degree proof has a unique highest monomial, with
coefficient `2^1144*3^760*beta^624`, so it holds for the actual positive
fixed beta without relying on a numerical ray test.

`INHERITED_SOURCE_PINS.json` records all unchanged parent, proof, seed,
recipe, and coefficient files at ProveIt commit
`84e16e43092614bae262ca59651cb9d77e31a255`. `parent/PROOF.md` and its
complete cited local proof sources are retained verbatim. New files are
kept separate from the source. The stable centered twelve-integer packet
is a separate sibling and is not modified by this construction.
