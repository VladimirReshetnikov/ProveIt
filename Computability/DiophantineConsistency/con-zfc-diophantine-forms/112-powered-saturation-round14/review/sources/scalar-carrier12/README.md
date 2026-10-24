# Twelve integers with a scalar intersective carrier

This candidate **passes independent ordinary-proof and literal review**. Its two
complete literal equations use twelve unrestricted integer variables,
the authentic six source34 coefficients, and the following evaluators:

| Variant | Live operations | Exact degree |
|---|---:|---:|
| rational auxiliary norm | 145 =93 multiplications+26 additions+26 subtractions | 1200 |
| integral auxiliary norm | 141 =89 multiplications+26 additions+26 subtractions | 1456 |

The complete equations are the final outputs of `rational.json` and
`integral.json`, set equal to zero. Named registers are abbreviations,
not additional unknowns. The scalar carrier

    K=X(X+2ac)-1,
    Ac=[(HT+K)^2+3H^2][(HT+K)^3-19H^3],
    S=IH^5, Z=Sn-Ac

replaces the old quadratic-algebra main-root carrier. Four roots remain:
the strong, first, guard and auxiliary roots. The full proposed ordinary
existence proof is in `PROOF.md`. It establishes nonzero I, prime-order
separation and H|K before main-Pell folding and the signed whole-product
projection; completeness uses the same fixed strong witness and full
residue interpolation theorem as the parent. No sign or coprimality of
H and I is assumed. Main-root recovery uses the explicitly generalized
nonodd strong-rank argument, not a false odd-coordinate normalization.

The independent checker imports neither the producer nor an inherited
emitter. It binds every front-register formula by a separate free-ring
cut, covers all prefix arithmetic and verifies all495 coefficients of
the four-root norm against a separately expanded16-conjugate product.
It authenticates every coefficient byte and the complete frozen parent
dependency inventory. A graded-lex leading induction on the actual DAG
works at every gate over all six formal coefficient ports. It gives
exact positive coefficients

    [j^576 w^144 v^144 s^80 r^80 c^160 T^16] P_rat
       =2^1200*3^720*beta^576,
    [j^704 w^176 v^176 s^96 r^96 c^192 T^16] P_int
       =2^1424*3^880*beta^704.

Wrong projection constants, carrier factors and norm polarity are
actually evaluated and rejected. These are universal algebraic checks,
rather than evidence from sampled evaluations. Both normal and
optimized Python pass. Reproduce from the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/build_scalar_carrier12.py --check
python -B Computability/DiophantineConsistency/candidates/scalar-carrier12/check.py
python -B -O Computability/DiophantineConsistency/tools/build_scalar_carrier12.py --check
python -B -O Computability/DiophantineConsistency/candidates/scalar-carrier12/check.py
```

The independent review covers the whole solvability argument as well
as the literal checks; see `reviews/scalar-carrier12-peer.*` relative to
the research root. `MANIFEST.json` seals this complete packet. The native/refutation
calibration remains the named ordinary dependency of the frozen parent;
no new internal-ZFC or Lean endpoint is claimed. Lean remains paused,
and canonical PDF/TeX and all older candidates are unchanged.
