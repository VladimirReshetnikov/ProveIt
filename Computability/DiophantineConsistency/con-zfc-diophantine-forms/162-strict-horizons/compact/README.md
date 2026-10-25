# A free quotient in the compact Pell encoding

Prepared with AI assistance for Vladimir Reshetnikov and ProveIt, 25 October 2026.

Two ordinary integer polynomials use ten strictly positive independent variables:

| Literal circuit | Binary operations | Exact degree |
|---|---:|---:|
| `equation_83_degree312.json` | 83 | 312 |
| `equation_89_degree278.json` | 89 | 278 |

The central step sets `Y=s` and moves `q` into the auxiliary Pell scale
`lambda=q`. The quotient coordinate `c=kY+eta` then has lower degree.
The denominator is restored only after the exponential projection. The
shift `T+alpha` has an explicit role in proving the early transport sign.

The ordinary proof, composed with the identified retained native/refutation
calibration, proves in ZFC that no strictly positive zero exists iff Con(ZFC).
This is not a consistency proof, a globally smallest-equation claim, or a
new end-to-end Lean/Rocq certificate.

All four fixed coefficient payloads and their finite reconstruction are retained.
There are no undecided coefficient parameters, variable exponents, or external
predicates in the actual polynomial. The coefficient tuple is the original
directly indexed BFS943 radix67 tuple, not a spliced or reinterpreted tuple.

## Verification

Python 3 standard library only; no network is used:

```
python3 -B build.py --check
python3 -B verify.py
python3 -B -O verify.py
python3 -B upstream_lucas/parent/rebuild_coefficients.py
```

The default checks are read-only. To save a verifier receipt use `--receipt PATH`.
The verifier imports no producer and checks every live gate through 28 exact
free-polynomial cuts, entire leading homogeneous forms, exact costs, fixed
numeral bytes and 20 deliberate gate corruptions.

`PROOF.md` supplies the full new ordinary proof, including all adverse signs
of the Lucas correction and the constructive positive converse.
`section.tex` is an article-ready account with complete formulas.
`upstream_lucas/` retains the identified compact parent and ordinary dependencies.
`SOURCE_LEDGER.json` fixes the inspected repository commit and source identities.

The new circuits improve specified operation/degree tradeoffs within the same
ten-positive domain. They do not supersede every other variable, degree,
coefficient-height, or domain tradeoff. New material uses the retained ProveIt
MIT No Attribution license; inherited licenses/notices remain in the source tree.
