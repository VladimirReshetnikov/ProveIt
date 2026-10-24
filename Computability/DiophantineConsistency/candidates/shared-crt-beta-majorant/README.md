# Shared CRT with its own beta-row majorant

This separate candidate uses `H=E(t,z,u)+F(t,z,u)`, removing the added
index from the factorial height. The literal beta row gives `H>=D^2>=1`,
where `D=1+(t+1)y`. The retained endpoint `y=M0+r0+2` gives `H>=t`
before any CRT interpretation. Full proof and dependency order are in
[PROOF.md](PROOF.md); the exact gate path is emitted by `majorant_audit.py`.

| Equation over nonnegative integers | Variables | Degree | Quadratic rows | Expanded monomials | Height |
|---|---:|---:|---:|---:|---:|
| `affine/equation.json` | **3,603** | **4** | 2,943 | 15,670 | 127,285,252 |
| `retained/equation.json` | **6,179** | **4** | 5,519 | 17,417 | 1,992 |

Each JSON equation supplies all variable names and all quadratic residuals.
Its single ordinary polynomial is the sum of their squares; the adjacent
`expanded_polynomial.json` gives the entire collected polynomial. Monomials
are sorted multisets of variable indices; the empty multiset denotes one.
No variable exponent, factorial, binomial, CRT product, or division symbol
remains in either polynomial. All source and arithmetic graph definitions
are fixed; no native tuple or coefficient blob is added.

The frozen prime-lift candidate and its integer companion are unchanged.
The new source differs from the original shared-certificates archive in
exactly two expressions. `SOURCE_PINS.json` binds the ZIP, all original
members, both changes, and the retained unbounded prime-lift proof.

From the repository root:

```sh
python3 -B Computability/DiophantineConsistency/tools/build_shared_crt_beta_majorant.py --check
python3 -B -O Computability/DiophantineConsistency/tools/build_shared_crt_beta_majorant.py --check
python3 -B Computability/DiophantineConsistency/candidates/shared-crt-beta-majorant/check.py
python3 -B -O Computability/DiophantineConsistency/candidates/shared-crt-beta-majorant/check.py
```

The checker verifies the exact source changes, actual beta-majorant gate
path and endpoint, complete quartic expansions and metrics, nonnegative
affine restoration, all 55 positive-power input licenses, and the exact
positive-power graph. The original arithmetic and calculus auditors are
retained unchanged. Normal and optimized receipts supplement the ordinary
unbounded proof; they do not replace it.

The ordinary C222/refutation equivalence and constructible-choice bridge
are inherited named dependencies. There is no new native calibration,
Lean build, or internally encoded object-ZFC derivation here. No absence
of solutions or consistency claim is decided by these computations.
