# Diophantine consistency through a common Pell index bound

This directory is a portable, Python-standard-library-only source and
equation bundle. It contains two explicit quartic polynomials over the
nonnegative integers. Their zeros encode finite C222 derivations of
contradiction and, by the inherited calibration and the supplied new
arithmetic proof, syntactic ZFC refutations.

| Endpoint | Variables | Quadratic residuals | Expanded quartic monomials | Coefficient height |
|---|---:|---:|---:|---:|
| Primary pooled-index equation | 261 | 194 | 31,679 | 85,566,955 |
| Sparse companion | 292 | 225 | 6,140 | 83,933,334 |
| Delivered Round14 baseline | 349 | 268 | 12,768 | 86,915,503 |

All equations are ordinary integer polynomials. There are no hidden
exponents, unbound program parameters, or undeclared semantic predicates
in the final equation files. `equation.txt` lists every quadratic
residual in plain text; `natural/equation.json` records the same data
exactly. The polynomial is the sum of their squares. Fully collected
coefficients are supplied in `natural/expanded_polynomial.json`.

The primary endpoint reduces the direct baseline's variable count by
88, or 25.2%, while increasing the monomial count. The sparse companion
improves variables, monomials and coefficient height simultaneously.
These are comparisons within the direct proof-certificate route. The
repository also contains much lower-variable equations at higher degree
or with large compiled coefficients; no global minimum is asserted.

## Mathematical change

One complete indexed-Pell certificate produces `V=Y_W(A)`. A single
aggregate bound makes every principal Pell ordinate smaller than `V`.
For the primary endpoint, one quadratic congruence

\[
\sum_i(Y_i-k_i)^2=(A-1)Q
\]

forces all the indices simultaneously: their decoded squared errors sum
to a nonnegative integer smaller than `A-1`, and the displayed row makes
that sum divisible by `A-1`. The coefficient `A-1` is a variable
modulus whose large size is proved from the retained scale certificate.
`CAP_THEOREM.md` supplies the soundness and constructive completeness
proofs, the exact cap certificate, and the required dependency order.

The primary endpoint also uses a radix sized by the actual CRT
representatives and the amplification budget `K=R`, supplied by the
independent arithmetic audit. Its horizon starts at 12. The sparse
companion keeps the prior radix and individual cap/residue rows, with
horizon 16.

## Reproduction

From this directory, with Python 3.10 or later:

```sh
python3 verify.py
python3 build.py --variant primary
python3 build.py --variant sparse
```

`verify.py` imports no producer module. It verifies the source hashes,
every nonnegative restoration certificate, every exact substitution,
and every expanded polynomial coefficient. `build.py` rebuilds the
arithmetic graph, emits the quartic, performs certified projection, and
requires exact equality with the frozen source, projected equation,
projection certificate, and expanded coefficients. Rebuilt files are
written under `rebuilt/` unless `--output` selects a different directory.
No network access or external repository is required.

`source/round14/` contains the exact dependency closure of the inherited
compiler, with its original relative layout. `source/custom/` contains
the new cap compiler and the self-sized-radix constructor. The only
packaging edits to imported source are documented local-path routing
changes. `SOURCE_MAP.json` records origins and SHA-256 hashes.

## Logical and verification scope

The finite artifact checks establish arithmetic syntax, domains,
elimination identities and polynomial coefficients. The unbounded
ordinary proof establishes their meaning; neither part alone replaces
the other. No newly completed Lean/Rocq certificate or literal
object-language ZFC derivation is claimed. The new proof is elementary
and formalizable in ZFC and composes with the retained ordinary C222
and CRT/Pell calibration proofs. It does not prove Con(ZFC), and it
does not assume either consistency or inconsistency.

Baseline review is pinned to ProveIt commit
`45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`, including the incoming
Round14 archive. The copied proof excerpts retain their original
statements and scope; they are not rewritten as new formal results.

This work and the new code were developed with AI assistance.
