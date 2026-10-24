# Quotient-frame quartics for Con(ZFC)

This packet constructs two explicit ordinary polynomials over unrestricted integers. Their integer-zero existence is equivalent to that of the pinned 75-predicate direct C222 parent. The ordinary proofs in `PROOF.md` and the inherited source packet establish the requested ZFC-provable no-zero/Con(ZFC) equivalence. A new end-to-end theorem-prover proof object is not supplied.

| Profile | Integer variables | Quadratic rows | Degree | Collected terms | Coefficient height |
|---|---:|---:|---:|---:|---:|
| `support8` | 577 | 363 | 4 | 7,326 | 2,445,790,974,704 |
| `support16_affine2` | 582 | 368 | 4 | 6,069 | 964,213 |

The matched source profiles have 604/609 variables and 9,676/8,823 terms, respectively, at the same heights. The new quotient frame removes nine nonnegativity certificates, saving all 27 of their integer witnesses. It omits the nine terminal power outputs from the frame, so their prior monic eliminations remain available. No optimum is claimed.

## Exact equation format

In each profile, `equation.json` fixes the ordered coordinates and every quadratic residual. The single polynomial is the sum of their squares. `polynomial.json` lists every collected coefficient of that same polynomial. A term `[c,[i,j,...]]` means the integer coefficient c times the indicated product of variables; `[]` means the constant monomial. Every variable ranges over Z. `projection.json` supplies the full sequence of monic integer substitutions and inverse recipes from `parent.json`.

The new raw parent retains all 1,259 original body coordinates and all 1,177 body rows except row 1176. It has 66 three-square predicates and therefore 1,457 variables and 1,243 rows before projection. `domain.json` names every retained predicate and every private witness position. The frame is

    W = 5 + sum(34 retained power atoms) + sum(9 omitted quotient coordinates squared).

The exact sets are literal in `domain.json`, `build.py`, and `check_source.py`. Terminal power outputs are bounded indirectly by their division equations. The five-unit margin gives sufficient exponent budget for the signed Pell residue argument. It does not impose an exponentiation operation in the final polynomial: all displayed equations are ordinary quadratic residuals and a quartic sum of squares.

## Reproduction

Python 3 with its standard library is sufficient. No network or theorem prover is required.

```sh
python3 -B check_source.py
python3 -B -O check_source.py --output SOURCE_VERIFY_OPTIMIZED.json
python3 -B build.py --check
```

`check_source.py` imports no builder or optimizer. It authenticates all local frozen inputs; checks the complete new source/predicate boundary; reconstructs the early raw93 sign; checks 118 whole original-row identities; replays 546 sign steps and all 431 strict-positive constructor steps without the removed signs; and binds every exact range and high-digit division to the original coefficients. It confirms all 34 retained atoms have the needed signs and all selected exponents have the stated frame margin.

The builder imports only the frozen standard-library monic-projection engine and checks every produced projection. `--check` compares every newly generated artifact byte for byte against the delivered version. The separately supplied independent verifier in the enclosing research package checks the signed inverse and every quartic coefficient without importing this optimizer.

`SOURCE_VERIFY.json`, `SOURCE_VERIFY_OPTIMIZED.json`, `FILTERED_PREFIX.json`, and `CENSUS.json` record the finite checks and exact measured sizes. These receipts verify finite algebra and interfaces; the unbounded mathematical statements are proved in `PROOF.md`.

## Provenance and logical calibration

`SOURCE_PINS.json` binds the local input bytes to repository commit `84e16e43092614bae262ca59651cb9d77e31a255`. `provenance/INHERITED_SOURCE_MAP.json` maps the ordinary proof dependencies to their exact repository paths and SHA-256 digests. The inherited 407/888 ZIP is included intact; it contains the direct calculus, CRT and arithmetic compiler papers, literal source code, and immediate C222-to-ZF and ZF-to-ZFC bridge sources. Later source/domain refinements are included under `provenance/later_proofs/`.

Historical files under `source/` and in the inherited ZIP are preserved as source inputs; the supported new entry points are the two scripts listed above and the enclosing package's independent verifier. They do not require running historical source emitters.

The construction directly represents C222 proof certificates. It does not simulate K215 or instantiate a Jones universal polynomial. Some historical source modules import machine-related modules for their other theorems; no claim about a completely machine-free import graph is intended.

## Proof boundary

The nine deleted signs are recovered at the original arithmetic tuple. Changing between the new quotient frame and the old linear frame requires rebuilding private Pell/CRT witnesses. This is an equivalence of zero existence, not a bijection of full raw zero sets. The monic projections themselves do have exact integer polynomial inverses to their own raw parent.

The work does not prove Con(ZFC), claim that the equations have no solutions, or claim global minimality. It gives explicit smaller quartics and an ordinary proof of the equivalence that ZFC can formalize.
