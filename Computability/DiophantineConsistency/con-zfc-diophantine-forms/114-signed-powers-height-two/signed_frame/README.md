# Output-square-frame quartic checkpoints

This packet constructs two explicit ordinary polynomials over unrestricted integers. Their integer-zero existence is equivalent to that of the pinned 75-predicate direct C222 parent. The ordinary proofs in `PROOF.md` and the inherited source packet establish the requested ZFC-provable no-zero/Con(ZFC) equivalence. A new end-to-end theorem-prover proof object is not supplied.

| Profile | Integer variables | Quadratic rows | Degree | Collected terms | Coefficient height |
|---|---:|---:|---:|---:|---:|
| `support8` | 586 | 372 | 4 | 7,059 | 2,445,790,974,704 |
| `support16_affine2` | 591 | 377 | 4 | 5,835 | 964,213 |

These two checkpoints square the nine terminal outputs in the common frame while deleting the corresponding quotient-sign guards. They retain nine more variables than the sharper quotient-frame siblings, but have fewer collected monomials at the same coefficient heights. They are preserved as distinct variable/support tradeoffs. No optimum is claimed.

## Exact equation format

In each profile, `equation.json` fixes the ordered coordinates and every quadratic residual. The single polynomial is the sum of their squares. `polynomial.json` lists every collected coefficient of that same polynomial. A term `[c,[i,j,...]]` means the integer coefficient c times the indicated product of variables; `[]` means the constant monomial. Every variable ranges over Z. `projection.json` supplies the full sequence of monic integer substitutions and inverse recipes from `parent.json`.

The raw parent has 1,457 unrestricted integer variables and 1,243 quadratic rows. It differs from the old 75-predicate parent only by removing nine scalar guards (27 witnesses) and changing row1176 to

    W = 2 + sum(34 unsigned power atoms) + sum(9 terminal power outputs squared).

The square terms bound the absolute values of those outputs before their signs are known. The signed Pell residue lemma recovers their exact power meanings; Euclidean division then recovers the omitted quotient signs. The full ordinary argument appears in `PROOF.md`.

## Reproduction

Python 3 with its standard library is sufficient. No network or theorem prover is required.

```sh
python3 -B check_source.py
python3 -B -O check_source.py --output SOURCE_VERIFY_OPTIMIZED.json
python3 -B build.py --check
```

`check_source.py` imports no builder or optimizer. It authenticates all local frozen inputs; checks the complete new source/predicate boundary; reconstructs the early raw93 sign; checks 118 whole original-row identities; replays 546 sign steps and all 431 strict-positive constructor steps without the removed signs; and binds every exact range and high-digit division to the original coefficients. It confirms all unsigned atoms have the needed signs and all nine selected outputs have the stated square bounds.

The builder imports only the frozen standard-library monic-projection engine and checks every produced projection. `--check` compares every newly generated artifact byte for byte against the delivered version. The separately supplied independent verifier in the enclosing research package checks the signed inverse and every quartic coefficient without importing this optimizer.

`SOURCE_VERIFY.json`, `SOURCE_VERIFY_OPTIMIZED.json`, `FILTERED_PREFIX.json`, and `CENSUS.json` record the finite checks and exact measured sizes. These receipts verify finite algebra and interfaces; the unbounded mathematical statements are proved in `PROOF.md`.

## Provenance and logical calibration

`SOURCE_PINS.json` binds the local input bytes to repository commit `84e16e43092614bae262ca59651cb9d77e31a255`. The sibling quotient-frame packet's `provenance/INHERITED_SOURCE_MAP.json` maps the ordinary proof dependencies to their exact repository paths and SHA-256 digests. The inherited 407/888 ZIP is included intact; it contains the direct calculus, CRT and arithmetic compiler papers, literal source code, and immediate C222-to-ZF and ZF-to-ZFC bridge sources. Later source/domain refinements are included in that same sibling packet under `provenance/later_proofs/`.

Historical files under `source/` and in the inherited ZIP are preserved as source inputs; the supported new entry points are the two scripts listed above and the enclosing package's independent verifier. They do not require running historical source emitters.

The construction directly represents C222 proof certificates. It does not simulate K215 or instantiate a Jones universal polynomial. Some historical source modules import machine-related modules for their other theorems; no claim about a completely machine-free import graph is intended.

## Proof boundary

The nine deleted signs are recovered at the original arithmetic tuple. Changing between the new output-square frame and the old linear frame requires rebuilding private Pell/CRT witnesses. This is an equivalence of zero existence, not a bijection of full raw zero sets. The monic projections themselves do have exact integer polynomial inverses to their own raw parent.

The work does not prove Con(ZFC), claim that the equations have no solutions, or claim global minimality. It gives explicit smaller quartics and an ordinary proof of the equivalence that ZFC can formalize.
