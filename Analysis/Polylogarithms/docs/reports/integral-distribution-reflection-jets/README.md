# Integral Cyclotomic Distribution Relations

**Reflection torsion, modular rank loci, contact-order Smith laws, and exact spectral-jet identities**  
Research continuation for ProveIt, 9 October 2026.

## Start here

The complete article is `article/article.pdf`; its LaTeX source is `article/article.tex` with eight section files and a bibliography. It contains full proofs, not just experimental rank tables.

The inspected repository snapshot is `aeafd6e9b843b589a3bf66850d15bf8ad0e196dd`. This delivery does not change the repository. A proposed companion-report destination is:

`Analysis/Polylogarithms/docs/reports/integral-distribution-reflection/`

## Main results

The module has generators `e_x` for `x in (1/q) Z/Z` and relations

`sum_{p*y=x} e_y - A_p e_x`, for each prime divisor `p` and `x in X_(q/p)`.

* It has an explicit raw-point basis over `Z[A_p]` of cardinality `phi(q)`, valid under every commutative-ring specialization. A selected maximal raw-relation minor is exactly 1.
* For integer weights and `q > 2`, both reflection coinvariants are `Z^n` plus either no torsion or `(Z/2)^h`, where `n=phi(q)/2`, `r=#odd prime divisors + [4 divides q]`, and `h=2^(r-1)`. Torsion occurs exactly when every odd-prime weight is odd.
* In characteristic two the reflection homology is the direct sum of the homology groups of the Koszul complex on `A_p-1` for odd primes, with `A_2(A_2-1)` added when `4 | q`. The universal homology is the cyclic module cut out by that active ideal.
* Along a characteristic-two power-series specialization, let `d` be the least valuation of the active scalars. The reflection Smith diagonal has `n-h` units, `h` entries `t^d`, and `n` zeros when `d` is finite. Its length-`L` cokernel dimension is `n L + h min(d,L)`. The article covers `d=0`, `d=infinity`, and `q=1,2` separately.
* Three polynomial certificates, using respectively 3, 4, and 5 prime rows, prove all-order cyclotomic identities. The level-15 identity yields a Stieltjes/polylogarithm derivative family for every nonnegative derivative order.

The formulas retain the formal endpoint generator `e_0`. Quotienting by an
additional endpoint relation is a different reflection presentation and must
not be assigned these torsion formulas without further analysis.

These are statements about a specified formal presentation and exact analytic identities. They are not claims of numerical independence of periods. Ordinary distribution freeness and ordinary sign cohomology have classical antecedents in Kubert, Anderson, and Ouyang; the article explicitly acknowledges them. No exhaustive global priority claim is made. The manuscript's S6 conjecture is not proved here.

## Replay without extra Python packages

Python 3.10 or later is sufficient for the exact core:

```sh
python code/verify_certificates.py
python code/test_exact.py
```

The certificate verifier reconstructs raw prime fibers and does not call the normal-form algorithm or generator. It also rejects a deliberately corrupted certificate. The frozen JSON is not regenerated as a prerequisite to replay.

To regenerate that JSON explicitly:

```sh
python code/generate_certificates.py
```

## Optional independent checks

```sh
python -m pip install -r requirements-optional.txt
python code/test_smith.py
python code/numerical_diagnostics.py
```

`test_smith.py` computes integer Smith normal forms with SymPy. The mpmath diagnostics check the analytic identities using direct polylogarithms and independent Mellin representations, including analytically differentiated Mellin kernels. These numerical checks are **not interval certificates**. Their purpose is to expose convention and implementation errors; the proof of equality is the exact row certificate and the analytic argument in the article.

The delivered fresh logs record:

| Check | Count |
| --- | ---: |
| Universal levels and unit minors | 123 |
| Raw prime rows checked as integer polynomials | 3,905 |
| Support/multidegree checks | 25,628 |
| Binary reflection weight specializations | 478 |
| Reflection weight specializations over F4 | 240 |
| Truncated characteristic-two jet cases | 385 |
| Resolution exactness checks over finite fields | 123 |
| Integer reflection Smith forms | 576 |
| Frozen polynomial certificates | 3 |
| High-precision analytic diagnostics | 18 |

Finite tests supplement the all-level proofs; they do not prove the theorems by extrapolation. No Lean or other proof-assistant verification is claimed.

## Build the PDF

A standard TeX Live installation with Latin Modern, AMS packages, `mathrsfs`, `microtype`, `xurl`, `hyperref`, `bookmark`, and `fancyhdr` is sufficient:

```sh
make pdf
```

The Makefile uses three LaTeX passes to settle the table of contents and cross-references. `make exact`, `make optional`, and `make all` expose the corresponding tests. The delivered PDF has already been compiled and visually checked.

## Integration and corrections

`integration/README.md` gives the insertion plan. `integration/manuscript-section.tex` is a compact, macro-light insertion with the principal theorem statements and proof outline. The full companion article remains the reference for complete proofs.

`integration/CORRECTIONS.md` identifies a Clausen parity sentence inconsistent with the manuscript's stated convention. `integration/propose_clausen_correction.py` prints a guarded unified diff by default; applying it requires an explicit `--apply`. It has not been run against the user's repository. Field-valued Fourier identities are not declared false; the article explains why they do not automatically identify integral lattices.

`CLAIMS.json` separates proved results, classical specializations, exact tests, and numerical evidence. `PROVENANCE.json` identifies the source commit and inspected source blobs. `MANIFEST.sha256` records the final delivered files (excluding the manifest itself). Rerunning tests regenerates their logs, so those delivered-file hashes will then change.
