# Beta transfer for harmonic polylogarithms

A research continuation for ProveIt, based on repository revision
`5537940fde730713eaac752265a486832b2fe540`.

The article is `article/beta_transfer.pdf`; its complete editable source is
`article/beta_transfer.tex`. It contains written proofs, not a proof-assistant
formalization. The source audit is targeted, not an exhaustive novelty search.

## Main results

For `F_{a,b}(z) = sum_{n>=1} H_{n-1}^{(b)} z^n/n^a` and `g_{a,b}=Im F_{a,b}(i)`:

- At fixed total order `w=a+b>0`, `-Im F_{a,w-a}(i rho)` strictly decreases with
  `a` for `0<rho<=sqrt(3)`. This proves Conjecture 12.3 in the preserved
  **The Sharp Real-Order Threshold for Harmonic Polylogarithms** report.
- The least constant in `0<E_N-g_{a,1-a}<C 2^{-N}`, uniform over `0<a<1` and
  `N>=1`, is `C=pi/4+log(2)/2`.
- A positive divided-difference remainder proves one-sided Euler convergence
  at **all** positive orders, even below `a+b=1`. These are analytic/Abel
  values where the original boundary series fails the term test.
- A new critical density satisfies `1<nu_a(T)<1+1/T`. Its full asymptotic
  expansion and a parameter-uniform remainder yield the worst-parameter law
  `(1-a_N) log((log N)/2) -> 1` and the corresponding maximal-error asymptotic.
- Rational beta profiles have exact finite polylogarithm reductions. Common
  poles force lower-order terms; six Gaussian specializations are certified
  in exact cyclotomic fields.
- The stronger monotonicity claim for **every** scaled error is false:
  `A_8(1/10)-A_8(0)>13/10000` is certified exactly.

`CLAIM_STATUS.md` separates these theorems, inherited results, exact finite
certificates, diagnostics, and unresolved questions. The established S4 proof
is not reclassified as new; S6 and the broad angular-zero questions remain open
in this report.

## Inspect the delivered package

Python 3.10 or newer is required by the supplied programs. From this directory:

```sh
python code/check_package.py --manifest
```

This checks the original SHA-256 inventory and the result receipts. It is not
an analytic theorem prover. Run the inventory check **before** rebuilding;
PDFs and diagnostic bytes can differ across library and TeX versions.

## Replay exact certificates

These two programs require only the Python standard library:

```sh
python code/certify_euler.py
python code/verify_cyclotomic.py
```

The default first program uses 160 Euler terms and 140-digit rational power
brackets. It checks 1,755 integer-root inequalities, encloses twelve Gaussian
values (three below the moment threshold), and verifies the eight-term
counterexample. The second reconstructs six rational-function identities in
`Q[X]/Phi_L(X)` and checks 548 rational coordinate equalities. Neither uses
PSLQ, a numerical root of unity, or a numerical polylogarithm oracle.

## Replay supplementary checks

Install the tested optional packages listed in `requirements-diagnostics.txt`,
then run:

```sh
python code/verify_symbolic.py
python code/diagnostics.py
```

The first checks 176 exact algebraic identities with SymPy. The second uses
mpmath for independent integral comparisons and numerical diagnostics. Their
roles are different and their outputs are labeled accordingly.

## Rebuild the article

A TeX installation providing `pdflatex`, AMS packages, Latin Modern,
`geometry`, `booktabs`, `microtype`, `xurl`, `fancyhdr`, `hyperref`, `bookmark`,
and `needspace` is required.

```sh
python code/build.py
python code/check_package.py
```

The build is isolated, uses three passes, rejects unresolved references and
overfull boxes, and leaves only the final PDF in `article/`. Its metadata epoch
is fixed to the pinned repository commit time. Exact byte reproducibility
across different TeX installations is not promised. `data/build_receipt.json`
and `data/visual_review.json` describe the delivered build and rendered review.

## Integration

The archive is additive and already follows the intended repository path:

`Analysis/Polylogarithms/docs/reports/beta-transfer-critical-euler/`

See `integration/INTEGRATION.md` and the `betatransfer:`-prefixed manuscript
fragment. Do not overwrite the historical threshold report or its immutable
incoming archive. No upstream Git branch was modified during preparation.

## Files

`article/` contains the PDF and TeX. `code/` contains two standard-library
certifiers, symbolic and numerical checks, a build script, and an integrity
checker. `data/` contains exact fraction certificates, cyclotomic coefficients,
check logs, diagnostics, and build/review receipts. `PROVENANCE.json` identifies
the pinned predecessor source and its verified hashes. `MANIFEST.sha256`
inventories every other delivered file.
