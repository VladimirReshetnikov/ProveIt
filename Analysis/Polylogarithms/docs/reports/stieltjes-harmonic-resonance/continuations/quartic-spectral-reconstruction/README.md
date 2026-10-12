# Harmonic-Tail Reconstruction, Quartic Trigamma Moments, and Spectral Stieltjes Calculus

Research continuation prepared for Vladimir Reshetnikov, 11 October 2026.

Source snapshot: `73f18ef013d5b74eafc883efb2c15210642df12a` of
<https://github.com/VladimirReshetnikov/ProveIt>.

## Main results

1. Complete optimal-prefix reconstruction for every pair `(p,q)=(8,2b)`, `b>=5`, including the previously omitted class `b=1 mod 16`.
2. Effective eventual reconstruction for every fixed smaller even order `p=2a`, with an exact terminating threshold algorithm. The unrestricted conjecture is still open. The explicit calculation at `a=5` proves the `p=10` family for all even `q>=3840`.
3. Every regular centered quartic trigamma moment, a fixed six-coordinate formula, an anchored analytic generator, and a finite polylogarithm construction of depth at most three.
4. The several-quadratic-factor second spectral derivative, its ordinary logarithmic correction, elementary resolvent quadrature, and complete confluence coefficients.
5. All higher bilateral and one-sided spectral defects, including every finite Hurwitz/Stieltjes correction, and the conjugate-linear specialization requested by the source.
6. An anchored dilogarithm/Gamma primitive for the cubic-weight nonlinear second jet.
7. An exact attribution/status correction identifying the connected double family with the established Ihara–Nakamura–Yamamoto interpolant.

The classical quartic zeroth moment, the square/cubic inputs, and the first-derivative anomaly framework are credited. Formal coordinate rank is not arithmetic independence. Gaussian S6 and the revised S8 candidate remain conjectural.

## Read and build

- `article.pdf`: the complete article.
- `article.tex`: modular main source; all sections and the bibliography are included.
- `article_singlefile.tex`: complete self-contained TeX source.
- `INTEGRATION.md`: proposed source updates and theorem boundaries.
- `CLAIM_STATUS.json`: machine-readable status map.
- `provenance.json`: pinned source paths, archive membership, and SHA-256 digests.

With a modern TeX Live or MiKTeX installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

After editing the modular sources, `python build.py` regenerates the combined
source and compiles the article. Use `python build.py --source-only` to update
only the combined TeX source.

Alternatively run `pdflatex article_singlefile.tex` twice. All mathematical content is embedded in the single-file source; no external images, bibliography database, or repository checkout are needed.

## Replay the mathematics

Install the two Python dependencies in `requirements.txt`, then run:

```sh
python verification/run_all.py
```

The default includes the complete inherited order-eight certificate replay, the general normalization checks, thresholds for a=1 through 5, and the explicit new (8,34) identity. Suites can also be run individually. Every suite uses local files and writes its own JSON record. The aggregate receipt records runtime versions, script hashes, exit status, and elapsed time.

The article supplies the analytic proofs. The exact scripts certify specified finite identities and integer comparisons. High-precision tests compare independent representations and are not interval certificates. No proof-assistant formalization is claimed.

## Files and integrity

The order-eight polynomial certificate is inherited from the pinned reconstruction report; its mathematical definitions are reproduced in the article and its complete source matrix is rebuilt independently. New finite exceptional residues, quartic coordinates, general threshold examples, and spectral diagnostics are distributed with their generating programs.

The file `verification/order8/order8_identity_b17_k0.json` specifies every coefficient of an ordinary convergent rational polygamma identity for the first newly covered pair (8,34). The generator can produce further extraction rows.

`SHA256SUMS` covers every distributed file except itself. A PDF rebuild can change metadata and should receive a fresh rendered review. The source repository was not modified remotely by this delivery.

Run `python verification/verify_manifest.py` before rebuilding or replaying to
check the delivered bytes. A new replay updates its JSON receipts and logs;
their resulting hashes can therefore differ from the delivered manifest.
