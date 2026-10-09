# Verification record

Date: 8 October 2026.

## Mathematical review

Independent review passes checked:

- The positive-coefficient scalar inequality, including \(x=0\), \(x=1\),
  \(m<s\), and the convention \(\binom mj=0\) for \(j>m\).
- Integration into the coupon probability bound and the signed-measure
  interpretation when multiple subsets have the same total probability.
- The Charlier signs and the scaling in the dimensionless product jets.
- The optimal scalar leading constant, the second term, global
  localization of maxima, and the analytic implicit-function argument.
- The all-\(m\) order-one bound and its derivative calculation.
- The arbitrary-probability Touchard moment envelope and its dependence
  on \(n,m,L,s\).
- Rare-coupon sharpness, the signed uniform-window limit, and its
  nonvanishing example for every fixed positive \(L\).
- The precise pointwise comparison with Hwang–Li–Zacharovas Lemma 5.3 and
  the stronger earlier order-one Lemma 2.1.
- The limitation on comparisons with Zacharovas's finite-difference
  seminorm and the distinction between arithmetic and bit complexity.

These are mathematical audits by independent AI work streams, not
external peer review and not proof-assistant checking.

## Independent implementation checks

Command:

~~~text
python -m unittest discover -s tests -v
~~~

Result: **11 test methods passed**. The loops include approximately 598
valid certificate calculations, 60 seeded nonuniform rational inputs,
orders 1–5, and several working precisions down to 64 bits.

The independent reference methods are integer inclusion–exclusion,
an exact occupancy-state Markov recurrence, and an exact uniform
distinct-count recurrence. Direct subset sums also check the moments
and approximants. These are different calculations from the product-jet
implementation.

## Probability experiments

- 24 uniform instances.
- 20 rare two-coupon instances.
- 24 heterogeneous instances.

All **68** independently computed 320-bit reference intervals were wholly
contained in the 224-bit certificates. The recorded JSON retains real-ball
strings, not just rounded display values.

## Scalar experiments

Exact symbolic coefficient identities were checked for orders 1–6, using
both the coefficient recurrence and independent binomial–exponential
convolution. Twelve 120-digit stationary-point experiments at \(m=1000\)
and \(m=10000\) agreed with the proved two-term asymptotics. Domain probes
in these experiments are illustrative and do not prove global optimality.

## Artifact checks

The final article is compiled with pdfLaTeX/BibTeX through latexmk.
Cross-references and citations resolve. PDF pages are rendered and visually
reviewed; the final package excludes intermediate LaTeX files and Python
bytecode. The ZIP contents and per-file checksums are checked before
delivery.

## Limits of this record

The literature review identifies a definite earlier lemma that the new
bound strengthens. It is not an exhaustive proof of novelty. Theorems
about growing order, general relative error, and bit complexity are
explicitly left as further research.
