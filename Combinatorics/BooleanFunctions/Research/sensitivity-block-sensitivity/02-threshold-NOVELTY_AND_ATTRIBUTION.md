# Novelty and attribution ledger

## Starting point

OpenAI, *A superquadratic separation between sensitivity and block sensitivity*, September 25, 2026, family 132 in `openai/math`. The source introduction, construction, recurrences, and separation sections were read in full through the GitHub connector. Their exact blob identifiers and the observed repository snapshot are in `source_provenance.json`.

The source already claims a fixed ordinary-sensitivity exponent greater than two. The present work must not be described as the first disproof of a universal quadratic bound.

## Inherited mathematics

The following ideas are not claimed as new here: regular tournament rows, edge-selected gate coordinates, recursively nested predicates, the use of ordinary and joint sensitivity profiles, separated Hamming-ball initialization, common disjoint block witnesses at zero, OR balancing, and composition powering.

The source attributes the gated-tournament architecture to work by Alexander Meiburg and earlier model-generated ideas. Meiburg's cited result concerns **spectral** sensitivity. Its exponent must not be compared directly to our ordinary-sensitivity exponent as if they measured the same thing. Ambainis–Sun and Ambainis–Prusis are credited for preceding separation and amplification ideas; the article reproves the specific elementary composition facts it uses.

## Refinements proved in this draft

**Threshold-resolved profiles.** Instead of taking a common maximum over every predicate index before each recursive step, retain the single-predicate index and each ordered endpoint pair. Gate reversals inside a full target row then use a stronger interval-specific joint bound.

**Coupled candidate-list packing.** Prove that two gate candidates allow at most `t-2` target candidates and three gate candidates allow at most `t-4`. This yields a monotone three-case maximum rather than unrelated worst-case bounds on target and gate lists.

**Independent parameters and exact certificate.** Separate base-center count and OR multiplicity from tournament degree, use four child positions and a larger forbidden coherent-set size, and evaluate the recurrence exactly. The certified family has divergence at exponent `3667/1809 > 2.027`.

**Exact block packing through minimum weight.** The inherited disjoint block witnesses partition the coordinates and attain the minimum accepting weight. This proves equality, not only a lower bound, for zero-input block sensitivity of the seed and every composition power.

The finite conditional-expectation procedure, interval-containment clipping, both-sided reduction, and direct query lower bound are useful supporting observations. They are not promoted as separate breakthrough results.

## Fair quantitative comparisons

The source's displayed depth-nine seed supports a logarithmic ratio around 2.000252407. Its own sufficient formulas support stronger values: the included scan over depths 1 through 200 with the smallest permitted size parameter attains approximately 2.006470828 at depth 20. The paper reports that scan instead of comparing only with the source's deliberately conservative displayed witness. The scan is not a proof of global optimality for the source's architecture.

The ablation table holds our final construction parameters fixed and compares different bounding schemes. The full ratio is approximately 2.02717077058. Interval clipping does not improve this particular seed and is explicitly not credited with that gain.

## Limits on priority and significance

These are claimed as proved refinements of the cited construction, subject to review of the provided arguments. No exhaustive search of unpublished or newly released work can certify priority. The literature search and source inspection did not establish that 2.02717077058 is the best known possible value across all constructions. The article does not claim that it is.

The result concerns a central Boolean complexity parameter, not an algorithmic speedup. The polynomial Sensitivity Conjecture was already settled by Huang; the paper strengthens a lower-bound exponent, leaving the sharp exponent unresolved.
