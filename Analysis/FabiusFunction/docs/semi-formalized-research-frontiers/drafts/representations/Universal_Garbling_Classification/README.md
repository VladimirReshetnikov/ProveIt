# Universal Garblings of Tilted Uniform Observations

A self-contained five-page mathematical companion to Exact Observation Order for Fabius Conditioning.

The main theorem classifies one Markov kernel that must work under every total-sum reweighting: two independent truncated exponentials admit such a kernel exactly when their real tilt parameters agree and the source cap is a positive integer multiple of the target cap. The kernel is uniquely the residue map, up to reference-null sets. Arbitrary independent additive noise, with no moment assumptions, does not alter the criterion. All lower-threshold conditionings already determine the full experiment.

A separate proposition proves that for arbitrary compactly supported independent coordinate laws, universal garbling is equivalent to a probability convolution factorization of the source law by the target law. Classical comparison-of-experiments and convolution antecedents are explicitly acknowledged. The proofs are ordinary mathematical arguments, not formalized or externally refereed results.

## Files

- universal_garbling_classification.pdf: complete report
- universal_garbling_classification.tex: editable LaTeX source
- build.sh: standard TeX Live build command
- SOURCES.md: references and exact repository source identifiers
- validation.json: final artifact and check summary
- checks/verify_discrete_analogue.py: standard-library exact rational regression
- checks/discrete_analogue_results.json and checks/verification.log: recorded results
- SHA256SUMS: package-file integrity manifest

## Reproduction

Run `bash build.sh` with a standard TeX Live installation containing the packages named in the source. Run `python3 checks/verify_discrete_analogue.py` to reproduce the finite exact checks. The checker reconstructs a unique candidate kernel from total-sum equations in a discrete truncated-geometric analogue and then verifies all remaining equations and stochasticity. It checks 576 parameter pairs, identifies exactly 42 feasible cases, and checks independent-noise and threshold identities. This finite analogue is a regression check; the continuous theorem rests on the analytic proof in the report.

## Scope

The classification concerns a single source coordinate, a single target coordinate, and one kernel for the complete weight or threshold family. It does not classify multicoordinate kernels, one prescribed threshold, or a restricted pair of hypotheses. The preceding modulo report is a separate unchanged companion.
