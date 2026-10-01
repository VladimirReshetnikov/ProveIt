# Arithmetic Classification of Geometric Observation Masks

A four-page research companion classifying the universal observation order for every geometric ratio 0<q<1.

Let H contain the positive integers k for which q^(-k) is an integer. If H is empty, one mask universally dominates another exactly when it contains that target mask. Otherwise H=dN for a least positive d, and the complete order is prefix-count dominance separately in each residue class modulo d. Classwise deterministic residue maps realize every permitted comparison, including finite/countable masks, unequal cardinalities, overlap, and arbitrary independent additive noise. Randomized kernels pooling source observations do not add comparisons.

The exceptional ratios are exactly M^(-1/d), M>=2 and d>=1 integers. They form a countable dense set. For any fixed comparison beyond inclusion, however, the admissible ratios are locally finite in (0,1); only inclusion comparisons persist on a nonempty open interval. Universal equivalence of masks holds only when the masks are equal.

## Files and reproduction

- arithmetic_geometric_mask_order.pdf: complete report
- arithmetic_geometric_mask_order.tex: editable LaTeX source
- build.sh: standard TeX Live build
- SOURCES.md: source context and references
- validation.json: final artifact and regression summary
- checks/verify_arithmetic_order.py: standard-library exact arithmetic checker
- checks/arithmetic_order_results.json and checks/verification.log: recorded results
- SHA256SUMS: integrity manifest

Run `bash build.sh` with standard TeX Live or `python3 checks/verify_arithmetic_order.py` for exact checks. The checker uses prime valuations to determine integer powers for 44 root-parameter configurations and compares the residue-prefix test against a generic bipartite matching algorithm for 180,224 mask pairs. It also checks 12,288 nonexceptional rational-ratio mask pairs and 1,320 exact power-membership identities. These are finite regression checks; the countable product and universal-kernel assertions are proved analytically.

## Scope

Universal comparison means one kernel for every total-sum reweighting, equivalently every positive-probability lower threshold. The theorem does not decide one fixed conditioning rule, a specified two-hypothesis comparison, or the sharp overlap asymptotics for the Fabius conditioning weight. General Blackwell and convolution methods are classical. No general priority claim is made, and these are ordinary mathematical proofs rather than formalized or externally refereed results.
