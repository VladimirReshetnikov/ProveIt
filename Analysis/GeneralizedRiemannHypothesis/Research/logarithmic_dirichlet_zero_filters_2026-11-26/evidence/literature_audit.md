# Literature and source audit for positive Dirichlet zero filters

## Scope of the proposed claim

The new packet proves an explicit finite construction with support radius at most `4*pi*K/delta + N/B`, exact zeros to prescribed orders, and tail bound `(sin 1)^N`. For a fixed finite Dirichlet family, the classical local count is `K=O(log B)`; taking `N=ceil(B log B)` gives logarithmic support and exponentially small high-frequency tail. This improves the inspected prior packet's reciprocal-ordinate support sum `O(log^2 B)`. Generic positive Fourier interpolation and Fourier-Gram diagonal dominance are not new concepts. Global priority of the combined quantitative arithmetic statement is not certified.

## Primary material actually inspected

1. **Kahane (1962)**, *Pseudo-périodicité et séries de Fourier lacunaires*, Ann. Sci. ENS (3)79(2),93–150, DOI 10.24033/asens.1108. Full primary paper inspected at <https://www.numdam.org/item/ASENS_1962_3_79_2_93_0.pdf>. Prop VI.2.1, printed p131, gives a Fourier-Gram dominance criterion for a positive compact measure to yield coefficient/integral norm equivalence. VI.2.2 identifies the interpolation consequence. This is close methodological precedent. It does not in that passage prove positivity of a newly interpolating density; our coefficient l1 bound supplies that separately. 

2. **Kozma–Oravecz (2002/2003)**, *On the gaps between zeros of trigonometric polynomials*, Real Analysis Exchange28(2),447–454. Full author preprint <https://arxiv.org/pdf/math/0601021> inspected. Theorem1: symmetric integer spectrum S, every ball of diameter sum over S of 1/(4|lambda|) contains a zero. Proof adds translates to remove frequencies, the dual of positive convolution cancellation. Statement uses integer frequencies; elementary removal itself extends to real ones. Journal metadata independently checked at Weizmann.

3. **Montgomery (1973)**, *The pair correlation of zeros of the zeta function*, Proc. Symp. Pure Math24,181–193. Full author-hosted primary PDF <https://public.websites.umich.edu/hlm/paircor1.pdf>. Under RH, Cor1 squared-sinc pair sum has leading coefficient `1/a+a/3` for fixed `0<a<1`; positivity yields distinct-ordinate multiplicity second moment ≤(4/3+o)N by taking the limit after T→∞. This is a theorem, not the full pair-correlation conjecture.

4. **Conrey–Ghosh–Gonek (1998)**, *Simple zeros of the Riemann zeta-function*, Proc. LMS(3)76,497–522. Full primary paper <https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/simplezeros.pdf>. Printed p498 explicitly recalls Montgomery's second-moment bound and derives distinct proportion≥5/6; their stronger main result needs RH+GLH. Our lower-bound paragraph only uses 5/6, obtained by the elementary integer inequality `1≥(3m−m²)/2`. Jensen then gives `H≥(5/12−o(1))logB` for simple cancellation, and `(1/2)logB−(1/2)log(2*pi)−1+O(log²B/B)` for multiplicity cancellation. No novel zero-density claim is made.

5. **Graham–Hare (2006)**, *ε-Kronecker and I0 sets in abelian groups, IV: interpolation by non-negative measures*, Studia Math177(1),9–24, DOI10.4064/sm177-1-2. Complete published primary paper inspected via <https://scispace.com/pdf/e-kronecker-and-i0-sets-in-abelian-groups-iv-interpolation-my1e3sdih8.pdf>. Printed p10 says explicitly that Florek provides a Sidon-set version of related positive-interpolation results. This verifies historical context, not a specific quantitative theorem in the unread Florek paper. Sidon/Kronecker interpolation is not automatically equivalent to arbitrary separated finite spectra with a uniform support constant.

## Particularly relevant unread paper

**J. Florek (1987)**, *Interpolation by the Fourier–Stieltjes transform of a positive compactly supported measure*, Colloq. Math54,113–120, DOI10.4064/cm-54-1-113-120. Official metadata actually opened:
<https://www.impan.pl/en/publishing-house/journals-and-series/colloquium-mathematicum/all/en/publishing-house/journals-and-series/colloquium-mathematicum/all/54/1/105540/interpolation-by-the-fourier-stieltjes-transform-of-a-positive-compactly-supported-measure>. Full-text link returned HTTP 403; author publication list corroborates title/pages. Thus cite the subject and metadata, not an invented theorem. This limitation is material to the refusal to certify global priority.

## Other related work and limits

Bondarenko–Radchenko–Seip, *Fourier Interpolation with Zeros of Zeta and L-Functions*, Constructive Approximation57 (2023),405–461, DOI10.1007/s00365-022-09599-w, full primary HTML inspected at <https://link.springer.com/article/10.1007/s00365-022-09599-w>. Theorem1.1 reconstructs strip-analytic functions from zeta-zero jets and Fourier samples at log integers. It does not state our positive compact-support filter. Broad novelty for 'Fourier interpolation using zeta zeros' would be false. No need to cite this as an input.

Classical Beurling–Malliavin completeness/gap theorems primarily concern signed or complex measures, entire functions, and infinite spectra. They should not be asserted without proof to supply a positive normalized measure with these finite constraints. A search did not locate a directly matching quantitative theorem; that is not evidence of absence.

## Current RH/GRH source facts

Detailed immutable source analysis is in `source_audit.md` and selected exact sources plus Git blob SHA provenance are in `upstream_snapshot/`. Commit `72fead102f663d5c7a407964a13dc0cf9d977207` of lsernau/grh-lean proves RH and Dirichlet GRH; Lean4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Five public results depend only on propext, Classical.choice, Quot.sound according to inspected independent logs. Both readable and compact exact snapshots have successful full paranoid Comparator logs at <https://math.mit.edu/~drew/shortgrh/>. The official joint statement is <https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>. No local full rebuild occurred. The new theorem is not Lean-formalized. Wikipedia was inspected and is consistent with the primary records.

## Internal proof review of annihilation_theorem.tex

Read the whole proof fragment. The finite construction, greedy coloring including multiplicities, positivity envelope, tail bound, frequency-error estimate, Jensen bound, constants in the integrated Riemann–von Mangoldt formula, and normalization of the final prime-remainder average are internally consistent. Endpoint handling in occupancy uses `(x,x+delta]` and reuse at distance≥delta correctly. The support lower bound counts each prescribed transform zero with its required order; it is not incorrectly inferred from distinct arithmetic zeros when multiplicities are not imposed. The explicit prime-sum spectral expansion and sharper remainder are proved separately in applications_and_audit.tex and were subjected to an additional mathematical review. The generic Fourier statement and root-zero computations alone do not prove that arithmetic input.
