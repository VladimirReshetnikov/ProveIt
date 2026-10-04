# Four-particle timing frontier: targeted read-only check

4 October 2026. This is a scope check and next-step recommendation, not a new article or a literature-priority claim. No upstream executable or saved schedule was run.

## Bottom line

The existing ProveIt proof already establishes the proposed finite-control / one-additive-gap mechanism, including eventual affine gap growth and quadratic elapsed time. It is substantially stronger than a bare decidability assertion. Source 18 already turns that classification into complete, disjoint fixed-input quadratic charts.

The more specific proposal that **all exact anchored-pattern hit sets are finite unions of quadratic sequences** is false under the usual meaning of sequences indexed by all sufficiently large integers or by fixed arithmetic progressions. Growing intervals of hits must also be allowed. The newly audited reversible clock itself gives a short counterexample below.

The defensible remaining target is a **uniform-in-initial-input quadratic chart theorem for each fixed rule**, with an effective compiler and canonical chart ownership. Current sources explicitly leave uniform timed arithmetic normal forms and uniform stationary-frame untimed Presburger definability open. Published novelty of such a strengthening has not been established.

## What the existing sources actually prove

All statements below concern a fixed finite-radius, deterministic, time-independent, translation-equivariant one-dimensional CA with finite positively weighted alphabet, unique zero-weight vacuum, conservation on finite supports, and at most one weight-one symbol. Binary NCCAs are included. Reversibility is not required.

1. **Source 17, Four-mass decision theorem.** Exact and translated reachability and anchored and translated finite-pattern occurrence are decidable at total mass at most four. Required pattern zeros are enforced. This is effective from the rule, with no efficiency bound.
2. **Source 17, Additive gap transitions.** In the isolated-unit stationary frame, every continuing large-gap section has finite-mode/residue control and updates
   `q'=f(q,D mod M), D'=D+c, L'=L+e, h=alpha D+beta`, with `alpha>0`. Only one unbounded control counter survives. A compact moving mass-three packet plus a unit either escapes or resets to the bounded four-mass core; two mass-two packets likewise meet in a bounded full encounter.
3. **Source 17, Effective orbit alternatives.** Every fixed mass-four input eventually has independent finite-phase objects, whole-configuration translated periodicity, or an expanding shuttle. In the shuttle,
   `D_n=D_0+n Delta`, `L_n=L_0+n E`, `Delta>0`, and
   `T_n=T_0+A n(n-1)/2+C n`, `A>0`.
   Complete spatial phases are affine/Presburger in the cycle counter and one within-flight counter. The theorem includes all intermediate configurations, not merely returns.
4. **Source 18, Sufficient chart interface.** The complete timed orbit of each fixed input is the bijective image of a finite disjoint family of affine-domain charts, each using at most two natural parameters and a rational polynomial output map of degree at most two. For flight phase `r` of period `p`,
   `t=S_l(n)+r+p j`, with `0<=r+p j<h_l(n)` and `h_l` affine. Local-prefix charts have just `n`. Original-frame positions add `delta t`.
5. **Source 18, Canonical timed quartic.** The above charts give a fixed-arity natural-single-fold quartic for complete timed configurations. The arity and coefficients may depend on both rule and initial input. The potentially enormous finite prehistory is allowed to be materialized. The general rule-to-chart preprocessing is not implemented.
6. **Source 20, First hits of fixed patterns.** A fixed-input stationary-frame first-hit relation already includes fixed finite-pattern anchors, with zeros enforced. First-hit domains are semilinear and least times are piecewise quadratic. This is not a uniform theorem in arbitrary initial inputs or arbitrary externally encoded patterns.

These are conventional mathematical proofs with independent scoped reviews, not proof-assistant formalizations. Source 18 is conditional on source 17's effective normal form. The current repository now contains `review_timed_four_mass_source18_intake.md`, whose verdict is PASS on that conditional chart/compiler argument and the explicit binary certificate; the inherited article's older front matter saying source 18 had not been reviewed is therefore no longer a complete account of current review status.

### Source locations

The inherited inert article is `/workspace/shared/four-particle-clock-independent-audit-20261004/inherited-article-source.tex`:

- Model and main theorem: lines 5979–6012
- Section machine and additive updates: lines 6152–6262
- Effective alternatives and quadratic clock: lines 6263–6339
- Original-frame anchored cutoff: lines 6340–6384
- Explicit remaining questions: lines 6550–6565
- Fixed-input quartic scope: lines 6606–6638
- Chart interface and complete phase construction: lines 6660–6797
- Fixed-pattern first-hit corollary: lines 10037–10057

Current repository listing returned the same article blob SHA-1 `ec10c7a579e04d3d27a92035d9a180dfcb695ff2`; local SHA-256 is `17d3c0d9b449c689f88c1dc082ffee9b116993e4f5585b65d52c4fe591b2d962`.

- [Article](https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/article.tex)
- [Source-17 independent audit](https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/17-four-mass-INDEPENDENT-AUDIT.md), blob `9012e5ddc9b194c7a37881766ef14d6eec7fd502`
- [Batch80 low-mass review](https://github.com/VladimirReshetnikov/ProveIt/blob/main/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_batch80_low_mass.md)
- [Current source-18 intake](https://github.com/VladimirReshetnikov/ProveIt/blob/main/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_timed_four_mass_source18_intake.md), blob `7410ef47d433575021646886a10468c06a79b627`

## Why isolated quadratic sequences are insufficient

Use the newly audited reversible binary clock, initial support `C_d={0,5,6,d}`, `d>=13`. Let

`t_k=k^2+(2d-23)k`, and `ell_(d+k)=t_(k+1)-t_k`.

Observe the exact pattern **100000** on sites 0 through 5. Site 0 stays occupied. Sites 1 through 4 are always vacant. Site 5 is occupied precisely at relative cycle time 0 in the right phase and at relative cycle time `ell_(d+k)-1` in the left phase. Thus its complete hit set is

`H = union_(k>=0) {t_k+1, ..., t_(k+1)-2}`

or equivalently

`H = N \ ({t_k:k>=0} union {t_(k+1)-1:k>=0})`.

It has natural density 1, but is not cofinite. A nonconstant quadratic sequence restricted to a finite collection of arithmetic-progressions of indices has density zero. A finite union of linear sequences with such restrictions is ultimately periodic. A finite union of degree-at-most-two sequences with density 1 must consequently have its linear part of density 1, hence must be cofinite. Therefore H cannot be such a finite union. Arithmetic phase restrictions do not repair the proposed class.

This is a direct corollary of the existing new-clock orbit formulas, not a new CA construction. It remains valid in the globally reversible subclass. Do not confuse an exact finite pattern with an exact complete configuration: the latter specifies the whole support and is a different observation.

## Correct fixed-input arithmetic envelope

An immediate route from sources 17–18 is a finite union of **quadratic arithmetic bands**, plus finite exceptions and ultimately periodic tails:

`{Q_i(n)+p_i j : n>=n_i, n in a fixed residue class, l_i(n)<=j<=u_i(n), j in a fixed residue class}`,

with rational quadratic `Q_i`, integer-valued on its domain, and rational affine bounds `l_i,u_i`. Residue refinement clears floors and denominators. Some bands have bounded width, including isolated quadratic sequences.

Reason: in the zero-drift expanding case each anchored pattern test, including every absent-particle requirement for a zero, is a Boolean combination of affine conditions on `(n,j)`. Intersect with the complete flight domains, split the finite Boolean conditions into disjoint cases, refine residues, and choose the eventually dominant affine lower/upper bounds. Finitely many exceptional cycle indices give finite time intervals. Nonzero original-frame drift has an effective finite observation cutoff: a nonzero pattern has only finitely many hits, and an all-zero pattern is eventually always present. Nonexpanding tails already have Presburger timed relations.

This is a natural explicit corollary/simplification of the already-proved chart theorem, not a fresh dynamical classification. A self-contained proof of the band refinement and any counting corollaries would still need to be written and checked before being advertised as an additional theorem. In particular, a general density/counting theorem was not proved by this frontier check.

## Strongest plausible remaining extension

For **each fixed binary NCCA F**, seek one finite, effective, canonically disjoint family of affine-domain charts for **all** mass-at-most-four initial configurations simultaneously. Initial occupied coordinates are external chart parameters; at most two additional evolution parameters should suffice per chart. The complete timed-configuration output should have total degree at most two, while stationary-frame spatial outputs should remain affine. Original-frame spatial outputs then remain quadratic by adding `delta t`.

If proved, this would strengthen the present fixed-input result, answer the repository's uniform timed-normal-form question, and plausibly imply its uniform untimed stationary-frame Presburger question. It would also give a quartic compiler whose arity depends on the fixed rule and support-label case, not on the particular initial gaps. This is a proposed theorem, not established here.

The unpaid work is parameter-uniform initial dispatch; symbolic first-contact selection; contracting-cycle acceleration with every intermediate guard enforced; affine/residue descriptions of the first bounded-core reset; and globally unique ownership of all finite-prefix, flight, contact and tail times. Simply materializing the prehistory for each input does not establish uniformity. Summing a variable number of affine-gap durations introduces the expected terms `n D_initial` and `n^2`, still total degree two, but that observation is not the full proof.

An implemented general rule-to-section compiler, explicit complexity bounds, and formal verification remain separate concrete targets. Radius optimization for the new reversible clock is another resource question, but it does not replace the stronger uniform arithmetic frontier.

## Literature boundary

Targeted public searches covered four-particle NCCAs, fixed-particle timing/hitting sets, quadratic clocks, and later work by Kong/Imai. They found no primary-source theorem resolving this exact uniform timing question. That negative search is not a novelty or priority result.

The existing review directly checked Kong's 2021 binary thesis, recording its three-particle theorem and its then-open four-particle conclusion. In this pass the university full-text endpoint returned HTTP 429, so those page claims remain inherited review evidence, not newly verified primary pages. The Alhazov–Imai full 2016 paper was not obtained; its publisher entry was found. Morita's accessible 2012 primary abstract concerns a multistate reversible NCCA simulation, not a fixed-four-particle binary timing classification. Relevant primary endpoints:

- [Kong thesis](https://hiroshima.repo.nii.ac.jp/record/2002360/files/k8621_3.pdf)
- [Alhazov–Imai publisher entry](https://ieeexplore.ieee.org/document/7818615/)
- [Morita 2012](https://arxiv.org/abs/1208.2760)

Safe language: **“A uniform extension not established in the current audited ProveIt sources; external published novelty remains unverified.”**
