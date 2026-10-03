# Batch80 review: single-unit three-mass and four-mass decidability

**PASS within the stated mathematical and executable scopes. No source or theorem correction requested.** The single-unit three-mass theorem supplies a uniform timed Presburger relation; the four-mass theorem supplies decidability by a different orbit analysis and correctly avoids claiming timed semilinearity. The binary four-mass shuttle explicitly disproves that stronger timing claim. Neither result yields a new universal-Diophantine operation bound.

The [portable checker](review_batch80_low_mass.py) and [deterministic receipt](review_batch80_low_mass.json) authenticate all three original archives and all 58 members before executable use. Originals are preserved. The review reads the full editable articles, their substantive proof supplements and supplied mathematical audits, every Python module, and the replay/build scripts. It runs all nine relevant non-figure Python verifier invocations in fresh private extraction trees, including the public binary helper's normal and optimized boundary tests. The optional matplotlib renderer and TeX/PDF rebuilds are not run; their scripts were read, and every plotted JSON/CSV state is checked independently.

## 1. Frozen inputs and the attribution-only revision

Source commit: `4e270aa4648c5fd7e18626507531046715976535`.

| Archive in `docs/incoming` | SHA256 | Members |
|---|---|---:|
| `Four_Mass_Decidability_Package.zip` | `0bcc026a8ca7bd4745b82e6f9c2841073e5fb8c639970105690fc40803a780fe` | 33 |
| `Single_Unit_Three_Mass_Decidability.zip` | `25c0d2712b111ba9240fb11b23689b3eded14b059a5a793e33aa515f1c97f646` | 12 |
| `Single_Unit_Three_Mass_Decidability (1).zip` | `299fef3508423dfe1fc88dc3473a39a40eac7cbfaf5d53c16dc26b9a3d119b12` | 13 |

The last archive is a revision of the second, not an independent theorem or implementation. It adds `REVISION.md` and changes exactly README, source provenance, manifest, article TeX and article PDF. Seven common members are byte-identical: both executable test sources, both saved test receipts, the independent audit, and the two shell scripts.

The complete TeX body from “Model and main result” through the end of the canonical quartic section is byte-identical, SHA256 `7a558f87fde57305988d639256b770209b45eabdd337018723d50ff2c26a0e43`. The validation section is also byte-identical, SHA256 `bce5a926bf741fac88ea884a76374550b79c3beac20f0674aa0bd5ac34627e1e`. This checks complete contiguous text, preserving theorem/formula multiplicity. I read the remaining diff: it changes the abstract's attribution, the literature-comparison section and bibliography. The revised source correctly separates a binary precursor from the weighted and uniform claims proved here. Running the identical code once reproduces both versions' two saved receipts.

## 2. Exact hypotheses and the three-mass proof

The model is a fixed, deterministic, translation-equivariant, time-independent, one-dimensional CA of finite radius and finite alphabet. Vacuum is quiescent and is the unique weight-zero symbol; other weights are positive integers. There is **at most one weight-one label**, though several labels may have weight two or three. Conservation is required on every finite-support configuration. The input has bounded total numerical weight, not merely bounded occupied-site count. No reversibility hypothesis is needed.

The revised single-unit article states this at TeX lines 44–82. Its theorem is uniform in all sparse input/output positions and time for each fixed rule and fixed label case. It does not place arbitrary rule tables in one Presburger parameter or construct a universal Presburger relation.

I checked the main proof steps:

1. An isolated unit must remain a single copy of its unique label at a fixed displacement. Subtracting that displacement produces a stationary-unit frame of radius at most `S=max(1,R+|delta|)`. If there is no unit label, mass at most three has at most one occupied site and is a finite-state walker. Radius zero is explicitly included.
2. A bounded mass-two packet cannot split into separate `2S`-components. For two units at distance greater than `S`, their original sites retain the isolated-unit outputs and exhaust the mass. At distance at most `S`, new support lies in their common neighborhood `[d−S,S]`, of width at most `2S`. A weight-two singleton has the same coarse diameter bound. Normalized packet shapes therefore form a finite effective set.
3. Outside the diameter-`4S` three-mass core, the only moving case is a bounded pair plus a stationary unit. The actual orbit agrees with the independent counterfactual union through first core entry, including the entry state: before that point the components are more than `2S` apart and their output supports remain disjoint. This avoids assuming an overlap can be merged arbitrarily.
4. First entry is an exact signed affine interval problem on finitely many packet phases. For left endpoint `a+A_r+nD` and packet width `d_r`, the bounds are `b−4S <= a+A_r+nD <= b+4S−d_r`. Positive, zero and negative drift are handled separately. No scan through the initial gap is needed.
5. Repeated normalized core states give a translated orbit identity at **every intermediate time**, not merely at return times. The uniform Presburger construction separately handles no entry through the queried time or the unique first entry, then uses a finite core-orbit formula. Subsequent periods and drifts depend on the finite core state, not an unbounded initial gap, so no product of quantified variables is introduced.

The published normalized counts `N2+2S` for mass-two shapes and `N3+8S*N2+binom(4S,2)` for the mass-three core agree with the possible weight partitions and support orderings. Pattern zeros are explicitly enforced as absence of occupied sites. Exact targets compare the entire support. Moving back to the original frame substitutes `y_j−delta*t`, which remains Presburger. These facts support the claimed exact, translated and finite-pattern decidability consequences.

## 3. The four-mass argument and its different quantifiers

The four-mass article states its model and theorem at lines 44–73. I read its entire proof and `finite-seed-section-lemma.md`, including the following points that are essential to effectivity.

The contact convention is **occupied-site proximity at most `2S`**, not an incompatible span-`4S` convention. A simultaneous head/two-marker contact is connected and has span at most `6S`. The finite connected mass-three seed library is computed first; its full finite prefixes and periodic phase representatives determine `B`. Only then are `N=4B+12S` and `W=N+2B` chosen. This ordering is noncircular.

The `B` bound includes delayed emissions, finite detachments and returns, all phase representatives, and the residual marker. A distant fourth unit stays outside every seed prefix. A compact translating three-mass object is followed for its potentially unbounded travel: it either remains independent or contacts the fourth unit with full span at most `2B+2S<W`. It cannot carry a second independent unbounded gap through that reset.

In the remaining recurrent configuration, a bounded mass-two head travels between two stationary units. Its marker-to-marker gap is the only unbounded control counter. The contacted marker's original coordinate is explicitly tagged in the finite entry type; physical identity of indistinguishable units is not assumed. For every continuing large-gap transition,

```
mode' = f(mode, gap mod M),
gap'  = gap + c,
left' = left + e,
duration = alpha*gap + beta,  alpha>0.
```

The first-contact condition is exact because a mass-two packet has diameter at most `2S`: the neighborhoods of its occupied endpoints fill its expanded hull. On each drift residue, the candidate phase times have the same leading gap coefficient; earliest-phase selection therefore uses finitely many constants. The high-gap threshold guarantees nonnegative periodic indices. Source/target marker order cannot reverse because a contact moves only one marker by a bounded amount less than the high gap.

The possible component mass partitions `4`, `3+1`, `2+2`, `2+1+1`, `1+1+1+1` exhaust the rule's geometry. The article explicitly chooses how to tag overlaps between bounded-span and live-emission representations. Ordinary transitions have positive elapsed time. In a repeated finite high-control cycle, zero gap change gives translated periodicity, positive change keeps all high guards valid, and negative change permits exact acceleration only while **every intermediate gap** remains above threshold. Finitely many ordinary normalized states then make the analysis terminate. If there is no unit label, at most two sites occur and the separate two-walker/core argument applies.

The resulting stationary-frame reachable set is Presburger **for a fixed input and after forgetting time**. An expanding cycle has affine spatial sections but quadratic accumulated time with positive leading coefficient. The article does not silently promote this to uniform timed Presburger definability.

For original-frame anchored observations with nonzero unit drift, the quadratic time translation eventually dominates all linear spatial spread. The explicit bound is uniform over every phase within a cycle. It gives an effective finite cutoff for a pattern containing a nonzero symbol or a nonempty exact target; an all-zero window is satisfied afterward. For zero frame drift the untimed spatial description suffices. Translation-invariant observations are frame-invariant. No unrestricted quadratic Diophantine decision procedure is being imported.

This establishes the stated decidability obstruction to a computable mass-at-most-four encoder with exact-target or finite-pattern halting observation in this class. It is not a lower bound on general Diophantine variable/gate counts, a theorem about signed mass, or a restriction on typed systems with several unit labels.

## 4. Literal binary shuttle and witness domains

The binary example has four occupied sites, ordinary weights 0/1, and radius at most six. Its exact component replacements are

```
{0,1}   -> {1,2}
{0,2}   -> {-1,1}
{0,1,3} -> {-1,1,4}
{0,2,4} -> {0,3,4}.
```

Different input components are separated by at least three, while output hulls expand by at most one. Their output supports are disjoint and every replacement preserves cardinality. Exact recognition guards and every changed output site fit in radius six; unrecognized larger components stay fixed. The independent checker reconstructs all 8,192 local outputs by guarded pattern detection, compares the actual strict public `step`, and verifies all 8,192 de Bruijn potential identities. The telescoping identity proves conservation for arbitrary finite support, beyond a finite dense census.

For initial support `{0,3,4,d}`, `d>=7`, a full cycle lasts `2d−10` and increments `d`. I checked the two complete within-cycle formulas and their collision endpoints. They give precisely

\[
 t_k=k^2+(2d-11)k.
\]

The pattern `10011` at sites 0–4 has no other hits, including its required zeros. The increasing gaps rule out eventual periodicity, hence timed Presburger definability. This is compatible with untimed decidability. The literal collision pair `{0,1,4,6}` and `{1,2,3,5}` has the same image, so the example is correctly described as noninjective, not reversible.

For natural inputs `x,t` with `d=7+x`, the timing polynomial is

\[
 [k^2+(2x+3)k-t]^2.
\]

Its natural witness `k` is unique at a hit and absent otherwise. Nonnegative rational witnesses give the same fibers because the quadratic is monic with integer coefficients. Nonnegative real witnesses do not: at `x=0,t=1`, the false hit has real witness `(sqrt(13)−3)/2`. Allowing signed integer witnesses also loses uniqueness: the second root at a genuine hit is `−k−(2x+3)`.

The receipt contains a literal six-gate schedule `x+x; add3; addk; multiplyk; subtractt; square`, correctly charging **2M+4A**, one natural witness and exact degree four. At fixed gap the coefficient is constant and the stated **2M+2A** schedule is valid. These are evaluation counts for the specific timing predicate; constructing the CA input and bit complexity remain outside those counts. No general fixed-arity unique-witness theorem follows merely from four-mass decidability.

## 5. Canonical arithmetic relevance

The single-unit report's quartic corollary first eliminates Presburger quantifiers, including time for untimed reachability, and only then invokes the existing canonical arithmetic compiler. That order is necessary: keeping an arbitrary reaching time as a witness would usually destroy uniqueness. Its stated `K=2I+6C+B` natural witnesses and `E=2I+5C+B+1` quadratic residuals are formula/circuit-dependent, with degree at most four. `B` is Boolean-gate count here, not the four-mass geometric constant.

The bound of twelve natural external coordinates, or thirteen with time, correctly counts signed rails for at most three initial and three final positions. It does not bound the auxiliary arity independently of quantifier elimination, the rule, or the selected formula. The package implements an orbit accelerator, not a general rule-to-Presburger generator or quantifier-elimination/compiler implementation.

There is an immediate already-reviewed refinement, not a defect in the report: the [five-witness congruence truth atom](presburger_congruence_five.md) can replace its six-witness predecessor after elimination. This gives `K=2I+5C+B` while keeping `E=2I+5C+B+1`, the natural single-fold property and quartic degree. The congruence truth port is unchanged and the deleted remainder is canonically restored. Its separately charged local schedule saves one addition against its explicit old baseline. No concrete CA formula is emitted here, so this review makes no total-gate saving claim for an unimplemented rule compiler. The existence-only congruence variants would surrender the single-fold conclusion and must not be substituted under that claim.

## 6. Replays, independent evidence and API scope

All original Python scripts were read before replay. The fresh private runs execute:

- Four-mass `test_expanding_shuttle.py`, `test_binary_expanding_shuttle.py`, the three independent arithmetic/rule audits, and `test_exact_boundaries.py` in both normal and optimized Python.
- The revised single-unit `test_single_unit_acceleration.py` and `independent/audit_accelerator.py`; identical original sources are not redundantly rerun.

All nine generated JSON/export files match the sealed bytes exactly, not just Python's loose numeric equality. The binary boundary receipt is removed only inside the private tree before normal/optimized regeneration. Recorded author counts reproduced include 1,140,320 single-unit direct/accelerated comparisons over 7,127 actual cases and 23 sample rules, the separate 118,600 boundary comparisons, and the binary shuttle's 302,400 direct steps and 2,424 exact hits. The complete receipts retain all literal counters and source pins.

Additional independent checks pass:

- 8,192 guarded local-rule reconstructions and 8,192 potential edges.
- 2,493 complete binary orbit states, 107 huge boundary transitions, nine huge exact timing cases and 1,060 rational-root cases.
- 480 literal complete-quartic source evaluations, 46 malformed public-helper rejections and an immutable certificate snapshot check.
- Every one of the 45 plotted configurations and its CSV row; images are not regenerated.
- 19,773 signed least-hit interval cases, 11,400 complete states from independently evaluated elementary rules on 475 initial configurations, and 20 no-unit/radius-zero finite-state cases.

The binary public helper explicitly checks exact built-in integers, natural timing parameters, complete certificate dimensions/metadata and duplicate coordinates; it snapshots to immutable tuples. Its conservation verifier deliberately does not authenticate that an arbitrary valid table is the particular shuttle, and the docs correctly say so. The separate source pin and local-table comparison supply that identity here.

The single-unit accelerator is expressly an internal sample harness with unit label `u`. It is not advertised as a general validated external rule API; missing arbitrary-symbol renaming or malformed-input guards are not presented as theorem defects. The mathematical theorem is broader than the sample implementation, and that limitation is stated.

## 7. Primary-source check and remaining coverage limits

I directly retrieved [Kong's June 2021 thesis](https://hiroshima.repo.nii.ac.jp/record/2002360/files/k8621_3.pdf), SHA256 `d511dc3a28f62b7c610e0895c4d46a88cdd3c810f5f1f1e09b9baa0a42483fad`, and read the relevant pages. Definition 1 on printed page 8 explicitly uses the binary alphabet. Theorem 2 on printed page 14 states three-particle non-strong-universality using whole or componentwise eventual periodicity; printed page 15 describes the four-particle case as open **in that historical source**. This supports the revised attribution and does not establish the present weighted/uniform strengthening or current novelty.

The [official KAKEN project record](https://kaken.nii.ac.jp/grant/KAKENHI-PROJECT-17K00015/) and [official final report](https://kaken.nii.ac.jp/ja/file/KAKENHI-PROJECT-17K00015/17K00015seika.pdf) were retrieved. The PDF bytes have SHA256 `baa8f969487df129452f4e778b83616ee06b7ad800132a7d6e5ce720fd865b58`. However, local and browser text extraction omitted much of the Japanese body because of its font encoding. This review does not independently certify the exact Japanese decidability sentence or its underspecified decision problem. The package's cautious scope should be retained.

The fresh [IEEE publisher page](https://ieeexplore.ieee.org/document/7818615/) fetch did not yield the full paper or usable abstract. I therefore do not upgrade the package's expressly abstract-only five-particle upper-bound attribution into a checked full-paper theorem, or infer a binary five-particle upper bound. No literature priority or present-day open-problem claim is made here.

The full editable mathematical arguments were read; the general theorems are not mechanically formalized. The independent finite checks exercise actual implementations and explicit arithmetic, not all CA rules. There is no general four-mass section compiler in the package, and no new fixed universal arithmetic circuit is claimed.

## 8. Portable replay

The helper uses only the Python standard library. It authenticates archive bytes, rejects unsafe paths/symlinks/duplicate entries, authenticates every member, and verifies the supplied manifests before execution. Modules used directly by the independent checks execute from pinned source bytes with temporary module names restored afterward. Author subprocesses have bounded timeouts. It writes only private temporary extraction/output data and an explicitly requested receipt.

```
python review_batch80_low_mass.py \
  --archives /path/to/Proofs/docs/incoming \
  --expect review_batch80_low_mass.json
```

If archives have subsequently been placed and removed from the working tree, the helper can restore their exact pinned historical bytes without a Git mutation:

```
python review_batch80_low_mass.py \
  --repo /path/to/Proofs \
  --expect review_batch80_low_mass.json
```

The saved receipt has no timing fields or absolute workspace paths. The initial archive-mode run and a fresh Git-fallback replay both exercise the complete verification. No repository source, archive, or Git state is edited by this review.

## Integration replay

The root reviewer read the frozen mathematical note and complete portable checker,
then ran a fresh archive-mode replay with `--expect` and a new output file.
All nine author invocations and the independent checks passed. The root receipt
is byte-identical to the committed receipt. The three original archives and
all report sources remain unchanged.
