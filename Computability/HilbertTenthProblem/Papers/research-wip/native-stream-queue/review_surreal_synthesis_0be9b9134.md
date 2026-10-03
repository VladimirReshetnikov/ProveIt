# Bounded review of the assembled surreal well-orders synthesis

Reviewed publication commits `d51fafea806cbd48ba29be017eff85cdd9653b14` and `0be9b913487fa2cc0e16cea6545c55f33b4446d8`. Result: two minor new prose findings, with a private three-location correction patch. No additional mathematical defect found in the new synthesis under its stated hypotheses. This is a scoped written review, not a formal verification of the transfinite results.

The target is `Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/`. The final article pin is SHA256 `728573d68da543e25ee8d0f7d37f9d75410695ce5196702336e71e4a7928b503` (Git blob `f20837b76f8d981cb1dce3da79f633e280edad41`); README is `8fc8b16c54a45cab946f383ee47b9f87b31b105939e0d65f681c88a1f1a6a568`. The companion receipt pins both publications' article, README, `Algebra/SurrealNumbers/docs/NOTATION.md`, and the applicable `Algebra/SurrealNumbers/AGENTS.md`.

## Read scope and separation of work

I read the applicable AGENTS, all 98 newly authored `hand chunk` blocks (2,061 source lines, including the bibliography), the complete new README, and the 21-line NOTATION addition. This covers the abstract, introduction, status, notation crosswalk, all newly written duplicate-result notes and route comparisons, choice/class-recursion summaries, model comparisons, formalization status, research-question annotations, and reproducibility notes. I also read the altered question passages outside those chunks and the original proof contexts needed to assess them: the GB choice recursion, both support-code definitions, the labelled comparison, regular-cutoff saturation, and the KM nonembedding proof. The remaining original theorem proofs were already reviewed in `review_batch80_surreal.md`; they were not rerun as a whole-book audit here.

The separate preservation reviewer owns the ordered source/transcription census, the 166-statement crosswalk, archive/companion inventory and exact transfer coverage. This note checks the mathematical meaning of the new notes, including those replacing duplicate proofs; it does not independently certify every copied symbol or crosswalk entry. No original author suite, Lean build, or PDF inspection was repeated. No repository file or Git state was changed.

## Findings and exact correction

**P3: “coherent” overstates the actual rank recursion.** At final article lines 3640 and 7336, the new commentary says the proof produces a coherent sequence of well-orders of `V_alpha`, or a coherent well-ordering of successive power sets. The proof at lines 3489–3526 uniformly defines each order, but does not assert or prove that later orders restrict to earlier ones.

There is an exact finite counterexample within the stated construction. Choose the input class well-order `W` so that its one-sign restriction is `- < +`, and its two-sign restriction begins `+- < --` (complete that layer as `+- < -- < ++ < -+`). These finitely specified layer orders can be extended to a class well-order, for example by birthday layers under Global Choice. The proof then gives

- `w_2`: `empty < {empty}`, because their one-sign membership codes are `-` and `+`;
- `w_3` restricted to `V_2`: `{empty} < empty`, because their two-sign codes are `+-` and `--`.

Thus compatibility under restriction fails already at finite stages. The original global-choice proof is sound: it needs only the uniformly defined `w_rank(A)` to select an element of each nonempty set `A`. Its successor stage uses the unique enumeration of an already specified set well-order, and its limit stage uses ranks. No coherent extension system or additional choice is needed. The patch says “uniformly defined sequence” and “uniform well-ordering” at the two new claims; it preserves the original question's request to compare with coherent systems.

**P3: the largest-file qualification omits PDFs.** README line 82 calls 126,780 bytes the largest delivered file. The independent authenticated four-archive inventory gives 543,575 bytes for the largest delivered file (source 11's PDF), while 126,780 is exactly the largest non-PDF file (source 11's TeX). The patch inserts “non-PDF”; it changes no delivery/omission claim. That inventory evidence belongs to the companion preservation review, rather than to this helper's mathematical checks.

`review_surreal_synthesis_0be9b9134.patch` contains only those three replacements in two files. Private `patch --batch --fuzz=0 -p1` dry-run and application both passed on the final pinned publication. The helper additionally compares the entire patched bytes to those exact three substitutions. Patch SHA256:

`0004ce2f78d1ebd1f5986948077ca1a70488a1793bb4b9bf67cc088f639aa839`.

Patched article SHA256 `22d164f31c4fd29f1154689d811b32836eeec9ec5918c0ea8acf1784619dc380`; patched README `526788392b329a02674563048e2af9f3ff005e9a9a508fefb926d3a79bf276c2`.

## Mathematical scope checks

The choice summary correctly strengthens the sources 09/12 `GB + AC` statements to source 11's theorem over GB without a choice axiom. An arbitrary class well-order of sign-sequence surreals, a set-like one, a class bijection from Ord, and Global Choice are equivalent there. The chosen class parameter remains part of the construction; this does not prove parameter-free definability of a global choice function. The new weak-choice question is answered in that sense. Its separate warning that order universality itself need not imply the same choice principle is retained.

The support-code crosswalk is an actual inverse equivalence for a fixed baseline, not merely equality of isomorphism types. For a fixed-point-free permutation of an ordinal support set `S`, extend by the identity to `lambda = sup{xi+1 : xi in S}`. This is a normalized permutation of `lambda`; `S` is invariant and hence so is its complement. Conversely, remove fixed points from a normalized ordinal permutation. These operations are inverse (including the empty code), and their identity extensions have identical evaluations against the same baseline. There is no claim that arbitrary different baselines give identical code classes, or that an order isomorphism preserves birthdays, simplicity, field operations, or permutation composition. The new README/NOTATION text respects those boundaries. The helper checks 874 finite permutation presentations as a regression for this explicitly proved correspondence; those tests do not establish the transfinite result.

The source 08 fixed-relation well-foundedness correction is accurately transferred. Over GBC, a fixed class relation is internally well-founded exactly when it has no set-coded descending omega-sequence. Holding the sets and relation fixed therefore holds that truth value fixed between GBC class expansions. What may change is which class relations exist; external well-foundedness is a further question. This is distinct from making that absoluteness claim for arbitrary weaker theories, or from saying the available-class collection itself cannot matter. The original proof review already checked the relevant primary discussion in Hamkins–Woodin, *Open class determinacy is preserved by forcing*, Sections 2–3 ([arXiv:1806.11180](https://arxiv.org/abs/1806.11180)); no new literature-status claim is being made here.

The assembled notes consistently distinguish set-valued Ord recursion, which uses a set-sized previous history at each set ordinal, from class-valued recursion and ETR. The newly “answered” source 08 comparison question is answered by comparison of labelled relations on a fixed labelled carrier. The explicit note at lines 4453–4468 preserves the warning about alignment or initial-segment comparison of abstract class domains. It does not claim that the labelled construction proves general abstract order-type comparability in GBC.

The KM nonembedding statement remains a schema for each fixed formula defining a total unique class transformation, with fixed set/class parameters. Its inverse evaluator quantifies over a class and uses impredicative comprehension. It is not a theorem excluding arbitrary external maps between a nonfull model's available-class collections. Likewise, the full model `(V_kappa, P(V_kappa))` assumes ambient ZFC and strongly inaccessible kappa; the singular example `beth_omega` is not substituted for that model hypothesis.

The singular/regular crosswalk states equimorphism or binary coding length, not isomorphism. Source 12's dichotomy answers only the specified minimal-slice coding question; the new question-status notes leave the requested cut spectra, point characters, longer enumeration types, and broader classification questions open. Source 11's regular eta-kappa theorem is used with its regularity and alphabet-size hypotheses. The crosswalk explicitly keeps binary cubes with endpoints/jumps distinct from saturated permutation orders.

Finally, ordinary class carriers, virtual predicates on class variables, and uniform families given by one class relation remain distinct. The no-uniform-evaluator diagonal theorem forbids an exhaustive same-level family of all class enumerations. It neither establishes Turing completeness nor supplies a finite arithmetic evaluator, a fixed-arity Diophantine representation, or an operation reduction for a universal equation. The new formalization prose describes possible modules and relevant existing primitives, and does not claim the report theorems have been checked in Lean. The mathematical interest for the Diophantine work remains a size/uniformity caution, not a new computational substrate.

## Reproducible bounded receipt

The portable helper reads only the two pinned Git objects, authenticates all eight selected object bytes, records the 98 editorial-chunk ranges/hashes, reconstructs the three finite successor stages giving the coherence counterexample, checks 874 finite support-code round trips, and tests the exact patch on a private temporary copy. It performs no source-code imports and has no fixed worktree or scratch dependency. Saved receipt comparison is recursive and type-sensitive. Fresh replay passed.

From a directory containing the helper, patch and saved receipt:

```sh
python review_surreal_synthesis_0be9b9134.py \
  --repo /path/to/Proofs \
  --patch review_surreal_synthesis_0be9b9134.patch \
  --output /tmp/surreal-synthesis-replay.json \
  --expect review_surreal_synthesis_0be9b9134.json
```

This finite receipt authenticates the reviewed inputs and concrete regression. The written arguments above provide the transfinite scope analysis; the finite checks are not substitutes for those arguments or for the separate preservation census.
