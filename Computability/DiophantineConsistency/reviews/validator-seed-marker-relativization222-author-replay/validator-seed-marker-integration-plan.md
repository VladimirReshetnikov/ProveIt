# Actual moving-marker proof transport after tagged Collection

27 October 2026. Read-only proposal, not a new theorem. No Lean source,
overlay, compiler invocation, dependency refresh, or cache mutation was made.
The paired JSON authenticates the proposed inputs and records the exact
dependency graph. The frozen Collection sources and evidence are untouched.

## 1. Recommended next pair and its exact boundary

Implement `ZFCinPA.ValidatorSeedMarkerRelativization222` and Checks, importing
only `ZFCinPA.ValidatorSeedMarkerDischarge222`. The first tagged stage retains
raw equality and membership. Therefore the existing represented construction
`InternalRelativization.relativize` is the exact operation needed. There is
no reason to introduce a second recursion or import the more general
`InternalInterpretation.interp` before quotient atom meanings are required.

For every arithmetic model of IΣ1, define the following abbreviations of
existing actual codes (all variables here range over the internal model):

```text
d(j) = MarkerDischarge.domainCode j       -- &j ∈ #0
E(j) = neg (MarkerDischarge.emptyCode j)  -- ¬Empty(&j)
C(j) = MarkerDischarge.sideSet j
R(j,p) = relativize ℒset d(j) p
S(j,s) = relSet ℒset d(j) s
Q(j,s) = insert E(j) (S(j,s) ∪ C(j)).
```

Use the same `seedTheory` as SourceBasis/FullSeedTheory, not an assumed
raw CP/GIC theory. For a source `T : SetTheory` with its actual `T.Δ₁`
instance, keep the precise axiom-image resource explicit:

```lean
hAx : ∀ p j : V, IsFormula ℒset p → p ∈ T.Δ₁Class → p < j →
  Derivable seedTheory (insert (R j p) (insert (E j) (C j)))
```

The main new target is a genuine bounded proof-code induction:

```lean
derivable_tagged_bounded (B : V) (hAx : ...) :
  ∀ der : V, Derivation T der → ∀ j ≤ B,
    der < j → der + j ≤ B → Derivable seedTheory (Q j (fstIdx der))
```

Then export the same theorem for every `j > der` by taking `B=der+j`,
and a refutation theorem:

```lean
provable_falsum_of_tagged (hAx : ...)
  (h : Provable T (^⊥ : V)) : Provable seedTheory (^⊥ : V)
```

At a source refutation choose its actual internal derivation code `der`
and `j=der+1`. Its interpreted singleton sequent is falsum, so an explicit
set equality turns `Q j {falsum}` into MarkerDischarge's `residual j`.
Apply the now independently accepted `provable_falsum_of_residual`.
Under IΣ2 the already imported
`ValidatorFullSeedTheory222.seedTheory_refutation_witness` then yields
`∃ d, ArithmeticHistory222.value d = 2`, still with exactly `hAx` explicit.
This optional last composition is an actual C222 witness, not a claim that
ZF/ZFC supplies `hAx` yet.

This is a new logical proof-transport theorem, not a supplied proof-map
premise. Its axiom-image premise is the remaining mathematical interface
to be discharged for a concrete tagged theory. It is not an assertion of
the final source-ZFC/checker equivalence or of the HA equation theorem.

## 2. Existing APIs remove most of the preliminary syntax work

`InternalRelativization.lean` already provides the total fixed Σ1 graph
`relativizeGraph`, all eight constructor equations, and the following laws
without any shift-fixedness hypothesis:

- `isSemiformula_relativize` and `isFormulaSet_relSet`;
- `relativize_neg`;
- `relativize_subst`, `relativize_substs1`, and `subst_qVec_domain`;
- `relSet.definable`, membership, insert and subset laws;
- `domF_mem_domSet` and typed side-set facts.

New laws are only the changing-domain ones:

```text
shift (R(j,p)) = R(j+1, shift p)
free (R(j,p)) = R(j+1, free p)           [p has bound arity 1]
setShift (S(j,s)) = S(j+1, setShift s)
shift E(j) = E(j+1).
```

For the first law, use the existing eight-case internal formula induction,
with the actual `shift_domain j` at the two quantifier cases. Do not call
the old `relativize_shift`, whose hypothesis fixes the domain. The free
law follows by the definition of `free`, the new shift law, and the existing
arbitrary bound-substitution theorem. No free variable of the source matrix
is discarded, and no source matrix is restricted to standard size.

MarkerDischarge already proves the exact side-set equation:

```text
C(j+1) = insert (free (neg d(j))) (setShift C(j)).
```

It also proves all empty/domain typing and shifts, `residual_succ`, and the
arbitrary internal-length discharge. Reuse those statements unchanged.

The set-language term classification is already in the selected closure:
`ValidatorSeedSourceBasis222.term_is_fvar`. Wrap an arbitrary raw
`IsTerm ℒset t` code as a typed `Term`, apply that theorem and take `.val`
of its equality. This gives `∃ i, t=^&i`. It needs neither another induction
nor a `SetRelativization` import. Our initial read-only import estimate
considered that extra historical module; ROOT pointed out this smaller
existing typed API before the inventory was frozen.

## 3. All ten actual derivation cases, with the internal budget

The constructors are exactly `Foundation...Syntax.Proof.Basic`'s
`Derivation.case_iff`, lines534–547. Fix `B`; the induction predicate is

```text
Derivation T der → ∀ j ≤ B,
  der<j → der+j≤B → Derivable seedTheory (Q(j,fstIdx der)).
```

`Derivation` is Δ1; the one new universal counter is bounded; comparisons
are arithmetic; and the total represented sequent functions compose with
Σ1 `Derivable`. Thus the required definability proof follows the actual
`HierarchySymbol.Definable.imp/ball_le` construction in
`ModelCodedProofRenaming.derivable_rename_bounded`. That module is a fully
read proof guide only, not a proposed import. Use genuine
`ISigma1.sigma1_order_induction` and `hd.case` with actual strict child-code
bounds, rather than metatheory induction over internally sized derivations.

| Actual constructor | Child counter and exact proof step |
|---|---|
| `axL s p` | No child. `Derivable.em` at `R(j,p)`, with `relativize_neg`, membership and well-typed `Q`. |
| `verumIntro s` | No child. `relativize_verum` and `Derivable.verum`. |
| `andIntro s p q dp dq` | Both children at `j`; `dp_lt_andIntro`/`dq_lt_andIntro` decrease the budget. Rewrite insert images and apply `Derivable.and_m`. |
| `orIntro s p q dpq` | Child at `j`; `d_lt_orIntro`; rewrite both inserted formulas and use `Derivable.or_m`. |
| `allIntro s p dp` | Child at `j+1`; `s_lt_allIntro` says `dp<parent` despite its name. Hence `dp+(j+1)≤parent+j≤B` and `dp<j+1`. The child's `R(j+1,free p)` is `free R(j,p)`; its side set contributes exactly `free(neg d(j))` plus the shifted parent side set. Combine these two opened formulas by OR, and use actual `Derivable.all_m` at `∀(neg d(j)∨R(j,p))`. The Empty guard shifts with the marker. |
| `exsIntro s p t dp` | Child at `j`; `d_lt_exsIntro`. Classify `t=^&i`. The precise chain is `i<^&i=t<exsIntro s p t dp<j`, using `var_lt_qqFvar` and `t_lt_exsIntro`. Therefore `domF d(j) i∈C(j)`. An excluded-middle source derivation supplies the positive domain conjunct at that witness; combine it with the translated child using AND, then `Derivable.ex_m`. This is ordinary classical source logic, not an HA rule. |
| `wkRule s dp` | Child at `j`; `d_lt_wkRule`; `relSet_subset` and unchanged guard/side set. |
| `shiftRule s dp` | Write positive `j=k+1` using internal `zero_or_succ`. Parent<j implies parent≤k, so `dp<parent≤k`; use child counter `k`. Its budget is smaller. Shift its derivation, apply the new family sequent/guard laws, then weaken `setShift C(k)` into `C(k+1)`. No subtraction/truncated-predecessor convention is needed. |
| `cutRule s p dp dn` | Both children at `j`; `d₁_lt_cutRule`/`d₂_lt_cutRule`; `relativize_neg` identifies the actual two cut formulas. |
| `axm s p` | No child. `p_lt_axm` and parent<j give p<j. Apply the exact `hAx`, then weaken its formula into the interpreted source sequent. |

For the ALL bound, internal discreteness gives `dp+1≤parent`; associativity
gives `dp+(j+1)≤parent+j`. For SHIFT, parent<j ensures the successor split
is nonzero and the child remains strictly below its smaller marker. These
are model arithmetic inequalities, not external Nat calculations.

The chosen side set contains *every* free label below `j`, including labels
not actually used. This is why EXS needs only the existing code inequality,
not a new global free-variable support oracle. The marker's own label is
excluded. CUT, ALL, and SHIFT are covered explicitly; no unrestricted GEN
rule for open resources is smuggled into the invariant.

Focused Checks should retain arbitrary internal `T`, typed nested formulas,
the changing-domain shift/free laws, raw-to-typed witness classification,
the EXS strict bound, ALL's successor budget, SHIFT's predecessor budget,
the exact residual singleton equality, and the conditional C222 value2
composition. A standard finite example alone cannot test the code induction.

## 4. How the frozen Collection theorem will supply an actual image

Collection is still candidate author-PASS pending independent ROOT acceptance
at this proposal's freeze. Its actual theorem has the source conclusion

```text
Empty(t) → t∈a → ∃c,
 t∈c ∧
 (∀y, t∈y → y∈c → ∃x, t∈x ∧ θ(y,x)) ∧
 (∀x, t∈x → x∈a → (∃y,t∈y∧θ(y,x)) →
                         ∃y,t∈y∧y∈c∧θ(y,x)).
```

The support witness `x` is unrestricted by `a`. This is the exact global
image requirement used in `KLowerTag.tag_collection`, not a weakened
collection statement. `taggedCollectionProof_isProof` is an actual source
Proof certificate; `collectionConclusionCode_eq` binds the total raw syntax
graph to the typed theorem. Arbitrary internally typed matrices and their
free parameters survive its replacement and binder operations.

The next image-binding task after the proposed transport is concrete:
take the actual existing `LeanProofs.ZFCinPA.gicBody K` skeleton from
`NativeGicDelta1.lean` (input slot0, output slot1). For `R(j,K)` of bound arity2, Collection's matrix must be
`θ=(R(j,K)).subst ![#1,#0]`, since Collection uses output slot0/input slot1.
After the new substitution/free laws, Collection and ordinary source
propositional rebracketing derive

```text
Provable seedTheory (Empty(&j) → R(j,(gicBody K).val)).
```

Closing the outer source `∀a` uses the `j+1` opened marker and shifted
matrix/parameters; it cannot be replaced by a fixed-marker GEN. Nor is the
displayed target definitionally identical to Collection's parenthesized
typed body: the proof must preserve the support/coverage permutations,
the outer tag guard, and the actual NNF implication spelling.

That open-body image still does not discharge an arbitrary internally
recognized closed schema. It needs the actual recognizer's internal
universal-closure count, matrix extraction, and a moving-marker closure
proof retaining `E(j),C(j)` and all free parameters. Existing
`NativePeel.peel` requires a shift-fixed `Good` parameter and is not a
shortcut. This image/recognizer pair is separate from the recommended
logical transport pair; importing the whole `NativeTheory` is unnecessary
and would incorrectly suggest its raw power-container axiom is available.

## 5. Actual remaining source axioms and the ZF/ZFC boundary

The immediate raw tagged interpretation leaves equality/member atoms
unchanged. Its genuine axiom-image obligations include actual equality
axioms (with guarded quantifiers and domain parameters), irreflexivity,
the Collection schema above, separation, tagged pairs, raw union and
transitive-bound constructions. The existing finite source results give
ingredients for these; they do not yet give all images under a uniform
recognized arbitrary-closure axiom predicate.

The ultimate source theory must match the QHyp route. Its additional
fields are exactly `KQHyp.QHyp`: GIC; profile `Eqv` reflexivity, symmetry,
transitivity and extensionality; profile pairs; interpreted union;
interpreted power; and singleton-closed containers. The latter three use
interpreted `Member`/`Eqv`. Tagged raw membership must not be silently
identified with interpreted `Member`; source equality interpreted by C222
`Eind` must not be identified with profile `Eqv` either.

`KLowerEqv` and `KLowerQHyp.tag_qhyp` currently prove the semantic
implications for ordinary Lean structures and ordinary formulas.
`KQ1ZF.zf_consistent` then forms the quotient and its WF part. Their
contracts tell us which finite syntactic proof templates and uniform
schema transport are needed. They do not supply arbitrary nonstandard
proof-code transformations. In particular the tagged domain need not
satisfy NativeTheory's literal power-container axiom. Therefore
`NativeSchema.provable_falsum_native_of_ZF` cannot replace this missing
QHyp/WF interpretation.

After those actual images and quotient/WF interpretation have been proved,
the retained all-internal Choice reduction is already available:
`LSchema.provable_falsum_ZF_of_ZFC` maps actual internal ZFC refutations
to ZF refutations in every IΣ1 model. Its exact source is pinned; there is
no need for a new standard-Nat Choice argument. Combining the future
ZF-to-seed bridge with FullSeedTheory's existing IΣ2 value2 endpoint is
the substantive source-ZFC→actual checker target. This proposal does not
assert that bridge, internal runtime calibration, Pell witness transfer,
or the final HA proof existence result.

## 6. Exact proposed dependency/provider scope

The read-only auditor passed its first execution. It rehashed 3,812 paths
and validates headers including `public meta import Aesop`, reachable
dependency order, all selected object/companion hashes, explicit boundaries,
and actual first artifact providers. It runs no compiler and creates no
overlay. The dependency inventory JSON has SHA256
`37aa5cc528c0dd4de6cde821a76610f9ddc055a9b5aace5690706b5688003cc1`.

| Proposed scope | Cached modules | Foundation | Custom artifacts | External boundaries | First artifact providers |
|---|---:|---:|---:|---:|---:|
| Recommended sole MarkerDischarge import | 203 | 136 | 611 | 45 | 656 |
| Later union with candidate Collection, before adding any future new leaf | 210 | 136 | 618 | 45 | 663 |

There are zero prerequisite refreshes. The recommended pair would create
only its two new regular outputs after separate approval. The hypothetical
later union is an inventory, not authorization to implement an axiom theory
or a quotation/recognizer bridge. Imports such as NativeGicDelta1 would need
their own reviewed delta before that later implementation.

Marker Discharge now selects the independently accepted provider
`/tmp/validator-seed-marker-discharge222-peer-od4hik4p/lib` directly.
Its main source is `7938f606…`, object `f0bc3b2d…`; peer packet
`e7ffbe74…`, 14-file manifest `54a4ee98…`. The original author packet and
all historical failures remain pinned. The current marker-counter proposal
file itself is `081cafbc…`; `a56ed75c1a` in the task is the earlier commit
reference, not the source-file hash recorded by this audit.

The Collection candidate selects
`/tmp/validator-seed-tagged-collection222-author-3wmh9dnm/lib` only in the
separate candidate branch. Source `7a05c987…`, object `38d1ac2e…`, author
packet `0c06fbab…`, 57-file manifest `000e1087…` remain provisional for
independent acceptance. A later accepted provider requires a separately
pinned selection update; these historical proposal bytes should stay fixed.

The accepted historical InternalRelativization source/object/run and absent
companion qualifications are preserved. Reading and hashing it here does
not relabel it freshly compiled. SetRelativization, InternalInterpretation,
ModelCodedProofRenaming, NativeGicDelta1, NativeTheory, NativeSchema, LSchema,
and the KLower/QHyp sources are pinned **source anchors**, not extra imports
of the recommended pair. Full source/object/provenance records and the
exact cached external paths are in the JSON. Before any future execution,
rehash those inputs and preserve the existing compiler/toolchain settings
and 512MiB disk reserve.
