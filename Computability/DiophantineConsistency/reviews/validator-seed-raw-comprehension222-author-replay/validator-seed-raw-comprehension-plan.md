# Next finite source proof: augmented raw comprehension

27 October 2026. Read-only source/API and provider audit by circuit_reduction.
No Lean source, compiler invocation, overlay, dependency refresh, or Git
mutation is part of this packet. Basis has author and independent peer PASS
and is root accepted at commit `a9ee83d2c2`.

## 1. Recommended next pair and exact conclusion

Implement only `ZFCinPA.ValidatorSeedRawComprehension222` and its Checks,
importing `ZFCinPA.ValidatorSeedSourceBasis222`. The substantive endpoint is
a genuine internally coded source proof of

```text
∃b ∀z, z∈b ↔ z=a ∨ (z∈a ∧ θ(z))
```

for every internally typed unary matrix θ and every internal source term a,
with all free parameters retained. The extra member a is essential. This is
the exact `KLowerRaw.raw_aug` construction, proved in the concrete source
theory rather than inferred from its standard-model semantics.

Work under `[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`, with
`Source V := seedTheory.internalize V` and `L := ℒₛₑₜ`. Proposed endpoints:

```lean
rawAugMatrix (θ : Semiformula V L 1) (a r : Term V L) : Semiformula V L 2
rawAugBody   (θ : Semiformula V L 1) (a : Term V L) : Semiformula V L 1
rawAugProof  (θ : Semiformula V L 1) (a : Term V L) :
  Source V ⊢! ∃⁰ rawAugBody θ a
rawAugProof_isProof (θ : Semiformula V L 1) (a : Term V L) :
  Proof seedTheory (rawAugProof θ a).val (∃⁰ rawAugBody θ a).val
```

Provide literal total raw-code constructors for the matrix and conclusion,
their fixed Σ₁ graphs, and exact `.val` identities on typed inputs. The proof
constructor is a fixed finite composition of actual source proof rules and
the already represented `openSeedProof`; it takes no supplied ordinary proof,
proof search result, source-axiom image, or semantic premise. A separate fixed
Σ₁ graph for the entire resulting proof-code function is not part of the
claim unless explicitly established. Its actual internal `Proof` certificate
is required, not merely an external satisfaction theorem.

## 2. Literal bodies and capture-safe parameters

Write `#i` for a typed bound variable and `a↑↑` for `a.bShift.bShift`.
`θ[#0]` means the actual typed `θ.subst ![#0]` into the displayed arity;
this leaves every original free parameter unchanged. Matrix slot 0 is the
output y and slot 1 is the input x.

```text
rawAugMatrix θ a r :=
  ((#1 = r↑↑) ∧ (#0 = a↑↑)) ∨
  ((∀ ((#0 ∈ #2) ↔ (#0 = #1))) ∧
    ((#0 ∈ a↑↑) ∧ θ[#0]))

rawAugBody θ a :=
  ∀ ((#0 ∈ #1) ↔
       ((#0 = a↑↑) ∨ ((#0 ∈ a↑↑) ∧ θ[#0])))
```

The matrix's inner singleton quantifier has slots `(w,y,x)`; it therefore
says `Singleton(x,y)`, not `Singleton(y,x)`. In the conclusion the inner
universal slots are `(z,b)`. These are literal typed formulas, with NNF
implication/iff expanded by the existing source connectives.

Define `rawAugAt θ a b := (rawAugBody θ a).subst ![b]` and prove:

```text
(rawAugMatrix θ a r).shift = rawAugMatrix θ.shift a.shift r.shift
(rawAugBody θ a).shift = rawAugBody θ.shift a.shift
(rawAugBody θ a).free = rawAugAt θ.shift a.shift (fvar 0)
```

Also expose the exact matrix instantiation at arbitrary terms y,x. Every
existential eigenvariable step shifts θ and every ambient term together.
There is no assumption `θ.shift=θ`, finite free-variable bound, fresh numeric
parameter, or standardness of θ. The semantic guide's `shiftAfter 2` is
replaced by the actual typed substitution above, not by an unproved renaming
equivalence. Source terms have no function symbols and their bound arity is
zero, so the existing `term_is_fvar` can discharge term-lifting identities.

## 3. Concrete finite derivation and the needed public helper

The full-seed body is already literal and available through `openSeedProof`.
Its two-binder remainder can be named in this new namespace and bound by
definitional equality to the existing `fullSeedBody`. No accepted source is
edited. The private `pairMatrix` and `pairAt` helpers in Basis are not usable
imports and must not be cited as public APIs.

From that exact remainder derive source implications for support, request,
and the following **full member-closure projection**:

```text
Pair(K,A,C) → y∈C →
  ∀p (p⊆y → ∀v (K(v,p) → ∃z (K(z,p) ∧ z∈C)))
```

Here `p⊆y := ∀w(w∈p → w∈y)`. The subset is of the member y, not of the
existential input witness in the support clause. This projection is the new
part not supplied by Basis's private support/request lemmas. Derive it by
eliminating the support witness while retaining its entire closure conjunct.
Retain the actual five matrix substitution vectors from `fullSeedBody`.

The augmented comprehension proof then has these finite steps:

1. Use `singleton_object a` to introduce r with `Singleton(r,a)`. Instantiate
   `openSeedProof (rawAugMatrix θ a r)` at root r to obtain its container C.
2. The request at output a has its first disjunct by reflexivity. Every
   returned matrix witness is a: its first branch states equality to a;
   in its second branch `Singleton(r,z)` and `Singleton(r,a)` give z=a.
   Atomic membership transport therefore gives a∈C in both branches.
3. For any z∈C, support yields some x and the matrix at z,x. Its first branch
   gives z=a; its second branch directly gives z∈a and θ(z). No rewriting
   inside the arbitrary formula θ is needed.
4. For z∈a and θ(z), use `singleton_object z` to introduce p={z}; atomic
   equality transport proves p⊆a. Apply the full closure at **member a** to
   p and output v=z. The second matrix branch is then established literally.
5. Closure returns z'∈C with the matrix at z',p. Its root branch p=r forces
   z=a by singleton uniqueness and also states z'=a, hence z'=z. Its
   singleton branch directly forces z'=z. Membership congruence gives z∈C.
6. Reintroduce the universal and existential binders with shifted contexts,
   eliminating the singleton and seed containers by actual source rules.

Required equality helpers are finite specializations of seedTheory's actual
reflexivity, symmetry, transitivity and membership-congruence axioms. They
do not equate source equality to numeric
`weq` or to the later tagged-profile `Eqv`. The argument uses no arbitrary-θ
equality-congruence theorem, so no new internal formula induction is needed.
The source logic is classical; this is not an HA derivation claim.

This overlap simplification is already visible in the retained semantic
`raw_aug_core` in
`Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/common-macros/lean/overlay/BusyBeaver/ZFC/KLowerRaw.lean`.
It is read as an inert proof guide and is not imported or executed. It shows
that this particular finite derivation need not use seedTheory's
irreflexivity axiom. The later tagged construction still has its actual
empty-marker and irreflexivity obligations. No stronger source theory or
new semantic premise is being assumed.

## 4. Why the existing compiler does not remove this proof obligation

The complete relevant APIs were read:

- `OpenSetTemplateCompiler.compileOpenTemplate` and `_isProof` transport a
  fixed actual ordinary proof to internally typed placeholder matrices. Their
  callback requires genuine source proofs of each used axiom at **every**
  shifted predicate family. They do not supply the raw-comprehension proof.
- `OpenTemplateClosure.closeTemplate` closes the finite ordinary template
  parameters while retaining arbitrary free parameters in the substituted
  internal matrices. Its `generalizeAll`/`closure_opening` machinery is valid
  here; there is no need to force a shift-fixed placeholder.
- `BufferedTemplateProofCompiler.compileProof` accounts for each ALL/SHIFT
  step of a fixed proof using its finite buffer. It is not an interpreter of
  arbitrary internally sized source proofs and has no seed axiom oracle.
- The older `SetPlaceholders.compileSetTemplate` requires shift-fixed
  placeholders. It is unsuitable for an arbitrary θ with free parameters.

There is no existing ordinary raw-augmented proof template to feed to this
compiler. Authoring a finite standard derivation and then its concrete
shifted-axiom callbacks would duplicate the same finite argument at this
checkpoint. The direct typed template above is smaller and retains the exact
internal source proof output. The buffered compiler remains a legitimate
later consumer when a family of already proved ordinary templates warrants
it. No semantic completeness theorem is used to manufacture such a proof.

## 5. Exact subsequent guarded target, not part of the first pair

The raw result is not exact separation. The subsequent finite proof pair
would first establish raw pairs and the exact two-root construction

```text
Empty(t) ∧ B≠t →
  ∃S ∀z, z∈S ↔ z=B ∨ z=t ∨ (z∈B ∧ θ(z)).
```

`KLowerRaw.raw_tagged` uses r={B,t} and the literal matrix
`(x=r ∧ y=B) ∨ (x=t ∧ y=t) ∨ (Singleton(x,y) ∧ y∈B ∧ θ(y))`.
The two distinct roots exclude singleton/empty-input collisions. Raw pair
itself is another finite full-seed instance, not yet provided by Basis.

The exact guarded conclusion in the unchanged source language is

```text
Empty(t) → ∃S (t∈S ∧ ∀z (t∈z → (z∈S ↔ z∈U ∧ θ(z)))).
```

Its one-slot body for S is literally

```text
(t↑ ∈ #0) ∧
∀ ((t↑↑ ∈ #0) → ((#0 ∈ #1) ↔ ((#0 ∈ U↑↑) ∧ θ[#0]))).
```

There is no U≠t premise. The U=t branch uses the singleton of t. Otherwise
the augmented envelope `E={U}∪{z∈U | t∈z}` satisfies E≠t and t∉E. Apply
the two-root construction to E with predicate `z∈U ∧ θ(z)`. Its extra
members E and t fail the guard `t∈z`, giving the displayed exact result.
This follows the actual `KLowerTag.dt_comp` proof, including its exceptional
U=t branch. No `interpretedMember=rawmem` identification is asserted.

This guarded finite proof would still leave the represented marker-reserving
formula interpreter, arbitrary tagged Collection, profile equivalence,
quotient/WF transfer, and internal ZF proof transformation open. In particular,
`KLowerTag.tag_sep` also uses `relT` and `swap01`; their standard semantic
lemmas do not supply an all-internal syntax/proof transport. The accepted
QHyp route and the existing later ZFC-to-ZF reduction remain the intended
route; neither raw CP/GIC nor an extra Choice assumption replaces them.

## 6. Focused checks and provider boundary

Checks should include arbitrary internally typed θ and source terms; exact
raw-code/typed bindings; the actual internal `Proof` certificate; θ=⊥
(singleton-shaped augmented result), θ=⊤; nested θ binders; free indices 0
and a sparse internal parameter; simultaneous θ/term shifts; and the exact
member-closure projection. Repeated free labels are allowed. No smaller
finite-model experiment substitutes for these uniform statements.

The freshly rehashed plan has two explicitly separated inventories:

| Branch | Cached modules | Foundation | Artifacts | External boundaries |
|---|---:|---:|---:|---:|
| Recommended sole Basis import | 201 | 136 | 609 | 45 |
| Optional Basis + OpenTemplateClosure | 209 | 136 | 617 | 45 |

The recommended branch's **246 actual first providers** all match their
selected hashes. The optional branch's eight additional records are each
authenticated, but a broad existing search path shadows the selected
`BoundedPAConsistency.TypedTemplateProofCompiler` object with a different
object in the shared build directory. That optional search path is explicitly
not build-ready; a selected-only private overlay would require separate
authorization. No shadowing affects the recommended branch.

Selected Basis provider:
`/tmp/validator-seed-source-basis222-controller-peer-81rcdk9o/lib`.
Main source `89cb03dae589494db007f42b030d9234613c4e02f35d91307a1bfcd3acdd8c03`;
main object `b386be3407776eded2b468241fd7bdd41528fe87345bbae6f360c7f37bf8df22`.
Peer receipt `82a0c17266176139f61b906fd4e5aff4acff503477a04b84b43b87ea24b31a66`.
Root acceptance receipt SHA256 is
`8dd67cba89edacc64991ae2b72cf033fbf340382e9e4f41bc2f7789be5945e85`;
its authentication manifest is
`88780ae02de0f36dc2a790a7097cd11083c70383f10f14695762b01fcf30cb7a`.
The accepted FullSeedTheory source/object and all inherited historical trace
and absent-companion qualifications remain unchanged.

The cache plan JSON is
`validator-seed-raw-comprehension-cache-plan.json`, SHA256
`1a7e1996851c977c43da4b641adb79dbbc1f18ff5133ac87d9aefee1cffd8175`.
It records the exact reachable current headers, dependency order, all selected
sources/objects, explicit package/toolchain boundaries, source anchors and
**1,188 rehashed observations**. No compiler was invoked. The original
tagged-source plan remains frozen.

The read-only auditor's first attempt treated the peer summary's file count
as a list; its second attempt deliberately stopped on the optional shadowed
provider. The successful v3 inventory is retained with its then-pending root
status. Adding root acceptance first exposed the different repository-relative
path convention in ROOT's manifest (v4), then the root-pinned audit passed
(v5). The final audit additionally pins the retained overlap-proof guide. All
original drivers and diagnostics are preserved. The final inventory distinguishes
optional non-build-ready lookup from the fully matched recommended scope.
These were planning-metadata diagnostics, not Lean/source failures. No files
outside this new planning packet changed.
