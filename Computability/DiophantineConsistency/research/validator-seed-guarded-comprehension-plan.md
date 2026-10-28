# Source pairs, two roots, and guarded comprehension

27 October 2026. Read-only mathematical/API and provider plan by
circuit_reduction. No new Lean source, compiler invocation, overlay,
dependency refresh, or Git mutation is part of this planning packet.
RawComprehension has frozen author PASS; independent root acceptance is
pending at this plan's freeze. Its frozen source is not changed.

## 1. Recommended next coherent proof pair

Propose `ZFCinPA.ValidatorSeedGuardedComprehension222` and its Checks, with
the sole import `ZFCinPA.ValidatorSeedRawComprehension222`. The new module
would establish actual internally coded source proofs of raw pairs, the
two-root construction, and finally guarded comprehension over an arbitrary
raw bound. This is a finite proof template, not an arbitrary-source-proof
interpreter or a model-theoretic completeness argument.

Use the exact existing assumptions and source theory:

```lean
{V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
Source V := ValidatorFullSeedTheory222.seedTheory.internalize V
```

For arbitrary internal `Term V ℒₛₑₜ` parameters `t,x,y,B,U` and internally
typed `θ : Semiformula V ℒₛₑₜ 1`, the proposed primary statements are:

```lean
raw_pair_of_empty (t x y : Term V ℒₛₑₜ) :
  Source V ⊢ emptyAt t 🡒 ∃⁰ rawPairBody x y

raw_pair (x y : Term V ℒₛₑₜ) :
  Source V ⊢ ∃⁰ rawPairBody x y

raw_two_root (θ : Semiformula V ℒₛₑₜ 1) (B t : Term V ℒₛₑₜ) :
  Source V ⊢ emptyAt t 🡒 ∼eqTerm B t 🡒 ∃⁰ twoRootBody θ B t

guarded_comprehension (θ : Semiformula V ℒₛₑₜ 1) (U t : Term V ℒₛₑₜ) :
  Source V ⊢ emptyAt t 🡒 ∃⁰ guardedBody θ U t
```

Their literal meanings are respectively:

```text
Empty(t) → ∃p ∀z, z∈p ↔ z=x ∨ z=y;
∃p ∀z, z∈p ↔ z=x ∨ z=y;
Empty(t) → B≠t → ∃S ∀z, z∈S ↔ z=B ∨ z=t ∨ (z∈B ∧ θ(z));
Empty(t) → ∃S (t∈S ∧ ∀z, t∈z → (z∈S ↔ z∈U ∧ θ(z))).
```

`Empty(t)`, `B≠t`, and all case splits are **object-language formulas** in
these source derivations. Distinct numeric term codes are not evidence of
object disequality. The guarded conclusion has no `U≠t` premise.
No distinctness of `x,y` is required for raw pairs.

Expose actual typed proof objects and `Proof seedTheory` certificates for
the three existential implications and the unconditional pair theorem.
As in RawComprehension, `.get` may extract an already constructed derivation;
no supplied standard proof or proof-search oracle is a hypothesis. A fixed
Σ₁ graph for the entire proof-code map is not claimed merely from these
certificates. Fixed total raw syntax constructors/graphs and their exact
typed identities are appropriate for the new matrices and conclusion bodies.

## 2. Literal syntax and parameter discipline

Below, `#0,#1` are typed bound slots. A zero-bound-slot term written under
two binders is explicitly lifted with `.bShift.bShift`. Every occurrence
`θ[#0]` means actual `θ.subst ![#0]` at the displayed arity and preserves
every original free parameter.

```text
rawPairBody x y :=
  ∀ ((#0 ∈ #1) ↔ ((#0 = x↑↑) ∨ (#0 = y↑↑)))

twoRootBody θ B t :=
  ∀ ((#0 ∈ #1) ↔
       ((#0 = B↑↑) ∨ ((#0 = t↑↑) ∨ ((#0 ∈ B↑↑) ∧ θ[#0]))))

guardedBody θ U t :=
  (t↑ ∈ #0) ∧
    ∀ ((t↑↑ ∈ #0) → ((#0 ∈ #1) ↔ ((#0 ∈ U↑↑) ∧ θ[#0])))
```

The outer existential chooses the container; the displayed inner universal
has `(z,container)` in slots `(0,1)`. Define `...At` by substituting the
chosen container into the one-slot body. Prove the exact shift/free laws,
for example:

```text
(guardedBody θ U t).shift = guardedBody θ.shift U.shift t.shift
(guardedBody θ U t).free = guardedAt θ.shift U.shift t.shift (fvar 0)
```

Also prove the corresponding laws for `rawPairBody`, `twoRootBody`, and
their matrix constructors. Existential introduction/elimination shifts the
entire finite context, θ, the marker, and every ambient term together.
There is no `θ.shift=θ`, `t.shift=t`, freshness bound, standard label, or
closed-parameter restriction.

Use the existing `term_is_fvar` only for zero-bound-slot terms: it gives an
arbitrary **internal** free label, not a standard natural label. Nested θ
binders remain untouched except by the capture-avoiding substitution APIs.

## 3. Raw pair and two-root source derivations

The existing semantic guides are fully read:
`BusyBeaver/ZFC/KLowerRaw.lean` (`raw_pair`, `raw_tagged`) and
`KLowerTag.lean` (`dt_comp`). They are inert proof guides, not imports or
source proof premises. Their `FormSeed`/`Sat` theorems cannot be used as an
all-internal proof transformation.

### Raw pair

Under `Empty(t)`, choose a source singleton `r={t}` using `singleton_object`.
Then `r≠t`: `t∈r`, while no element belongs to t. Instantiate the actual
open seed proof at root r with matrix (output z, input p):

```text
pairMatrix(t,r,x,y)(z,p) := (p=r ∧ z=x) ∨ (p=t ∧ z=y).
```

Its typed definition uses `#0` for z, `#1` for p, and twice-lifted ambient
terms. Request at root r gives x∈C; its second branch is excluded by r≠t.
Support restricts each member of C to x or y. Because t is a subset of every
source object, full member closure at x∈C and input t gives y∈C; its first
branch is excluded by the same root disequality. Thus C is the exact pair.
This works unchanged when x=y, x=t, y=t, or any free labels coincide.
Eliminate t with `empty_object` for the unconditional `raw_pair` endpoint.

### Two roots

Under `Empty(t)` and the source formula `B≠t`, choose r={B,t}. Prove in the
source theory all three collision exclusions:

```text
r≠t;
∀v ¬Singleton(r,v);
∀v ¬Singleton(t,v).
```

For the middle statement, B∈r and t∈r would give B=v=t under a singleton
assumption. The last statement follows because a singleton contains its
designated element. These are actual equality/membership derivations, not
tests on syntax codes. No membership extensionality is required.

Use the literal three-branch seed matrix:

```text
twoRootMatrix(θ,B,t,r)(z,p) :=
  (p=r ∧ z=B) ∨
  ((p=t ∧ z=t) ∨ (Singleton(p,z) ∧ z∈B ∧ θ(z))).
```

The singleton subformula under its own binder w has slots `(w,z,p)` and
is `∀w (w∈p ↔ w=z)`. Root request gives B∈C. Full member closure at B
and empty input t gives t∈C. For z∈B satisfying θ, choose a source singleton
p={z}; it is a subset of B. Closure at B with input p returns a selected
matrix output in C. The root and empty-input branches are excluded by the
three facts above; singleton uniqueness identifies the output with z.
Support supplies the exact forward membership implication.

There is no need to rewrite inside arbitrary θ by source equality: support
already contains θ at its actual output, and the reverse direction uses
atomic membership transport after singleton uniqueness. Thus no new
internal formula-congruence induction is required at this checkpoint.

## 4. Guarded comprehension, including the exceptional bound

The source proof performs a finite classical split on the **source formula**
`eqTerm U t`. It must not branch on metatheoretic equality of the term codes.

If U=t, choose S={t}. Then t∈S. A guarded element z (t∈z) cannot equal t,
by the actual source irreflexivity axiom. It therefore cannot belong to S.
It also cannot belong to U=t because t is empty. Both sides of the desired
membership equivalence are false, independently of θ. This branch cannot be
omitted or replaced by an extra U≠t premise.

If U≠t, invoke the public `raw_augmented` with the unary matrix `t∈#0`:

```text
E = {U} ∪ {z∈U | t∈z}.
```

The actual augmented endpoint and its public body definition yield U∈E,
E≠t, and t∉E. For the last fact, the root branch would imply t=U; the
selected branch would imply t∈t. Apply `raw_two_root` at B=E and matrix
`(#0∈U) ∧ θ[#0]`, obtaining

```text
S = {E,t} ∪ {z∈E | z∈U ∧ θ(z)}.
```

Its t root proves t∈S. Under the guard t∈z, neither extra member E nor t
is possible (using t∉E and t∉t). Conversely, z∈U and the guard imply z∈E
by the augmented envelope, so the selected branch puts z in S. Arbitrary
free parameters of θ survive both existential eliminations.

Here membership irreflexivity is genuinely used. Obtain its typed source
proof directly from the exact `irreflexiveSentence` member of seedTheory,
then specialize at the required arbitrary term. Do not cite the validator
numeric image theorem as though it were this source proof.

## 5. Public import boundary and finite helper obligations

The usable public imported endpoints are `openSeedProof`, `empty_object`,
`singleton_object`, `emptyAt`, `singletonAt`, `eqTerm`, `memTerm`,
`seedPairAt`, `memberClosure`, `full_member_closure`, `subsetTerm`,
`singTerm`, `raw_augmented`, `rawAugBody`, `rawAugAt`, and the public
shift/free/raw-code identities. Every frozen private helper stays private.
In particular, neither `pair_request`/`pair_support` nor `source_symm`/
`source_mem_ext` can be cited as a public imported theorem.

The new leaf may derive small named source helpers from the literal public
full-seed body and the recognized source equality axioms. Its support and
request specializations must be checked against `seedPairAt` by exact
definitional expansion of the public wrapper; closure uses the actual
public `full_member_closure`. A new one-slot seed-container body may name
the literal remainder of `fullSeedBody`; prove its exact relationship to
the public wrapper, without editing an accepted definition or using a
private generated FQName. This is finite syntax manipulation, not a new
schema recognizer.

Equality reflexivity, symmetry, transitivity, and two-argument membership
congruence are finite specializations of actual seedTheory equality axioms.
Keep terminal truth/falsum and the four-binder relation-congruence order.
Atomic transport of a marker or a bound uses those axioms explicitly.
All uses of GEN and existential elimination retain `.free` and the shifted
finite context; the object premises Empty(t) and B≠t shift with it.

The complete proposed endpoint should remain guarded comprehension,
not only the easier raw pair. If implementation needs a physical split,
freeze raw-pair/two-root helpers as a coherent first leaf and obtain review
for a second guarded leaf; do not silently label that intermediate as the
full result. No such Lean file or split is implemented by this plan.

## 6. Focused checks, cache scope, and remaining boundary

Checks should cover literal matrix substitutions, simultaneous shifts,
arbitrary internal free label zero and a sparse label, θ with nested binders,
θ=⊤/⊥, actual proof-code certificates, and total raw syntax graph instances.
Include raw pairs with x=y and with both equal to t; a separate specialization
of guarded comprehension at U=t; and exact object-antecedent preservation
for two-root B≠t. No finite model test replaces these uniform statements.

The sole-import plan is exactly **202 cached modules / 136 Foundation /
610 object artifacts / 45 external boundaries**, adding only the frozen Raw
main object to the preceding 201-module closure. All 247 first providers
must match the chosen objects. There is no new external boundary, dependency
build, compiler-package change, or Foundation import. The inherited source,
trace, companion, and absent-companion qualifications remain explicit.

The provisional Raw author provider is
`/tmp/validator-seed-raw-comprehension222-author-k3tb0hhm/lib`:
main source `b3db367233a5428190acb9d0394089bf465a2cc3ffbf59bd9c1aa757837cbbc6`,
main object `b252e49fa0d40722f45e4e1489f8ce1db5475ab746a095656ab04df608cebc75`.
Root independent acceptance is still pending at freeze; later selection of
an accepted provider must be pinned as additional evidence without rewriting
this historical plan. The raw replay/bundle and all six attempts are retained.

The JSON inventory and fully read read-only auditor beside this note pin the
complete dependency order, actual public/meta imports (including Aesop),
selected objects, explicit external boundaries, current first providers,
the source guides, and prior replay evidence. No compiler or overlay was
created during planning. The driver rejects any changed source/provider or
an unexpected boundary before producing its inventory.

This next packet would prove guarded comprehension in the original source
language. It would **not** yet prove the represented marker-reserving `relT`
translation, parameter-safe proof induction, tagged Collection, profile
equality/bisimulation, quotient/well-founded interpretation, or a ZF/ZFC
proof transformation. `KLowerRel.sat_top` and `KLowerTag.tag_sep` still have
ordinary semantic scopes; their use with standard formulas alone does not
discharge internally sized source syntax. There is no Good shift-fixedness
assumption for a free marker, no raw CP/GIC replacement, no identification of
source equality with primitive numeric `weq` or later profile `Eqv`, and no
new closed HA equation/consistency claim.

The read-only audit passed on its first run, rehashing **1,474 observations**
and matching all 247 actual first providers. The frozen cache inventory is
`validator-seed-guarded-comprehension-cache-plan.json`, SHA256
`42822cf5e43a8541d9fabe86b1c031e9c8fe3c64d97ea89a1fa0f540d355cba8`.
The sibling audit log and four-file manifest preserve the complete planning
execution. There were no planning failures or compiler invocations.
