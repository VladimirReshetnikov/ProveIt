# Actual hierarchy-one GG comparison: exact next-leaf proposal

Read-only audit, 26 October 2026, `circuit_reduction`. This proposes one
new `FoundationHASigmaOneGG.lean` and focused checks. No implementation or
compiler invocation occurred for this proposal. The finite-DNS prerequisite
has now passed root's independent replay and was accepted at `a9d241426f`.
The preceding [calibration audit](ha-negative-sigma-one-calibration-audit.md)
remains frozen; this note makes its generic hierarchy step precise.

## Exact target and motive

Use the **existing** Foundation classical NNF syntax, its **existing**
`Semiformula.doubleNegation`, and the already defined ordinary interpretation
`FoundationHADeltaZero.ordinaryAux`. Do not define another formula grammar or
negative-translation algorithm. Write `F := SetTheory.PA.Formula`, with
`ProofEquiv` the existing abbreviation in `FoundationHADeltaZeroGG`:

```lean
ProofEquiv a b = HA.Proves (.and (.imp a b) (.imp b a))
```

The proposed helper and public endpoints are:

```lean
hierarchy_sigma_one_doubleNeg
    {ξ : Type*} {n s : Nat} {Γ : Polarity}
    {p : Semiformula ℒₒᵣ ξ n}
    (hp : Arithmetic.Hierarchy Γ s p) (hΓ : Γ = 𝚺) (hs : s = 1)
    (bv : Fin n → PTerm) (fv : ξ → PTerm) :
  ProofEquiv (formulaAux bv fv pᴺ) (doubleNeg (ordinaryAux bv fv p))

sigma_one_doubleNeg
    {ξ : Type*} {n : Nat} {p : Semiformula ℒₒᵣ ξ n}
    (hp : Arithmetic.Hierarchy 𝚺 1 p)
    (bv : Fin n → PTerm) (fv : ξ → PTerm) :
  ProofEquiv (formulaAux bv fv pᴺ) (doubleNeg (ordinaryAux bv fv p))
```

A `sigma_one_doubleNeg_relative` corollary weakens the **actual HA proof**
to any finite context `G`; it changes no arithmetic axiom set. The helper's
induction motive is, for every indexed `Γ,s,n,p`,

```text
∀ (hΓ : Γ = Σ) (hs : s = 1) (bv : Fin n → PTerm) (fv : ξ → PTerm),
  ProofEquiv (formulaAux bv fv pᴺ) (doubleNeg (ordinaryAux bv fv p)).
```

Both equalities remain explicit during induction on `hp`. One must not
erase the polarity or level and then attempt to cover an arbitrary
unbounded-universal constructor. A `sigma` constructor reaches a Π0 body;
the proof uses the accepted level-zero theorem on that body, not a
nonexistent Σ1 induction hypothesis for it.

## Literal source constructors

The source is
`Foundation/FirstOrder/Arithmetic/Basic/Hierarchy.lean:10–26`, relative to
`/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation/`.
It has these fourteen constructors, not a hidden prenex representation:

| Constructor | Exact applicable case at the target index | HA proof route |
| --- | --- | --- |
| `verum`, `falsum` | Any polarity/level | Ordinary truth/falsity are already syntactically negative; use actual introduction and `HA.Negative` stability. |
| `rel` | Equality or order in `ℒₒᵣ` | Literal GG atom is exactly double-negated ordinary atom; identity. |
| `nrel` | Negative equality or order | Both interpretations contain one negation; triple-negation stability compares it with its double negation. |
| `and` | Both premises at Σ1 | Combine the two IHs and the intuitionistic equivalence `¬¬(A∧B) ↔ (¬¬A∧¬¬B)`. |
| `or` | Both premises at Σ1 | Preserve literal `¬(¬C∧¬D)` and prove its equivalence to `¬¬(A∨B)` from `C↔¬¬A`, `D↔¬¬B`. No component decision. |
| `ball` | Same level; source bound `t.Positive` | Extract the witness-free outer bound; normalize the exact negative guard, apply finite DNS, and transport the ordinary decidable-order guard. |
| `bexs` | Same level; source bound `t.Positive` | Apply the conjunction comparison to the order atom and matrix, then the general negative-existential comparison. No bounded-existential recovery. |
| `exs` | `Hierarchy Σ (s+1)` body and conclusion; target forces `s=0` | Apply the IH at lifted environments and negative-existential comparison. |
| `all` | Conclusion polarity Π | Impossible under `hΓ`. |
| `sigma` | Π `s` body, Σ `(s+1)` existential conclusion; target forces `s=0` | Obtain Δ0 by `Hierarchy.zero_iff_delta_zero`, use bounded ordinary/GG comparison and genuine ordinary decision, then negative-existential comparison. |
| `pi` | Conclusion polarity Π | Impossible under `hΓ`. |
| `dummy_sigma` | Conclusion level `s+2` | Impossible under `hs`. |
| `dummy_pi` | Conclusion polarity Π (also level at least two) | Impossible under `hΓ` or `hs`. |

`Hierarchy.zero_iff_delta_zero` is in the same file, line 89. The Π0 bridge
is a syntactic theorem; it is not an invocation of classical truth or
`ProperOn`. The exact `sigma` case must first rewrite its numeric index to
zero before invoking that bridge.

## Finite logical helpers and quantifier contexts

These are HA derivations over the existing syntax, not semantic claims.
Their inputs are actual object-language proof equivalences.

The proposed finite logical helper signatures, with all `A,B,C,D,L : F`,
are as follows (names provisional; statements fixed):

```lean
negative_doubleNeg (hA : HA.Negative A) : ProofEquiv A (doubleNeg A)

neg_of_doubleNeg_equiv (h : ProofEquiv C (doubleNeg A)) :
  ProofEquiv (neg C) (neg A)

and_doubleNeg_equiv (hA : ProofEquiv C (doubleNeg A))
    (hB : ProofEquiv D (doubleNeg B)) :
  ProofEquiv (.and C D) (doubleNeg (.and A B))

or_doubleNeg_equiv (hA : ProofEquiv C (doubleNeg A))
    (hB : ProofEquiv D (doubleNeg B)) :
  ProofEquiv (neg (.and (neg C) (neg D))) (doubleNeg (.or A B))

ex_doubleNeg_equiv (h : ProofEquiv C (doubleNeg A)) :
  ProofEquiv (neg (.all (neg C))) (doubleNeg (.ex A))

guard_doubleNeg_equiv (h : ProofEquiv C (doubleNeg A)) :
  ProofEquiv (neg (.and (doubleNeg L) (neg C))) (.imp L (doubleNeg A))
```

Bookkeeping helpers can compose/reverse `ProofEquiv`, map its implications
under double negation using `map_doubleNeg`, and reclose with `all_imp`.
These are finite compositions of accepted rules, not additional assumptions.
For the Π0 base, a helper with **explicit** hypotheses
`h : ProofEquiv A C` and `hd : Proves (dec A)` yields
`ProofEquiv C (doubleNeg A)` using accepted `stable_of_decidable`. Only
that syntactically bounded base supplies `hd`; no Σ1 decision is inferred.

1. From `ProofEquiv C (doubleNeg A)`, derive
   `ProofEquiv (neg C) (neg A)`. Both implications are contraposition plus
   triple-negation elimination for a literal negation. No stability of `A`
   is required.
2. From comparisons for `C,A` and `D,B`, derive the conjunction and negative
   disjunction comparisons in the table. Reuse `HABoundedDoubleNegation.doubleNeg_pair`
   for the nontrivial conjunction direction, and the existing
   `FoundationHAOrderAdditive.map_doubleNeg` for projections/compositions.
3. From `ProofEquiv C (doubleNeg A)`, derive

   ```text
   ProofEquiv (neg (.all (neg C))) (doubleNeg (.ex A)).
   ```

   The forward direction assumes `¬∃A`; the already proved
   `not_ex_all_not` gives `∀¬A`, then the pointwise negative comparison
   yields `∀¬C`, contradicting the negative encoding. In the reverse
   direction, `∀¬C` would imply `¬∃A`: eliminate an actual existential
   witness, map `A→¬¬A→C`, and contradict the corresponding `¬C` instance.
   This contradicts `¬¬∃A`. **Neither direction produces an existential
   witness from a double negation**, nor requires a decision of `∃A`.

Use `FoundationHADeltaZero.all_imp` for universal transport. In each
`Relative.all_intro`, the entire assumption context is mapped by
`Formula.rename Nat.succ`. In each `Relative.ex_elim`, the context is
`A :: G.map (Formula.rename Nat.succ)` and the conclusion is renamed.
The exact accepted identity
`Formula.subst_instTerm_var_zero_rename_up_succ` discharges opening a
shifted quantifier at the fresh variable. These are the same rules already
used in `not_ex_all_not` and the bounded-DNS converse.

Under a source binder, both interpreted matrices use **exactly**

```text
liftBound bv = Fin.cases (var 0) (rename succ ∘ bv),
liftFree fv  = rename succ ∘ fv.
```

Thus the IH is instantiated with `liftBound bv, liftFree fv`. Arbitrary
environment terms containing slot zero do not become the new source
witness: their slots have been shifted. No supplied context is generalized
without this shift.

## The bounded-universal case in detail

The exact positive-bound theorem says

```text
t.Positive → ∃ u, t = Rew.bShift u
  ∧ termAux (liftBound bv) (liftFree fv) t
      = Term.rename Nat.succ (termAux bv fv u).
```

This is `FoundationHADeltaZero.positive_bound`, using the pinned
`Rew.positive_iff` and `FoundationPAHFSyntax.termAux_bShift`. `Positive`
means absence of source bound-variable zero; it does **not** mean a positive
natural value. Zero bounds are permitted.

Set `T := termAux bv fv u`, `L := ltFormula (var 0) (rename succ T)`,
`A := ordinaryAux (liftBound bv) (liftFree fv) p`, and
`C := formulaAux (liftBound bv) (liftFree fv) pᴺ`. The source is literally
NNF `∀(¬L ∨ p)`, so the exact two target expressions are:

```text
ordinary: all (or (neg L) A)
GG:       all (neg (and (doubleNeg L) (neg C))).
```

The IH says `C ↔ ¬¬A`. A finite logical helper proves

```text
¬(¬¬L ∧ ¬C) ↔ (L → ¬¬A).
```

For left-to-right, assume `L` and `¬A`. The IH makes `¬C` available, while
`L` gives `¬¬L`; contradiction. For right-to-left, `¬C` and the IH yield
`¬¬A→⊥`; with `L→¬¬A` this gives `¬L`, contradicting `¬¬L`. No decision of
the matrix, or even of `L`, is needed for this helper.

Reclosing yields GG `↔ ball T (doubleNeg A)`. The accepted bounded-DNS
theorem yields `↔ doubleNeg (ball T A)`. Finally the already proved
`guard_forward` and `guard_reverse`, the latter with
`FoundationHAOrderDecidable.lt_decidable`, give

```text
all (or (neg L) A) ↔ ball T A.
```

Transport these **proved** implications under double negation. This finishes
the comparison with the actual ordinary NNF interpretation. It never uses
unbounded `∀¬¬A→¬¬∀A`, nor treats the disjunctive source guard as a
definitionally equal primitive implication.

For bounded existence the literal GG is
`neg (all (neg (and (doubleNeg L) C)))`. The conjunction helper compares
`and (doubleNeg L) C` with `doubleNeg (and L A)`, after which the general
negative-existential helper applies. The source positive-bound premise
remains part of the hierarchy constructor, although this existential
argument itself works even for a dependent guard. No theorem of the form
`¬¬bex T A → bex T (¬¬A)` is asserted.

## Scope, checks, and later fixed target

The smallest coherent next packet is the generic hierarchy theorem plus
its finite logical helpers, about 260–340 main lines and 70–100 checks.
If helper proof engineering exceeds that scope, freeze a separate finite
logic leaf first rather than enlarging the target or adding assumptions.
Recommended focused checks cover literal GG shapes, arbitrary undecided
propositional matrices, unbounded-existential `exs`, the distinct Π0
`sigma` introduction, bounded-all of an unbounded-existential matrix,
nested positive bounds referring to a preceding witness, zero bounds,
sparse environments, and shifted finite contexts. A negative control should
retain the **double negation** on the ordinary existential conclusion;
there is no claim that the Σ1 formula is decidable.

Do not import the wide fixed-consistency or current-equation closure into
this generic leaf. A later specialization may use the exact syntactic
evidence `(provabilityPred' T ⊥).sigma_prop` and
`provabilityPred'_val` from
`Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean:487–490`.
Combining the generic result with the existing transported GG negation
duality can target **HA negation of the ordinary positive source predicate**.
That later step is not part of this proposal's implementation.

In particular, do not assert `ordinaryAux (∼ρ) = neg (ordinaryAux ρ)`:
Foundation NNF negation may exchange conjunction/universality with
disjunction/existence, and intuitionistic De Morgan reversal is not
available. This proposal supplies no Markov principle, positive Σ1 DNE,
checker properness normalization, independent proof-checker equivalence,
current-equation PA theorem, or 215/222 runtime calibration.

## Rehashed cache and source boundary

Proposed imports are only `FoundationHADeltaZeroGG` and
`HABoundedDoubleNegation`. Read-only current-import traversal gives exactly
**104 cached modules, 76 Foundation modules, 332 existing artifacts and 34
explicit external boundaries**. Only the new main and checks would be fresh;
no Foundation or prerequisite build is required. No cached client imports
either proposed new module. The 762 inherited/explicit pin observations
were rehashed, including current source bytes, selected object companions,
external boundaries, both original author bundles and both independent
root records. This is a cache feasibility audit, not a fresh compiler replay.

The selected accepted root primaries are:

- `FoundationHADeltaZeroGG`: root record
  `95816b89f211437e005f4e7b1de5efe82c765b7e0213a8ec3b3d84e33f481d7e`;
  `/tmp/foundation-ha-deltazero-gg-root-peer-y5x43g1v/lib`, object
  `f9f8d84acd4726cfacc6f2c7eb1bad8d1f1666fbb54230421ebb09a774042a3a`.
- `HABoundedDoubleNegation`: root record
  `289f3ee4d80606920ddaa9b13676db66a5ac70d2cd522165913ba2cd7c852ea3`;
  `/tmp/ha-bounded-double-negation-root-peer-z7i5h7h7/lib`, object
  `f0e760efed2f33d6b23e19b83266c479212d7a19cc51b011f8f26c3f4ea14344`.

All exact source anchors and the dependency-ordered selected inventory are
in [the companion pin file](ha-sigma-one-gg-proposal-pins.json), SHA
`b18471360f8868aaa7c703179f7ffd96a4b123ccf4567298010f790ffbc34889`.
No source, object, vendor file, shared document, or Git state was modified
by the audit; only this new proposal and its read-only pin inventory were
written.
