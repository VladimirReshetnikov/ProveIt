import BoundedZFCConsistency.AxiomTruth
import Foundation.FirstOrder.SetTheory.Z

/-!
# `Conₙ(ZFC)` is a theorem of Foundation's `𝗭𝗙𝗖`, for every metatheoretic `n`

The repository's `BoundedZFCConsistency` project proves, semantically, that
every model of the nine ZFC axioms satisfies the bounded-consistency sentence
`conZFCForm n`.  This module carries that result across to the Formalized
Formal Logic *Foundation* library: for each metatheoretic `n` there is an
actual Foundation-side derivation `𝗭𝗙𝗖 ⊢ Conₙ^set`, where `Conₙ^set` is the
translation of `conZFCForm n` into Foundation's language of set theory `ℒₛₑₜ`.

The bridge reuses the completed project's **semantic core, not its
derivations**.  The route is completeness:

1. `toSet` translates the repository's flat-De Bruijn `Form` syntax into
   Foundation's `Semiformula ℒₛₑₜ ℕ k`, splitting each repository index at the
   current binder depth `k` into a Foundation bound variable `#i` (below `k`)
   or free variable `&(i-k)` (at or above `k`).
2. `eval_toSet` shows the translation preserves satisfaction: over any
   Foundation set structure — where the standard structure interprets `=` as
   genuine equality and `∈` as the structure's membership — Foundation's
   Tarski evaluation of `toSet k φ` agrees with the repository's `Sat`, under
   the evident environment correspondence.
3. `zfcAxioms_of_models` extracts the repository's semantic bundle
   `ZFCAxioms` from any Foundation model of `𝗭𝗙𝗖`.  The eight non-schematic
   clauses read off Foundation's axioms through the model-side lemmas of
   `Foundation.FirstOrder.SetTheory.Z`; Separation feeds the translation of an
   arbitrary repository formula into Foundation's separation schema; and
   Replacement instantiates Foundation's replacement schema at a *totalized*
   graph, since Foundation's schema demands `∀ x, ∃! y` while the repository's
   `repl` assumes uniqueness only.
4. `zfc_proves_conZFCSet` combines the above with
   `noBoundedRefutationAtLevel_zfc` and Foundation's completeness theorem
   (`SetTheory.provable_of_models`) to produce the derivation.

**Equality.**  Foundation's completeness for `ℒₛₑₜ`-theories containing
`𝗘𝗤 ℒₛₑₜ` is packaged as `SetTheory.provable_of_models`: it suffices to verify
the sentence in every `SetStructure` model, i.e. every type with a membership
relation carrying the `standardStructure`, whose `eq` symbol denotes real
equality.  Foundation internally reduces arbitrary structures to these by the
`QuotNormalize` quotient, so no equality bookkeeping leaks into this module.

`conZFCForm n` is a closed formula (`sentence_conZFCForm`), so its translation
has no semantic free variables; `conZFCSet` nevertheless takes the universal
closure `univCl`, which is the uniform way Foundation turns a `Proposition`
into a `Sentence` and is vacuous here.
-/

namespace LeanProofs
namespace ZFCinPA

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The membership relation of a Foundation set structure, in the binary-
relation form the repository's semantic layer (`SetTheory.Sat`, `ZFAxioms`)
consumes. -/
abbrev memRel (V : Type*) [SetStructure V] : V → V → Prop := (· ∈ ·)

/-! ## The syntax translation

The repository's `Form` uses one flat De Bruijn index space: under `k`
binders, index `i < k` points at the `i`-th enclosing binder and `i ≥ k` is
free.  Foundation separates bound variables `#i : Fin k` from free variables
`&j : ℕ`, with the same "new binder is `#0`" orientation, so the translation
is index splitting and nothing else. -/

/-- The translation of a repository De Bruijn variable at binder depth `k`. -/
def toSetVar (k i : Nat) : Semiterm ℒₛₑₜ ℕ k :=
  if h : i < k then #(⟨i, h⟩ : Fin k) else &(i - k)

/-- **The syntax translation** at binder depth `k`.  Atoms go to the `mem` and
`eq` relation symbols of `ℒₛₑₜ`, the propositional connectives to Foundation's
(implication is Foundation's defined `🡒`), and the quantifiers to `∀⁰`/`∃⁰`
with the depth incremented. -/
def toSet : (k : Nat) → SetTheory.Form → SetTheorySemiproposition k
  | k, .fMem i j => .rel Language.Mem.mem ![toSetVar k i, toSetVar k j]
  | k, .fEq i j  => .rel Language.Eq.eq ![toSetVar k i, toSetVar k j]
  | _, .fBot     => ⊥
  | k, .fImp a b => toSet k a 🡒 toSet k b
  | k, .fAnd a b => toSet k a ⋏ toSet k b
  | k, .fOr a b  => toSet k a ⋎ toSet k b
  | k, .fAll a   => ∀⁰ toSet (k + 1) a
  | k, .fEx a    => ∃⁰ toSet (k + 1) a

/-! ## Satisfaction preservation

The environment-correspondence invariant: a repository environment
`e : ℕ → V` matches a Foundation valuation pair `(b, f)` at depth `k` when
`b i = e i` on the `k` bound slots and `f j = e (k + j)` on the free ones.
The correspondence is preserved on both sides of a binder: prepending `d` to
`b` matches `scons d e` at depth `k + 1` with the same `f`. -/

/-- A translated variable evaluates to the corresponding repository
environment entry. -/
theorem val_toSetVar {V : Type*} [SetStructure V] {k : Nat} {b : Fin k → V}
    {f e : ℕ → V} (hb : ∀ i : Fin k, b i = e i.val)
    (hf : ∀ j, f j = e (k + j)) (i : ℕ) :
    (toSetVar k i).val b f = e i := by
  unfold toSetVar
  by_cases h : i < k
  · rw [dif_pos h]
    exact hb ⟨i, h⟩
  · rw [dif_neg h]
    have h2 : k + (i - k) = i := by omega
    rw [Semiterm.val_fvar, hf (i - k), h2]

/-- **Satisfaction preservation.**  Over any Foundation set structure the
Tarski evaluation of the translation agrees with the repository's `Sat`,
whenever the valuations correspond.  One structural induction; the two binder
cases extend the correspondence through `scons`. -/
theorem eval_toSet {V : Type*} [SetStructure V] (φ : SetTheory.Form) :
    ∀ (k : Nat) (b : Fin k → V) (f e : ℕ → V),
      (∀ i : Fin k, b i = e i.val) → (∀ j, f j = e (k + j)) →
      ((toSet k φ).Eval b f ↔ SetTheory.Sat (memRel V) e φ) := by
  induction φ with
  | fMem i j =>
      intro k b f e hb hf
      simp [toSet, SetTheory.Sat, val_toSetVar hb hf]
  | fEq i j =>
      intro k b f e hb hf
      simp [toSet, SetTheory.Sat, val_toSetVar hb hf]
  | fBot =>
      intro k b f e hb hf
      simp [toSet, SetTheory.Sat]
  | fImp a b iha ihb =>
      intro k bb f e hb hf
      simp only [toSet, LogicalConnective.HomClass.map_imply, SetTheory.Sat]
      exact imp_congr (iha k bb f e hb hf) (ihb k bb f e hb hf)
  | fAnd a b iha ihb =>
      intro k bb f e hb hf
      simp only [toSet, LogicalConnective.HomClass.map_and, SetTheory.Sat]
      exact and_congr (iha k bb f e hb hf) (ihb k bb f e hb hf)
  | fOr a b iha ihb =>
      intro k bb f e hb hf
      simp only [toSet, LogicalConnective.HomClass.map_or, SetTheory.Sat]
      exact or_congr (iha k bb f e hb hf) (ihb k bb f e hb hf)
  | fAll a ih =>
      intro k bb f e hb hf
      simp only [toSet, Semiformula.eval_all, SetTheory.Sat]
      refine forall_congr' fun d => ih (k + 1) (d :> bb) f (SetTheory.scons d e) ?_ ?_
      · intro i
        refine Fin.cases ?_ (fun i' => ?_) i
        · simp [SetTheory.scons]
        · simpa [SetTheory.scons] using hb i'
      · intro j
        have h2 : k + 1 + j = (k + j) + 1 := by omega
        rw [h2]
        simpa [SetTheory.scons] using hf j
  | fEx a ih =>
      intro k bb f e hb hf
      simp only [toSet, Semiformula.eval_ex, SetTheory.Sat]
      refine exists_congr fun d => ih (k + 1) (d :> bb) f (SetTheory.scons d e) ?_ ?_
      · intro i
        refine Fin.cases ?_ (fun i' => ?_) i
        · simp [SetTheory.scons]
        · simpa [SetTheory.scons] using hb i'
      · intro j
        have h2 : k + 1 + j = (k + j) + 1 := by omega
        rw [h2]
        simpa [SetTheory.scons] using hf j

/-! ### Valuation correspondences at the depths the extraction uses -/

private theorem env1_eq {V : Type*} (x : V) (e : ℕ → V) :
    ∀ i : Fin 1, ![x] i = SetTheory.scons x e i.val := fun i =>
  Fin.cases rfl (fun j => j.elim0) i

private theorem env1_shift {V : Type*} (x : V) (e : ℕ → V) (j : ℕ) :
    e j = SetTheory.scons x e (1 + j) := by
  rw [Nat.add_comm]
  rfl

private theorem env2_eq {V : Type*} (x y : V) (e : ℕ → V) :
    ∀ i : Fin 2, ![x, y] i = SetTheory.scons x (SetTheory.scons y e) i.val := fun i =>
  Fin.cases rfl (fun j => Fin.cases rfl (fun j' => j'.elim0) j) i

private theorem env2_shift {V : Type*} (x y : V) (e : ℕ → V) (j : ℕ) :
    e j = SetTheory.scons x (SetTheory.scons y e) (2 + j) := by
  rw [Nat.add_comm]
  rfl

/-! ## Bundle extraction

Everything below is relative to a Foundation model of `𝗭𝗙𝗖`: a nonempty
`SetStructure` satisfying the theory.  The model-side development of
`Foundation.FirstOrder.SetTheory.Z` is stated for models of `𝗭`, so we first
restrict the modelhood along `𝗭 ⊆ 𝗭𝗙 ⊆ 𝗭𝗙𝗖`.  (These are theorems rather
than instances: an instance from `⊧* 𝗭𝗙𝗖` back to `⊧* 𝗭𝗙` would form a cycle
with Foundation's `models_theory_sup` through the union `𝗭𝗙 ∪ 𝗔𝗖`.) -/

section Extraction

variable {V : Type*} [SetStructure V] [Nonempty V]

/-- A model of `𝗭𝗙𝗖` is a model of `𝗭𝗙`. -/
theorem modelsZF_of_modelsZFC [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖] : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
  models_theory_iff.mpr fun _ hφ => Theory.models V 𝗭𝗙𝗖 (Set.mem_union_left _ hφ)

/-- A model of `𝗭𝗙𝗖` is a model of `𝗭`. -/
theorem modelsZ_of_modelsZFC [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖] : V↓[ℒₛₑₜ] ⊧* 𝗭 :=
  models_theory_iff.mpr fun _ hφ =>
    models_theory_iff.mp (modelsZF_of_modelsZFC (V := V)) _ (z_subset_zf hφ)

/-! ### The Separation schema

Foundation's separation schema takes a `Semiproposition 1`; feeding it the
depth-`1` translation of an arbitrary repository formula, with the repository
environment supplied through the free variables, yields exactly the
repository's `sep` clause. -/

/-- The repository's Separation clause, from Foundation's separation schema at
the translated formula. -/
theorem sep_clause [V↓[ℒₛₑₜ] ⊧* 𝗭] (phi : SetTheory.Form) (e : ℕ → V) (a : V) :
    ∃ s : V, ∀ x, x ∈ s ↔ (x ∈ a ∧ SetTheory.Sat (memRel V) (SetTheory.scons x e) phi) := by
  obtain ⟨s, hs⟩ := separation_exists_eval a ((Rew.rewriteMap e) ▹ (toSet 1 phi))
  refine ⟨s, fun x => (hs x).trans (and_congr_right fun _ => ?_)⟩
  rw [Semiformula.eval_rewriteMap]
  exact eval_toSet phi 1 ![x] (fun j => id (e j)) (SetTheory.scons x e)
    (env1_eq x e) (fun j => env1_shift x e j)

/-! ### The Replacement schema

Foundation's replacement schema demands a *total* functional relation
(`∀ x, ∃! y`), while the repository's `repl` assumes uniqueness only.  The gap
is closed by totalizing the graph: `totalGraphF psi` relates `x` to `y` iff
`psi` relates value `y` to argument `x`, or `x` has no `psi`-value and
`y = x`.  Under a functional reading this is total and functional; its image
of `a` contains the desired image of `a`, from which Separation carves the
exact one via `carveF psi`.

De Bruijn conventions: the repository's `relOf mem psi e z x` reads `psi` at
slot `0 = z` (the value) and slot `1 = x` (the argument), parameters shifted
by two; Foundation's schema substitutes the *argument* into slot `0` and the
*value* into slot `1`.  The renamings below mediate. -/

/-- Renaming that swaps the two distinguished De Bruijn slots. -/
def swapR : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => n + 2

/-- Renaming that reads the graph under one extra binder: the new slot `0` is
the value, slot `1` remains the argument, parameters move past one binder. -/
def liftR : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => n + 3

/-- Renaming used by the image carving: the value comes from slot `1`, the
argument from the new slot `0`, parameters move past one extra binder. -/
def carveR : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => n + 3

/-- The totalized graph of `psi`, in Foundation's argument order (slot `0` the
argument `x`, slot `1` the value `y`): either `psi` relates `y` to `x`, or `x`
has no `psi`-value at all and `y = x`. -/
def totalGraphF (psi : SetTheory.Form) : SetTheory.Form :=
  .fOr (SetTheory.rename swapR psi)
    (.fAnd (.fImp (.fEx (SetTheory.rename liftR psi)) .fBot) (.fEq 1 0))

/-- The image predicate for the carving step (slot `0` the image member `y`,
slot `1` the source set `a`, parameters shifted by two): "some `x ∈ a` has
`psi`-value `y`". -/
def carveF (psi : SetTheory.Form) : SetTheory.Form :=
  .fEx (.fAnd (.fMem 0 2) (SetTheory.rename carveR psi))

/-- Satisfaction of the totalized graph, computed. -/
theorem sat_totalGraphF {V : Type*} [SetStructure V] (psi : SetTheory.Form)
    (e : ℕ → V) (xv yv : V) :
    SetTheory.Sat (memRel V) (SetTheory.scons xv (SetTheory.scons yv e)) (totalGraphF psi) ↔
      (SetTheory.relOf (memRel V) psi e yv xv ∨
        ((¬ ∃ z, SetTheory.relOf (memRel V) psi e z xv) ∧ yv = xv)) := by
  unfold totalGraphF
  simp only [SetTheory.Sat]
  refine or_congr ?_ (and_congr ?_ Iff.rfl)
  · exact SetTheory.Sat_rename_ext psi swapR _ _ (fun n => match n with
      | 0 => rfl
      | 1 => rfl
      | _ + 2 => rfl)
  · refine not_congr (exists_congr fun z => ?_)
    exact SetTheory.Sat_rename_ext psi liftR _ _ (fun n => match n with
      | 0 => rfl
      | 1 => rfl
      | _ + 2 => rfl)

/-- Satisfaction of the carving predicate, computed. -/
theorem sat_carveF {V : Type*} [SetStructure V] (psi : SetTheory.Form)
    (e : ℕ → V) (a y : V) :
    SetTheory.Sat (memRel V) (SetTheory.scons y (SetTheory.scons a e)) (carveF psi) ↔
      ∃ x, x ∈ a ∧ SetTheory.relOf (memRel V) psi e y x := by
  unfold carveF
  simp only [SetTheory.Sat]
  refine exists_congr fun x => and_congr Iff.rfl ?_
  exact SetTheory.Sat_rename_ext psi carveR _ _ (fun n => match n with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl)

/-- The repository's Replacement clause, from Foundation's replacement schema
at the totalized graph, followed by Separation. -/
theorem repl_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖] (psi : SetTheory.Form) (e : ℕ → V)
    (hfun : SetTheory.Functional (SetTheory.relOf (memRel V) psi e)) (a : V) :
    ∃ r : V, ∀ y, y ∈ r ↔ ∃ x, x ∈ a ∧ SetTheory.relOf (memRel V) psi e y x := by
  haveI : V↓[ℒₛₑₜ] ⊧* 𝗭 := modelsZ_of_modelsZFC (V := V)
  -- The totalized graph, read through satisfaction preservation.
  have hTG : ∀ xv yv : V,
      ((toSet 2 (totalGraphF psi)).Eval ![xv, yv] e ↔
        (SetTheory.relOf (memRel V) psi e yv xv ∨
          ((¬ ∃ z, SetTheory.relOf (memRel V) psi e z xv) ∧ yv = xv))) := fun xv yv =>
    (eval_toSet (totalGraphF psi) 2 ![xv, yv] e
        (SetTheory.scons xv (SetTheory.scons yv e))
        (env2_eq xv yv e) (fun j => env2_shift xv yv e j)).trans
      (sat_totalGraphF psi e xv yv)
  -- Totalized functionality: exactly what Foundation's schema demands.
  have htot : ∀ x : V, ∃! y, (toSet 2 (totalGraphF psi)).Eval ![x, y] e := by
    intro x
    by_cases hx : ∃ z, SetTheory.relOf (memRel V) psi e z x
    · obtain ⟨z, hz⟩ := hx
      exact ⟨z, (hTG x z).mpr (Or.inl hz), fun y hy =>
        ((hTG x y).mp hy).elim (fun h => hfun x y z h hz)
          (fun h => absurd ⟨z, hz⟩ h.1)⟩
    · exact ⟨x, (hTG x x).mpr (Or.inr ⟨hx, rfl⟩), fun y hy =>
        ((hTG x y).mp hy).elim (fun h => absurd ⟨y, h⟩ hx) (fun h => h.2)⟩
  -- Foundation's replacement schema at the totalized graph.
  have hrepl :
      ∀ f : ℕ → V,
        (∀ x : V, ∃! y : V, (toSet 2 (totalGraphF psi)).Eval ![x, y] f) →
        ∀ X : V, ∃ Y : V, ∀ y : V,
          y ∈ Y ↔ ∃ x ∈ X, (toSet 2 (totalGraphF psi)).Eval ![x, y] f := by
    simpa [models_iff, Axiom.replacementSchema, Matrix.constant_eq_singleton,
      Matrix.comp_vecCons'] using
      Theory.models V 𝗭𝗙𝗖 (Set.mem_union_left _
        (ZermeloFraenkel.axiom_of_replacement (toSet 2 (totalGraphF psi))))
  obtain ⟨Y, hY⟩ := hrepl e htot a
  -- Carve the exact image out of the totalized one.
  obtain ⟨r, hr⟩ := sep_clause (carveF psi) (SetTheory.scons a e) Y
  refine ⟨r, fun y => ?_⟩
  rw [hr y, sat_carveF psi e a y]
  constructor
  · rintro ⟨-, hx⟩
    exact hx
  · rintro ⟨x, hxa, hRyx⟩
    exact ⟨(hY y).mpr ⟨x, hxa, (hTG x y).mpr (Or.inl hRyx)⟩, x, hxa, hRyx⟩

/-! ### The remaining seven clauses -/

/-- The repository's Union clause (conjuncts in the repository's order). -/
theorem union_clause [V↓[ℒₛₑₜ] ⊧* 𝗭] (u : V) :
    ∃ w : V, ∀ x, x ∈ w ↔ ∃ v, x ∈ v ∧ v ∈ u := by
  obtain ⟨w, hw⟩ := union_exists u
  exact ⟨w, fun x => (hw x).trans
    ⟨fun ⟨v, hv, hx⟩ => ⟨v, hx, hv⟩, fun ⟨v, hx, hv⟩ => ⟨v, hv, hx⟩⟩⟩

/-- The repository's Powerset clause: `Sub` is Foundation's `⊆` verbatim. -/
theorem pow_clause [V↓[ℒₛₑₜ] ⊧* 𝗭] (a : V) :
    ∃ p : V, ∀ x, x ∈ p ↔ SetTheory.Sub (memRel V) x a := by
  obtain ⟨p, hp⟩ := power_exists a
  exact ⟨p, fun x => (hp x).trans Iff.rfl⟩

/-- The repository's Infinity clause, witnessed by Foundation's `ω`: it
contains the empty set and is closed under `succ`. -/
theorem inf_clause [V↓[ℒₛₑₜ] ⊧* 𝗭] :
    ∃ I : V, (∃ e0, e0 ∈ I ∧ ∀ z, ¬ z ∈ e0) ∧
      (∀ x, x ∈ I → ∃ sx, sx ∈ I ∧ ∀ t, t ∈ sx ↔ (t ∈ x ∨ t = x)) := by
  refine ⟨ω, ⟨∅, empty_mem_ω, fun z => not_mem_empty⟩,
    fun x hx => ⟨succ x, ω_succ_closed hx, fun t => ?_⟩⟩
  rw [mem_succ_iff]
  exact or_comm

/-- The repository's Regularity clause, from Foundation's foundation axiom. -/
theorem reg_clause [V↓[ℒₛₑₜ] ⊧* 𝗭] (a : V) (ha : ∃ x, x ∈ a) :
    ∃ m : V, m ∈ a ∧ ¬ ∃ z, z ∈ m ∧ z ∈ a := by
  haveI : IsNonempty a := ⟨ha⟩
  obtain ⟨m, hma, hm⟩ := foundation a
  exact ⟨m, hma, fun ⟨z, hzm, hza⟩ => hm z hza hzm⟩

/-- The repository's choice principle `ChoiceSem`, from Foundation's axiom of
choice.  The pairwise-disjointness hypotheses are contrapositives of one
another, and the `∃!` conclusion supplies the selected element together with
its uniqueness in each member. -/
theorem choice_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖] :
    BoundedZFCConsistency.ChoiceSem (memRel V) := by
  have h : ∀ 𝓧 : V, (∀ X ∈ 𝓧, IsNonempty X) →
      (∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ x ∈ X, x ∈ Y) → X = Y) →
      ∃ C : V, ∀ X ∈ 𝓧, ∃! x, x ∈ C ∧ x ∈ X := by
    simpa [models_iff, Axiom.choice] using
      Theory.models V 𝗭𝗙𝗖 (Set.mem_union_right _ rfl)
  intro x hne hdisj
  obtain ⟨C, hC⟩ := h x (fun X hX => isNonempty_def.mpr (hne X hX))
    (fun X hX Y hY hex => by
      by_contra hne'
      obtain ⟨z, hzX, hzY⟩ := hex
      exact hdisj X Y hX hY hne' ⟨z, hzX, hzY⟩)
  refine ⟨C, fun y hy => ?_⟩
  obtain ⟨z, ⟨hzC, hzy⟩, hz⟩ := hC y hy
  exact ⟨z, hzy, hzC, fun w hwy hwC => hz w ⟨hwC, hwy⟩⟩

/-- **Bundle extraction.**  Any Foundation model of `𝗭𝗙𝗖` carries the
repository's nine-axiom semantic bundle over its membership relation. -/
theorem zfcAxioms_of_models [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖] :
    BoundedZFCConsistency.ZFCAxioms (memRel V) :=
  haveI : V↓[ℒₛₑₜ] ⊧* 𝗭 := modelsZ_of_modelsZFC (V := V)
  { ext := fun _ _ h => mem_ext h
    sep := sep_clause
    pair := pairing_exists
    union := union_clause
    inf := inf_clause
    repl := repl_clause
    pow := pow_clause
    reg := reg_clause
    choice := choice_clause }

end Extraction

/-! ## The numeralwise theorem -/

/-- `Conₙ(ZFC)` translated into Foundation's language of set theory: the
universal closure of the depth-`0` translation of the repository's
bounded-consistency sentence.  The closure is semantically vacuous, since
`conZFCForm n` is a sentence (`sentence_conZFCForm`). -/
def conZFCSet (n : Nat) : SetTheorySentence :=
  (toSet 0 (BoundedZFCConsistency.conZFCForm n)).univCl

/- `conZFCForm n` unfolds to the sealed closure of a large body, and reducing
the closure evaluates `bound` over the whole of it.  Nothing in the endpoint
proof needs to see through the quotation, and the elaborator must not try. -/
attribute [local irreducible] BoundedZFCConsistency.conZFCForm SetTheory.sealF

set_option maxRecDepth 8000

/-- **The numeralwise theorem.**  For every metatheoretic `n`, Foundation's
`𝗭𝗙𝗖` derives the translation of `Conₙ(ZFC)`.

By completeness (`SetTheory.provable_of_models`) it suffices to verify the
sentence in an arbitrary Foundation model of `𝗭𝗙𝗖`.  There, the extracted
bundle feeds the completed project's `noBoundedRefutationAtLevel_zfc`, whose
conclusion `sat_conZFCForm_iff` converts into satisfaction of `conZFCForm n`
under every environment; satisfaction preservation finishes. -/
theorem zfc_proves_conZFCSet (n : Nat) : 𝗭𝗙𝗖 ⊢ conZFCSet n := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙𝗖 (conZFCSet n) ?_
  intro V _ _ _
  show V↓[ℒₛₑₜ] ⊧ (toSet 0 (BoundedZFCConsistency.conZFCForm n)).univCl
  refine models_iff_proposition.mpr fun f => ?_
  have K : BoundedZFCConsistency.ZFCAxioms (memRel V) := zfcAxioms_of_models
  have hsat : ∀ e : ℕ → V,
      SetTheory.Sat (memRel V) e (BoundedZFCConsistency.conZFCForm n) :=
    (BoundedZFCConsistency.sat_conZFCForm_iff K.toZFAxioms n).mpr
      (BoundedZFCConsistency.noBoundedRefutationAtLevel_zfc K n)
  exact (eval_toSet (BoundedZFCConsistency.conZFCForm n) 0 ![] f f
    (fun i => i.elim0) (fun j => by rw [Nat.zero_add])).mpr (hsat f)

end ZFCinPA
end LeanProofs
