import BusyBeaver.ZFC.ZFRank
import Foundation.FirstOrder.SetTheory.Basic.Axioms

set_option autoImplicit false

/-!
Ordinary semantic ZF extraction and a fixed power-container theorem.
The syntax translation and totalized Replacement argument are adapted from
ZFCinPA/Translation.lean, using only ZF axioms directly. The checked native
rank theorem is reused; no arbitrary internal formula is quoted or interpreted.
This source does not yet connect its fixed sentence to decoded numerical C.
-/
namespace LeanProofs.ZFCinPA.NativeZFContainers254
open LO LO.FirstOrder LO.FirstOrder.SetTheory

abbrev memRel (V : Type*) [SetStructure V] : V → V → Prop := (· ∈ ·)

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

section Extraction
variable {V : Type*} [SetStructure V] [Nonempty V]

/-- Ordinary Separation at an external formula, using the actual ZF axiom. -/
theorem sep_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (phi : SetTheory.Form) (e : ℕ → V) (a : V) :
    ∃ s : V, ∀ x, x ∈ s ↔ (x ∈ a ∧ SetTheory.Sat (memRel V) (SetTheory.scons x e) phi) := by
  have hh : ∀ f : ℕ → V, ∀ X : V, ∃ Y : V, ∀ z : V,
      z ∈ Y ↔ z ∈ X ∧ (toSet 1 phi).Eval ![z] f := by
    simpa [models_iff,Axiom.separationSchema,Matrix.constant_eq_singleton,
      Matrix.comp_vecCons'] using
      Theory.models V 𝗭𝗙 (ZermeloFraenkel.axiom_of_separation (toSet 1 phi))
  obtain ⟨s,hs⟩ := hh e a
  refine ⟨s,fun x => (hs x).trans (and_congr_right fun _ => ?_)⟩
  exact eval_toSet phi 1 ![x] e (SetTheory.scons x e)
    (env1_eq x e) (fun j => env1_shift x e j)

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
theorem repl_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (psi : SetTheory.Form) (e : ℕ → V)
    (hfun : SetTheory.Functional (SetTheory.relOf (memRel V) psi e)) (a : V) :
    ∃ r : V, ∀ y, y ∈ r ↔ ∃ x, x ∈ a ∧ SetTheory.relOf (memRel V) psi e y x := by
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
      Theory.models V 𝗭𝗙
        (ZermeloFraenkel.axiom_of_replacement (toSet 2 (totalGraphF psi)))
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

theorem ext_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (a b : V)
    (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b := by
  have he : ∀ x y : V, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y := by
    simpa [models_iff,Axiom.extentionality] using
      Theory.models V 𝗭𝗙 ZermeloFraenkel.axiom_of_extentionality
  exact (he a b).mpr h

theorem pair_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    ∀ x y : V, ∃ p : V, ∀ z, z ∈ p ↔ z = x ∨ z = y := by
  simpa [models_iff,Axiom.pairing] using
    Theory.models V 𝗭𝗙 ZermeloFraenkel.axiom_of_pairing

theorem union_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (u : V) :
    ∃ w : V, ∀ x, x ∈ w ↔ ∃ v, x ∈ v ∧ v ∈ u := by
  have hh : ∀ X : V, ∃ Y : V, ∀ z, z ∈ Y ↔ ∃ w, w ∈ X ∧ z ∈ w := by
    simpa [models_iff,Axiom.union] using
      Theory.models V 𝗭𝗙 ZermeloFraenkel.axiom_of_union
  obtain ⟨w,hw⟩ := hh u
  exact ⟨w,fun x => (hw x).trans
    ⟨fun ⟨v,hv,hx⟩ => ⟨v,hx,hv⟩,fun ⟨v,hx,hv⟩ => ⟨v,hv,hx⟩⟩⟩

theorem succ_exists [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (x : V) :
    ∃ s : V, ∀ z, z ∈ s ↔ z ∈ x ∨ z = x := by
  obtain ⟨singleton,hs⟩ := pair_clause x x
  obtain ⟨p,hp⟩ := pair_clause x singleton
  obtain ⟨s,hu⟩ := union_clause p
  refine ⟨s,fun z => ?_⟩
  rw [hu z]
  constructor
  · rintro ⟨v,hz,hv⟩
    rcases (hp v).mp hv with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr (((hs z).mp hz).elim id id)
  · rintro (hz | hz)
    · exact ⟨x,hz,(hp x).mpr (Or.inl rfl)⟩
    · subst z
      exact ⟨singleton,(hs x).mpr (Or.inl rfl),(hp singleton).mpr (Or.inr rfl)⟩

theorem inf_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    ∃ I : V, (∃ e0, e0 ∈ I ∧ ∀ z, ¬ z ∈ e0) ∧
      (∀ x, x ∈ I → ∃ sx, sx ∈ I ∧ ∀ t, t ∈ sx ↔ (t ∈ x ∨ t = x)) := by
  have he : ∃ e : V, ∀ z, z ∉ e := by
    simpa [models_iff,Axiom.empty] using
      Theory.models V 𝗭𝗙 ZermeloFraenkel.axiom_of_empty_set
  have hi : ∃ I : V, (∀ e, (∀ z, z ∉ e) → e ∈ I) ∧
      (∀ x, x ∈ I → ∀ s, (∀ z, z ∈ s ↔ z = x ∨ z ∈ x) → s ∈ I) := by
    simpa [models_iff,Axiom.infinity,isEmpty,isSucc,Rew.q_subst,
      Semiterm.val_substs,Function.comp_def] using
      Theory.models V 𝗭𝗙 ZermeloFraenkel.axiom_of_infinity
  obtain ⟨e,he⟩ := he
  obtain ⟨I,hI,hstep⟩ := hi
  refine ⟨I,⟨e,hI e he,he⟩,fun x hx => ?_⟩
  obtain ⟨s,hs⟩ := succ_exists x
  exact ⟨s,hstep x hx s (fun z => (hs z).trans or_comm),hs⟩

theorem pow_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (a : V) :
    ∃ p : V, ∀ z, z ∈ p ↔ SetTheory.Sub (memRel V) z a := by
  have hh : ∀ x : V, ∃ y : V, ∀ z, z ∈ y ↔ ∀ u, u ∈ z → u ∈ x := by
    simpa [models_iff,Axiom.power,isSubsetOf] using
      Theory.models V 𝗭𝗙 ZermeloFraenkel.axiom_of_power_set
  exact hh a

theorem reg_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (a : V) (ha : ∃ x, x ∈ a) :
    ∃ m : V, m ∈ a ∧ ¬ ∃ z, z ∈ m ∧ z ∈ a := by
  have hh : ∀ x : V, (∃ z, z ∈ x) → ∃ y : V, y ∈ x ∧ ∀ z, z ∈ x → z ∉ y := by
    simpa [models_iff,Axiom.foundation,isNonempty,Rew.q_subst,
      Semiterm.val_substs,Function.comp_def] using
      Theory.models V 𝗭𝗙 ZermeloFraenkel.axiom_of_foundation
  obtain ⟨m,hm,hmin⟩ := hh a ha
  exact ⟨m,hm,fun ⟨z,hzm,hza⟩ => hmin z hza hzm⟩

theorem zfAxioms_of_models [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : SetTheory.ZFAxioms (memRel V) :=
  { ext := ext_clause
    sep := sep_clause
    pair := pair_clause
    union := union_clause
    inf := inf_clause
    repl := repl_clause }

theorem power_containers [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (a : V) :
    ∃ v : V, a ∈ v ∧ ∀ x, x ∈ v →
      (∀ z, z ∈ x → z ∈ v) ∧ ∃ p, p ∈ v ∧ ∀ z, (∀ u, u ∈ z → u ∈ x) → z ∈ p := by
  obtain ⟨v,hav,htrans,hpow⟩ :=
    SetTheory.BusyBeaver.ZFC.ZFRank.containers
      (zfAxioms_of_models (V := V)) reg_clause pow_clause a
  exact ⟨v,hav,fun x hx => ⟨htrans x hx,hpow x hx⟩⟩

end Extraction

/-- One fixed ordinary sentence; all variables are bound. -/
def containerSentence : SetTheorySentence :=
  “∀ a, ∃ v, a ∈ v ∧ ∀ x ∈ v,
    (∀ z ∈ x, z ∈ v) ∧ ∃ p ∈ v, ∀ z, (∀ u ∈ z, u ∈ x) → z ∈ p”

theorem zf_container_sentence : (𝗭𝗙 : SetTheory) ⊢ containerSentence := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙 containerSentence ?_
  intro V _ _ _
  simpa [models_iff,containerSentence] using (power_containers (V := V))

/-- The same fixed container property in the exact binder/connective order
of Circuit.container. Distinct quotation names give exactly the de Bruijn
structure of the source row, including its repeated-label shadowing. -/
def containerRowSentence : SetTheorySentence :=
  “∀ c, ∃ b,
    (∀ a, a ∈ b →
      ((∃ p, (∀ z, (∀ u, u ∈ z → u ∈ a) → z ∈ p) ∧ p ∈ b) ∧
        (∀ t, t ∈ a → t ∈ b))) ∧ c ∈ b”

theorem zf_containerRow_sentence : (𝗭𝗙 : SetTheory) ⊢ containerRowSentence := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙 containerRowSentence ?_
  intro V _ _ _
  have hh : ∀ c : V, ∃ b : V,
      (∀ a : V, a ∈ b →
        ((∃ p : V, (∀ z : V, (∀ u : V, u ∈ z → u ∈ a) → z ∈ p) ∧ p ∈ b) ∧
          (∀ z : V, z ∈ a → z ∈ b))) ∧ c ∈ b := by
    intro c
    obtain ⟨b,hcb,hb⟩ := power_containers c
    refine ⟨b,fun a ha => ?_,hcb⟩
    obtain ⟨htrans,p,hpb,hpow⟩ := hb a ha
    exact ⟨⟨p,hpow,hpb⟩,htrans⟩
  simpa [models_iff,containerRowSentence] using hh

end LeanProofs.ZFCinPA.NativeZFContainers254

