import ZFCinPA.LGlue2

set_option autoImplicit false
noncomputable section

/-!
# The glue, internally: the atomic case

For an atom `&a ∈ &b` (or `&a = &b`) with `a, b < j`,
`𝗭𝗙 ⊢ ∀t (¬M_j t ∨ (atom ↔ envForm 0 atom (t)))` (`glue_atom`). The step
template `LGlueT2.atomG` consumes the slot statements (`LGlue1.slot_MT`),
the numerals (`LNumOK.numOK`), functionality (`LGlue1.fun_MT`), and two
logical facts specialized at `&a`, `&b`: uniqueness of `x = &a`, and
`u R v ↔ ∃x ∃y (x = u ∧ y = v ∧ x R y)` (the closed templates `uniqC`,
`adC`).
-/

namespace LeanProofs.ZFCinPA.LGlue3

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory Entailment
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.EnvTransform LeanProofs.ZFCinPA.LDriverBase
open LeanProofs.ZFCinPA.LGlueT LeanProofs.ZFCinPA.LGlueT2 LeanProofs.ZFCinPA.LMatch
open LeanProofs.ZFCinPA.LGlue1 LeanProofs.ZFCinPA.LGlue2
open LeanProofs.ZFCinPA.NumeralOmega (numChainQ)
open scoped LO.FirstOrder.Arithmetic

local instance : Language.Mem GL := ⟨Sum.inl Language.Set.Rel.mem⟩

/-- `x = u → x' = u → x' = x`, with `u = #2`, `x = #1`, `x' = #0`. -/
def uniqC : Sentence GL :=
  ∀⁰ ∀⁰ ∀⁰ (∼(lift eq2S ⇜ ![#1, #2]) ⋎ (∼(lift eq2S ⇜ ![#0, #2]) ⋎ (lift eq2S ⇜ ![#0, #1])))

/-- `u R v ↔ ∃x ∃y (x = u ∧ y = v ∧ x R y)`, read at an ignored `t = #0`,
with `u = #2`, `v = #1`. -/
def adC (isEq : Bool) : Sentence GL :=
  ∀⁰ ∀⁰ ∀⁰ ((lift (if isEq then eqXYS else memXYS) ⇜ ![#1, #2, #0]) 🡘
    ∃⁰ ∃⁰ ((lift eq2S ⇜ ![#1, #4]) ⋏ ((lift eq2S ⇜ ![#0, #3]) ⋏
      lift (if isEq then eqXYS else memXYS) ⇜ ![#0, #1, #2])))

theorem uniqC_provable : templTheory 8 arG ⊢ uniqC := by
  apply templ_provable
  intro M _ _ s _ _ _
  simp [uniqC, eq2S, models_iff, Semiformula.Operator.eq_def]
  intro u x x'
  by_cases h₁ : x = u
  · by_cases h₂ : x' = u
    · exact Or.inr (Or.inr (h₂.trans h₁.symm))
    · exact Or.inr (Or.inl h₂)
  · exact Or.inl h₁

theorem adC_provable (isEq : Bool) : templTheory 8 arG ⊢ adC isEq := by
  apply templ_provable
  intro M _ _ s _ _ _
  cases isEq <;> simp [adC, eq2S, eqXYS, memXYS, models_iff, Semiformula.Operator.eq_def]


variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem q_three {k n : ℕ} (w : Bootstrapping.SemitermVec V ℒₛₑₜ (k + 3) n) :
    w.q 3 = (w 2).bShift := rfl

theorem q_four {k n : ℕ} (w : Bootstrapping.SemitermVec V ℒₛₑₜ (k + 4) n) :
    w.q 4 = (w 3).bShift := rfl

/-- The atom `&a R &b`, read at level one. -/
def atomR (isEq : Bool) (a b : V) : SF V 1 :=
  Bootstrapping.Semiformula.rel
    (if isEq then (Language.Eq.eq : (ℒₛₑₜ).Rel 2) else (Language.Mem.mem : (ℒₛₑₜ).Rel 2))
    ![Bootstrapping.Semiterm.fvar a, Bootstrapping.Semiterm.fvar b]

theorem atomDef_prov (isEq : Bool) (a b : V) (M N N' : SF V 1) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ translateFormula
      (K8 M (atomR isEq a b) ⊤ N (xT a) N' (xT b) ⊤) (Rewriting.emb (atomDef isEq)) := by
  have h := compiledG (adC_provable isEq) (K8 ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ : (i : Fin 8) → SF V (arG i))
  simp [adC, translateFormula, LogicalConnective.iff, Bootstrapping.Semiformula.imp_def] at h
  have h1 := Bootstrapping.TProof.specialize! h (Bootstrapping.Semiterm.fvar a)
  rw [Bootstrapping.Semiformula.substs_all] at h1
  have h2 := Bootstrapping.TProof.specialize! h1 (Bootstrapping.Semiterm.fvar b)
  convert h2 using 1
  apply Bootstrapping.Semiformula.ext
  cases isEq <;>
  simp [atomDef, G, translateFormula, atomR, xT, K8, LogicalConnective.iff, eqXYS, memXYS, eq2S,
    Bootstrapping.Semiformula.imp_def, Bootstrapping.SemitermVec.val, Matrix.vecHead,
    Matrix.vecTail, Semiformula.Operator.eq_def, LO.FirstOrder.Sentence.typed_quote_def,
    q_one, q_two, q_three, q_four]
  all_goals done

theorem uniqG_prov (a : V) (Ks : (i : Fin 8) → SF V (arG i)) (k : Fin 8) (hk : Ks k = xT a) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ translateFormula Ks (Rewriting.emb (uniqG k)) := by
  have h := compiledG uniqC_provable (K8 ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ ⊤ : (i : Fin 8) → SF V (arG i))
  simp [uniqC, translateFormula] at h
  have h1 := Bootstrapping.TProof.specialize! h (Bootstrapping.Semiterm.fvar a)
  convert h1 using 1
  apply Bootstrapping.Semiformula.ext
  simp [uniqG, G, translateFormula, hk, xT, eq2S, Bootstrapping.SemitermVec.val, Matrix.vecHead,
    Matrix.vecTail, Semiformula.Operator.eq_def, LO.FirstOrder.Sentence.typed_quote_def,
    q_one, q_two, q_three, q_four]

theorem numOKG_prov (a : V) (Ks : (i : Fin 8) → SF V (arG i)) (j : Fin 8)
    (hj : Ks j = numChainQ a) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ translateFormula Ks (Rewriting.emb (numOKG j)) := by
  have h := LNumOK.numOK a
  convert h using 1
  simp [numOKG, NumOKT, LStepAtom.numOK₀, LStepAnd.P₀, G, translateFormula, hj, K6,
    Semiformula.Operator.eq_def]
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

/-- The translated atom body over the numeral slots. -/
def EAtomT (isEq : Bool) (Na Nb : SF V 1) : SF V 1 :=
  translateFormula (K8 ⊤ ⊤ ⊤ Na ⊤ Nb ⊤ ⊤) (Rewriting.emb (envAtom isEq))

theorem tr_envAtom (Ks : (i : Fin 8) → SF V (arG i)) (isEq : Bool) :
    translateFormula Ks (Rewriting.emb (envAtom isEq)) = EAtomT isEq (Ks 3) (Ks 5) := by
  cases isEq <;> simp [EAtomT, envAtom, G, translateFormula, K8]

theorem tr_atomConcl (Ks : (i : Fin 8) → SF V (arG i)) (isEq : Bool) :
    translateFormula Ks (Rewriting.emb (∀⁰ (∼G 0 ⋎ (G 1 🡘 envAtom isEq)) : Sentence GL)) =
      GF (Ks 0) (Ks 1) (EAtomT isEq (Ks 3) (Ks 5)) := by
  rw [← tr_envAtom]
  simp [GF, G, translateFormula, LogicalConnective.iff, Bootstrapping.Semiformula.imp_def]

theorem eAtomT_val (isEq : Bool) (a b R : V) (hR : R = if isEq then 0 else 1) :
    (EAtomT isEq (numChainQ a) (numChainQ b)).val = atomCode R a b := by
  subst hR
  cases isEq
  · have h := LDriver.atomT_val_mem a b 1 _root_.one_ne_zero
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← h]
    simp [EAtomT, AtomT, envAtom, LStepAtom.memAtomBody, G, LStepAnd.P₀, LStepAnd.P₂,
      translateFormula, K8, K6]
  · have h := LDriver.atomT_val_eq a b
    simp only [↓reduceIte]
    rw [← h]
    simp [EAtomT, AtomT, envAtom, LStepAtom.eqAtomBody, G, LStepAnd.P₀, LStepAnd.P₂,
      translateFormula, K8, K6]

/-- **The atomic glue.** -/
theorem glue_atom (isEq : Bool) (j a b : V) (ha : a < j) (hb : b < j) :
    (𝗭𝗙 : SetTheory).internalize V ⊢
      GF (MT j) (atomR isEq a b) (EAtomT isEq (numChainQ a) (numChainQ b)) := by
  have hc := compiledG (atomG_provable isEq)
    (K8 (MT j) (atomR isEq a b) ⊤ (numChainQ a) (xT a) (numChainQ b) (xT b) ⊤)
  rw [atomG, LogicalConnective.HomClass.map_imply, translateFormula_imp, tr_atomConcl] at hc
  simp only [LogicalConnective.HomClass.map_and, tr_andG, tr_slotS, tr_funM] at hc
  exact hc ⨀ K!_intro (slot_MT j a ha) (K!_intro (slot_MT j b hb)
    (K!_intro (numOKG_prov a _ 3 rfl) (K!_intro (numOKG_prov b _ 5 rfl)
    (K!_intro (fun_MT j) (K!_intro (uniqG_prov a _ 4 rfl) (K!_intro (uniqG_prov b _ 6 rfl)
    (atomDef_prov isEq a b _ _ _)))))))

end LeanProofs.ZFCinPA.LGlue3
