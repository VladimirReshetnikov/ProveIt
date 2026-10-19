import ZFCinPA.R2Ax

set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.R2Fixed

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254 LeanProofs.ZFCinPA.ValidatorQuantifierCore254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open LeanProofs.ZFCinPA.R2Ctx LeanProofs.ZFCinPA.R2Neg LeanProofs.ZFCinPA.R2Quant LeanProofs.ZFCinPA.R2Gic
open scoped LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

abbrev bv {n : ℕ} (i : Fin n) : Bootstrapping.Semiterm V ℒₛₑₜ n := Bootstrapping.Semiterm.bvar i
abbrev eqA {n : ℕ} (i j : Fin n) : SF (V := V) n :=
  Bootstrapping.Semiformula.rel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) ![bv i, bv j]
abbrev memA {n : ℕ} (i j : Fin n) : SF (V := V) n :=
  Bootstrapping.Semiformula.rel (Language.Mem.mem : (ℒₛₑₜ).Rel 2) ![bv i, bv j]

abbrev neqA {n : ℕ} (i j : Fin n) : SF (V := V) n :=
  Bootstrapping.Semiformula.nrel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) ![bv i, bv j]
abbrev nmemA {n : ℕ} (i j : Fin n) : SF (V := V) n :=
  Bootstrapping.Semiformula.nrel (Language.Mem.mem : (ℒₛₑₜ).Rel 2) ![bv i, bv j]

/-! ## Typed atoms -/

lemma encode_eq_bvars {n : ℕ} (F B s : V) (i j : Fin n) :
    encode F B s (eqA (V := V) i j).val = weq B.[(i : V)] B.[(j : V)] := by
  have hu := (eqA (V := V) i j).isSemiformula.isUFormula
  simp only [eqA] at hu ⊢
  rw [Bootstrapping.Semiformula.rel_val] at hu
  rw [Bootstrapping.Semiformula.rel_val,
    encode_rel F B s (IsUFormula.rel.mp hu).1 (IsUFormula.rel.mp hu).2]
  have hv := (IsUFormula.rel.mp hu).2
  have h0 := TermLabels.vec_nth F B hv (show (0 : V) < ↑(2 : ℕ) by simp)
  have h1 := TermLabels.vec_nth F B hv (show (1 : V) < ↑(2 : ℕ) by simp)
  simp only [Formulas.atom, nth_adjoin_zero, nth_adjoin_one]
  rw [if_pos (by change ((0 : ℕ) : V) = 0; simp), h0, h1]
  simp [Matrix.vecHead, Matrix.vecTail]

lemma encode_memA {n : ℕ} (F B s : V) (i j : Fin n) :
    encode F B s (memA (V := V) i j).val = wel B.[(i : V)] B.[(j : V)] :=
  encode_mem_bvars F B s i j

lemma encode_nrelT {k n : ℕ} (F B s : V) (R : (ℒₛₑₜ).Rel k)
    (v : Bootstrapping.SemitermVec V ℒₛₑₜ k n) :
    encode F B s (Bootstrapping.Semiformula.nrel R v).val =
      wim (encode F B s (Bootstrapping.Semiformula.rel R v).val) 1 := by
  have hu := (Bootstrapping.Semiformula.rel R v).isSemiformula.isUFormula
  rw [Bootstrapping.Semiformula.rel_val] at hu
  rw [Bootstrapping.Semiformula.rel_val, Bootstrapping.Semiformula.nrel_val,
    encode_nrel F B s (IsUFormula.rel.mp hu).1 (IsUFormula.rel.mp hu).2,
    encode_rel F B s (IsUFormula.rel.mp hu).1 (IsUFormula.rel.mp hu).2]

lemma encode_neqA {n : ℕ} (F B s : V) (i j : Fin n) :
    encode F B s (neqA (V := V) i j).val = wim (weq B.[(i : V)] B.[(j : V)]) 1 := by
  rw [neqA, encode_nrelT, ← eqA, encode_eq_bvars]

lemma encode_nmemA {n : ℕ} (F B s : V) (i j : Fin n) :
    encode F B s (nmemA (V := V) i j).val = wim (wel B.[(i : V)] B.[(j : V)]) 1 := by
  rw [nmemA, encode_nrelT, ← memA, encode_memA]

lemma encT_falsum {n : ℕ} (F B s : V) : encode F B s (⊥ : SF (V := V) n).val = 1 := by simp

/-! ## The equality axioms -/

section Taut
open Kalmar.PF
local notation "⊥'" => Kalmar.PF.bot
local infixr:60 " ⟹ " => Kalmar.PF.imp
local notation "x0" => Kalmar.PF.var 0
local notation "x1" => Kalmar.PF.var 1
local notation "x2" => Kalmar.PF.var 2
local notation "x3" => Kalmar.PF.var 3

lemma taut2 {a b : V} (f : Kalmar.PF) (hb : f.Bounded 2) (ht : f.Tautology)
    (he : f.eval wim 1 (sig [a, b]) = wim (wim a b) (wim (wim (wim a 1) 1) b)) :
    CProv (wim (wim a b) (wim (wim (wim a 1) 1) b)) := by rw [← he]; exact taut f 2 hb ht _

lemma glue_symm {E R : V} (h : CProv (wim E R)) : CProv (wim (wim (wim E 1) 1) R) := by
  have t := taut ((x0 ⟹ x1) ⟹ (((x0 ⟹ ⊥') ⟹ ⊥') ⟹ x1)) 2
    (by repeat' (first | exact trivial | decide | constructor)) (by
      intro v; simp only [truth]
      generalize v 0 = a0; generalize v 1 = a1
      revert a0 a1; decide) (sig [E, R])
  simp only [eval, sig, List.getD_cons_zero, List.getD_cons_succ] at t
  exact cProv_mp t h

lemma glue_trans {E1 E2 E3 : V} (h : CProv (wim E1 (wim E2 E3))) :
    CProv (wim (wim (wim E1 1) 1) (wim (wim (wim E2 1) 1) E3)) := by
  have t := taut ((x0 ⟹ x1 ⟹ x2) ⟹ (((x0 ⟹ ⊥') ⟹ ⊥') ⟹ (((x1 ⟹ ⊥') ⟹ ⊥') ⟹ x2))) 3
    (by repeat' (first | exact trivial | decide | constructor)) (by
      intro v; simp only [truth]
      generalize v 0 = a0; generalize v 1 = a1; generalize v 2 = a2
      revert a0 a1 a2; decide) (sig [E1, E2, E3])
  simp only [eval, sig, List.getD_cons_zero, List.getD_cons_succ] at t
  exact cProv_mp t h

lemma glue_ext {E0 E1 R R' : V} (h : CProv (wim E0 (wim E1 (wim R R')))) :
    CProv (wim (wim (wim (wim (wim E0 1) 1) (wim (wim (wim E1 1) 1) 1)) 1)
      (wim (wim (wim R 1) 1) R')) := by
  have t := taut ((x0 ⟹ x1 ⟹ x2 ⟹ x3) ⟹
      (((((x0 ⟹ ⊥') ⟹ ⊥') ⟹ (((x1 ⟹ ⊥') ⟹ ⊥') ⟹ ⊥')) ⟹ ⊥') ⟹ (((x2 ⟹ ⊥') ⟹ ⊥') ⟹ x3))) 4
    (by repeat' (first | exact trivial | decide | constructor)) (by
      intro v; simp only [truth]
      generalize v 0 = a0; generalize v 1 = a1; generalize v 2 = a2; generalize v 3 = a3
      revert a0 a1 a2 a3; decide) (sig [E0, E1, R, R'])
  simp only [eval, sig, List.getD_cons_zero, List.getD_cons_succ] at t
  exact cProv_mp t h

lemma glue_irr {A : V} (h : CProv (wim A 1)) : CProv (wim (wim (wim A 1) 1) 1) := by
  have t := taut ((x0 ⟹ ⊥') ⟹ (((x0 ⟹ ⊥') ⟹ ⊥') ⟹ ⊥')) 1
    (by repeat' (first | exact trivial | decide | constructor)) (by
      intro v; simp only [truth]
      generalize v 0 = a0
      revert a0; decide) (sig [A])
  simp only [eval, sig, List.getD_cons_zero, List.getD_cons_succ] at t
  exact cProv_mp t h

end Taut

lemma nth_three_cons (a b c d e : V) : (a ∷ b ∷ c ∷ d ∷ e).[3] = d := by
  rw [show (3 : V) = 2 + 1 by norm_num, nth_adjoin_succ, nth_two_cons]

lemma quote_sentence (σ : SetTheorySentence) :
    (⌜σ⌝ : V) = (⌜(Rewriting.emb σ : SetTheoryProposition)⌝ : Bootstrapping.Formula V ℒₛₑₜ).val := rfl

open LeanProofs.ZFCinPA.ValidatorEqualityCore254

theorem refl_ax (F s : V) : CProv (encode F 0 s (⌜(Theory.Eq.refl ℒₛₑₜ : SetTheorySentence)⌝ : V)) := by
  rw [quote_sentence, show (⌜(Rewriting.emb (Theory.Eq.refl ℒₛₑₜ) : SetTheoryProposition)⌝ :
    Bootstrapping.Formula V ℒₛₑₜ) = ∀⁰ eqA 0 0 from rfl, encT_all, encode_eq_bvars]
  simpa using cProv_gen s (eq_refl s)

theorem symm_ax (F s : V) : CProv (encode F 0 s (⌜(Theory.Eq.symm ℒₛₑₜ : SetTheorySentence)⌝ : V)) := by
  rw [quote_sentence, show (⌜(Rewriting.emb (Theory.Eq.symm ℒₛₑₜ) : SetTheoryProposition)⌝ :
    Bootstrapping.Formula V ℒₛₑₜ) = ∀⁰ ∀⁰ (neqA 1 0 ⋎ eqA 0 1) from rfl,
    encT_all, encT_all, encT_or, encode_neqA, encode_eq_bvars]
  simpa using cProv_gen s (cProv_gen (s + 2) (glue_symm (eq_symm s (s + 2))))

theorem trans_ax (F s : V) : CProv (encode F 0 s (⌜(Theory.Eq.trans ℒₛₑₜ : SetTheorySentence)⌝ : V)) := by
  rw [quote_sentence, show (⌜(Rewriting.emb (Theory.Eq.trans ℒₛₑₜ) : SetTheoryProposition)⌝ :
    Bootstrapping.Formula V ℒₛₑₜ) = ∀⁰ ∀⁰ ∀⁰ (neqA 2 1 ⋎ (neqA 1 0 ⋎ eqA 2 0)) from rfl,
    encT_all, encT_all, encT_all, encT_or, encT_or, encode_neqA, encode_neqA, encode_eq_bvars]
  simpa [nth_two_cons] using
    cProv_gen s (cProv_gen (s + 2) (cProv_gen (s + 2 + 2) (glue_trans (eq_trans s (s + 2) (s + 2 + 2)))))

theorem relExt_mem_ax (F s : V) :
    CProv (encode F 0 s (⌜(Theory.Eq.relExt (Language.Mem.mem : (ℒₛₑₜ).Rel 2) : SetTheorySentence)⌝ : V)) := by
  rw [quote_sentence, show (⌜(Rewriting.emb (Theory.Eq.relExt (Language.Mem.mem : (ℒₛₑₜ).Rel 2)) :
    SetTheoryProposition)⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
    ∀⁰ ∀⁰ ∀⁰ ∀⁰ ((neqA 0 2 ⋎ (neqA 1 3 ⋎ ⊥)) ⋎ (nmemA 0 1 ⋎ memA 2 3)) from rfl,
    encT_all, encT_all, encT_all, encT_all, encT_or, encT_or, encT_or, encT_or, encode_neqA, encode_neqA,
    encode_nmemA, encode_memA, encT_falsum]
  simpa [nth_two_cons, nth_three_cons] using
    cProv_gen s (cProv_gen (s + 2) (cProv_gen (s + 2 + 2) (cProv_gen (s + 2 + 2 + 2)
      (glue_ext (rel_congr (s + 2 + 2 + 2) (s + 2) (s + 2 + 2) s)))))

theorem relExt_eq_ax (F s : V) :
    CProv (encode F 0 s (⌜(Theory.Eq.relExt (Language.Eq.eq : (ℒₛₑₜ).Rel 2) : SetTheorySentence)⌝ : V)) := by
  rw [quote_sentence, show (⌜(Rewriting.emb (Theory.Eq.relExt (Language.Eq.eq : (ℒₛₑₜ).Rel 2)) :
    SetTheoryProposition)⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
    ∀⁰ ∀⁰ ∀⁰ ∀⁰ ((neqA 0 2 ⋎ (neqA 1 3 ⋎ ⊥)) ⋎ (neqA 0 1 ⋎ eqA 2 3)) from rfl,
    encT_all, encT_all, encT_all, encT_all, encT_or, encT_or, encT_or, encT_or, encode_neqA, encode_neqA,
    encode_neqA, encode_eq_bvars, encT_falsum]
  simpa [nth_two_cons, nth_three_cons] using
    cProv_gen s (cProv_gen (s + 2) (cProv_gen (s + 2 + 2) (cProv_gen (s + 2 + 2 + 2)
      (glue_ext (eq_congr (s + 2 + 2 + 2) (s + 2) (s + 2 + 2) s)))))

/-! ## Irreflexivity -/

/-- The validator's falsum is the atom `0 ∈ 0`. -/
lemma wel_zero_zero : wel (0 : V) 0 = 1 := by
  have h := ArithmeticCantor.triangle_double (0 : V)
  have h0 : ArithmeticCantor.triangle (0 : V) = 0 := by simpa using h
  simp [wel, tagged, ArithmeticCantor.cantor, h0]

/-- No label is a member of itself. -/
lemma not_mem_self (s : V) : CProv (wim (wel s s) 1) := by
  by_cases hs0 : s = 0
  · subst hs0; rw [wel_zero_zero]; exact self_imp 1
  · have L : CProv (wim (weq 0 s) (wim (wel s s) 1)) := by
      have r := rel_congr s 0 s 0
      rw [wel_zero_zero] at r
      exact ded2 (.mp (.mp (.mp (.ax r) (.mp (.ax (eq_symm 0 s)) h1)) (.mp (.ax (eq_symm 0 s)) h1)) h0)
    have e : CProv (ex 0 (wim (wel s s) 1)) :=
      cProv_mp (cProv_mp (all_imp_ex 0 (weq 0 s) (wim (wel s s) 1)) (cProv_gen 0 L)) (ex_equality 0 s)
    exact cProv_mp (ex_elim_of_vac (vac_neg (vac_rel s s 0 (Ne.symm hs0) (Ne.symm hs0)))) e

theorem irr_ax (F s : V) : CProv (encode F 0 s (⌜NativeSet.irAx⌝ : V)) := by
  rw [quote_sentence, show (⌜(Rewriting.emb NativeSet.irAx : SetTheoryProposition)⌝ :
    Bootstrapping.Formula V ℒₛₑₜ) = ∀⁰ (nmemA 0 0 ⋎ ⊥) from rfl,
    encT_all, encT_or, encode_nmemA, encT_falsum]
  simpa using cProv_gen s (glue_irr (not_mem_self s))

end LeanProofs.ZFCinPA.R2Fixed
