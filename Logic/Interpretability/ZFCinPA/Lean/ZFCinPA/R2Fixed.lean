import ZFCinPA.R2Ax

set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.R2Fixed

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254 LeanProofs.ZFCinPA.ValidatorQuantifierCore254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254 LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254
open LeanProofs.ZFCinPA.ValidatorNativeGicSlots254
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

lemma taut2 {a b : V} (f : Kalmar.PF) (hb : f.Bounded 2) (ht : f.Tautology)
    (he : f.eval wim 1 (sig [a, b]) = wim (wim a b) (wim (wim (wim a 1) 1) b)) :
    CProv (wim (wim a b) (wim (wim (wim a 1) 1) b)) := by rw [← he]; exact taut f 2 hb ht _

lemma glue_symm {E R : V} (h : CProv (wim E R)) : CProv (wim (wim (wim E 1) 1) R) :=
  compose (double_neg_elim E) h

lemma glue_trans {E1 E2 E3 : V} (h : CProv (wim E1 (wim E2 E3))) :
    CProv (wim (wim (wim E1 1) 1) (wim (wim (wim E2 1) 1) E3)) :=
  ded2 (.mp (.mp (.ax h) (.mp (.ax (double_neg_elim E1)) h1))
    (.mp (.ax (double_neg_elim E2)) h0))

lemma glue_ext {E0 E1 R R' : V} (h : CProv (wim E0 (wim E1 (wim R R')))) :
    CProv (wim (wim (wim (wim (wim E0 1) 1) (wim (wim (wim E1 1) 1) 1)) 1)
      (wim (wim (wim R 1) 1) R')) :=
  ded2 (.mp (.mp (.mp (.ax h)
    (.mp (.ax (double_neg_elim E0)) (.mp (.ax (conj_left _ _)) h1)))
    (.mp (.ax (double_neg_elim E1)) (.mp (.ax (conj_right _ _)) h1)))
    (.mp (.ax (double_neg_elim R)) h0))

lemma glue_irr {A : V} (h : CProv (wim A 1)) : CProv (wim (wim (wim A 1) 1) 1) :=
  compose (double_neg_elim A) h


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

/-! ## The container axiom -/

lemma relL (x y u : V) : CProv (wim (weq x y) (wim (wel x u) (wel y u))) := rel_left x y u
lemma relL' (x y u : V) : CProv (wim (weq x y) (wim (wel y u) (wel x u))) :=
  ded2 (.mp (.mp (.ax (rel_left y x u)) (.mp (.ax (eq_symm x y)) h1)) h0)
lemma relR (x y u : V) : CProv (wim (weq x y) (wim (wel u x) (wel u y))) := rel_right x y u
lemma relR' (x y u : V) : CProv (wim (weq x y) (wim (wel u y) (wel u x))) :=
  ded2 (.mp (.mp (.ax (rel_right y x u)) (.mp (.ax (eq_symm x y)) h1)) h0)
lemma selfU (h X : V) : CProv (wim h (wim X X)) := under (self_imp X)
lemma dneg (X : V) : CProv (wim (neg (neg X)) X) := double_neg_elim X

lemma bundleC_eq (a b c : V) : ArithmeticTemplates254.bundleC a b c =
    ex b (conj (wal a (wim (wel a b) (conj (ex c (conj (wal b (wim (wal c (wim (wel c b) (wel c a)))
      (wel b c))) (wel c b))) (wal c (wim (wel c a) (wel c b)))))) (wel c b)) := rfl

lemma neg_conj_neg (A B : V) : CProv (wim (neg (conj A (neg B))) (wim A B)) :=
  compose (double_neg_elim (wim A (neg (neg B))))
    (ded2 (.mp (.ax (double_neg_elim B)) (.mp h1 h0)))

/-- `¬∃w (w ∈ z ∧ ¬ w ∈ y) → ∀w (w ∈ z → w ∈ y)`. -/
lemma negEx_all (W Z Y : V) :
    CProv (wim (neg (ex W (conj (wel W Z) (neg (wel W Y))))) (wal W (wim (wel W Z) (wel W Y)))) :=
  compose (dneg _) (all_mono W (neg_conj_neg _ _))

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

/-- **The container bridge**, at abstract labels `a < b < c < X < C < Y < P < Z < W`. -/
theorem container_core {a b c X C Y P Z W : V}
    (lab : a < b) (lbc : b < c) (lcX : c < X) (lXC : X < C) (lCY : C < Y) (lYP : Y < P)
    (lPZ : P < Z) (lZW : Z < W) :
    CProv (wal X (ex C (conj (wel X C) (wal Y (wim (neg (neg (wel Y C)))
      (conj (wal P (wim (neg (neg (wel P Y))) (wel P C)))
        (ex P (conj (wel P C) (wal Z (wim (neg (ex W (conj (wel W Z) (neg (wel W Y)))))
          (wel Z P))))))))))) := by
  -- all pairwise orders
  have lac := lab.trans lbc
  have lbX := lbc.trans lcX
  have laX := lac.trans lcX
  have lcC := lcX.trans lXC
  have lbC := lbX.trans lXC
  have laC := laX.trans lXC
  have lcY := lcC.trans lCY
  have lbY := lbC.trans lCY
  have laY := laC.trans lCY
  have lXY := lXC.trans lCY
  have lcP := lcY.trans lYP
  have lbP := lbY.trans lYP
  have laP := laY.trans lYP
  have lXP := lXY.trans lYP
  have lCP := lCY.trans lYP
  have lcZ := lcP.trans lPZ
  have lbZ := lbP.trans lPZ
  have laZ := laP.trans lPZ
  have lXZ := lXP.trans lPZ
  have lCZ := lCP.trans lPZ
  have lYZ := lYP.trans lPZ
  have lcW := lcZ.trans lZW
  have lbW := lbZ.trans lZW
  have laW := laZ.trans lZW
  have lXW := lXZ.trans lZW
  have lCW := lCZ.trans lZW
  have lYW := lYZ.trans lZW
  have lPW := lPZ.trans lZW
  -- the literal instance
  have hL : CProv (ArithmeticTemplates254.bundleC a b c) :=
    ValidatorNativeGic254.cProv_container a b c lac.ne' lbc.ne'
  rw [bundleC_eq] at hL
  -- S1: rename the subset witness c ↦ W, backwards (antecedent position)
  have S1 : CProv (wim (wal W (wim (wel W b) (wel W a))) (wal c (wim (wel c b) (wel c a)))) :=
    all_rename (imp_under (relL' W c b) (relL W c a))
      (vac_imp (vac_rel c b W lcW.ne' lbW.ne') (vac_rel c a W lcW.ne' laW.ne'))
      (vac_all W (vac_imp (vac_rel W b c lcW.ne lbc.ne') (vac_rel W a c lcW.ne lac.ne')))
  -- S2, S3: the power-set clause body, then rename b ↦ Z
  have S3 : CProv (wim (wal b (wim (wal c (wim (wel c b) (wel c a))) (wel b c)))
      (wal Z (wim (wal W (wim (wel W Z) (wel W a))) (wel Z c)))) := by
    have S2 := all_mono b (ValidatorNativeGicCongruence254.cProv_imp_mono S1 (self_imp (wel b c)))
    refine compose S2 (all_rename (imp_under (all_under (vac_eq b Z W lbW.ne' lZW.ne')
        (imp_under (relR b Z W) (selfU _ _))) (relL b Z c)) ?_ ?_)
    · exact vac_imp (vac_all W (vac_imp (vac_rel W Z b lbW.ne lbZ.ne) (vac_rel W a b lbW.ne lab.ne')))
        (vac_rel Z c b lbZ.ne lbc.ne)
    · exact vac_all b (vac_imp (vac_all W (vac_imp (vac_rel W b Z lZW.ne lbZ.ne') (vac_rel W a Z lZW.ne laZ.ne')))
        (vac_rel b c Z lbZ.ne' lcZ.ne'))
  -- S4: the subset clause, rename c ↦ P
  have S4 : CProv (wim (wal c (wim (wel c a) (wel c b))) (wal P (wim (wel P a) (wel P b)))) :=
    all_rename (imp_under (relL' c P a) (relL c P b))
      (vac_imp (vac_rel P a c lcP.ne lac.ne') (vac_rel P b c lcP.ne lbc.ne'))
      (vac_all c (vac_imp (vac_rel c a P lcP.ne' laP.ne') (vac_rel c b P lcP.ne' lbP.ne')))
  -- S5: the power-set witness, rename c ↦ P
  have S5 : CProv (wim (ex c (conj (wal b (wim (wal c (wim (wel c b) (wel c a))) (wel b c))) (wel c b)))
      (ex P (conj (wal Z (wim (wal W (wim (wel W Z) (wel W a))) (wel Z P))) (wel P b)))) := by
    refine compose (ex_mono c (ValidatorNativeGicCongruence254.cProv_conj_mono S3 (self_imp _))) ?_
    exact ex_rename (conj_under' (all_under (vac_eq c P Z lcZ.ne' lPZ.ne')
        (imp_under (selfU _ _) (relR c P Z))) (relL c P b))
      (vac_conj (vac_all Z (vac_imp (vac_all W (vac_imp (vac_rel W Z P lPW.ne lPZ.ne) (vac_rel W a P lPW.ne laP.ne')))
        (vac_rel Z c P lPZ.ne lcP.ne'))) (vac_rel c b P lcP.ne' lbP.ne'))
      (vac_ex P (vac_conj (vac_all Z (vac_imp (vac_all W (vac_imp (vac_rel W Z c lcW.ne lcZ.ne) (vac_rel W a c lcW.ne lac.ne')))
        (vac_rel Z P c lcZ.ne lcP.ne))) (vac_rel P b c lcP.ne lbc.ne')))
  -- S6: the element clause, rename a ↦ Y
  have S6 : CProv (wim (wal a (wim (wel a b) (conj (ex c (conj (wal b (wim (wal c (wim (wel c b) (wel c a)))
      (wel b c))) (wel c b))) (wal c (wim (wel c a) (wel c b))))))
      (wal Y (wim (wel Y b) (conj (ex P (conj (wal Z (wim (wal W (wim (wel W Z) (wel W Y))) (wel Z P)))
        (wel P b))) (wal P (wim (wel P Y) (wel P b))))))) := by
    refine compose (all_mono a (ValidatorNativeGicCongruence254.cProv_imp_mono (self_imp _)
      (ValidatorNativeGicCongruence254.cProv_conj_mono S5 S4))) ?_
    have vPh : Vac P (weq a Y) := vac_eq a Y P laP.ne' lYP.ne'
    have vZh : Vac Z (weq a Y) := vac_eq a Y Z laZ.ne' lYZ.ne'
    have vWh : Vac W (weq a Y) := vac_eq a Y W laW.ne' lYW.ne'
    refine all_rename (imp_under (relL' a Y b) (conj_under'
      (ex_under vPh (conj_under' (all_under vZh (imp_under (all_under vWh
        (imp_under (selfU _ _) (relR' a Y W))) (selfU _ _))) (selfU _ _)))
      (all_under vPh (imp_under (relR' a Y P) (selfU _ _))))) ?_ ?_
    · exact vac_imp (vac_rel Y b a laY.ne lab.ne)
        (vac_conj (vac_ex P (vac_conj (vac_all Z (vac_imp (vac_all W (vac_imp (vac_rel W Z a laW.ne laZ.ne)
          (vac_rel W Y a laW.ne laY.ne))) (vac_rel Z P a laZ.ne laP.ne))) (vac_rel P b a laP.ne lab.ne)))
          (vac_all P (vac_imp (vac_rel P Y a laP.ne laY.ne) (vac_rel P b a laP.ne lab.ne))))
    · exact vac_all a (vac_imp (vac_rel a b Y laY.ne' lbY.ne')
        (vac_conj (vac_ex P (vac_conj (vac_all Z (vac_imp (vac_all W (vac_imp (vac_rel W Z Y lYW.ne lYZ.ne)
          (vac_rel W a Y lYW.ne laY.ne'))) (vac_rel Z P Y lYZ.ne lYP.ne))) (vac_rel P b Y lYP.ne lbY.ne')))
          (vac_all P (vac_imp (vac_rel P a Y lYP.ne laY.ne') (vac_rel P b Y lYP.ne lbY.ne')))))
  -- S7: the container, rename b ↦ C
  have S7 : CProv (ex C (conj (wal Y (wim (wel Y C) (conj (ex P (conj (wal Z (wim (wal W (wim (wel W Z)
      (wel W Y))) (wel Z P))) (wel P C))) (wal P (wim (wel P Y) (wel P C)))))) (wel c C))) := by
    refine cProv_mp ?_ (cProv_mp (ex_mono b (ValidatorNativeGicCongruence254.cProv_conj_mono S6 (self_imp _))) hL)
    have vYh : Vac Y (weq b C) := vac_eq b C Y lbY.ne' lCY.ne'
    have vPh : Vac P (weq b C) := vac_eq b C P lbP.ne' lCP.ne'
    refine ex_rename (conj_under' (all_under vYh (imp_under (relR' b C Y) (conj_under'
      (ex_under vPh (conj_under' (selfU _ _) (relR b C P)))
      (all_under vPh (imp_under (selfU _ _) (relR b C P)))))) (relR b C c)) ?_ ?_
    · exact vac_conj (vac_all Y (vac_imp (vac_rel Y b C lCY.ne lbC.ne')
        (vac_conj (vac_ex P (vac_conj (vac_all Z (vac_imp (vac_all W (vac_imp (vac_rel W Z C lCW.ne lCZ.ne)
          (vac_rel W Y C lCW.ne lCY.ne))) (vac_rel Z P C lCZ.ne lCP.ne))) (vac_rel P b C lCP.ne lbC.ne')))
          (vac_all P (vac_imp (vac_rel P Y C lCP.ne lCY.ne) (vac_rel P b C lCP.ne lbC.ne'))))))
        (vac_rel c b C lcC.ne' lbC.ne')
    · exact vac_ex C (vac_conj (vac_all Y (vac_imp (vac_rel Y C b lbY.ne lbC.ne)
        (vac_conj (vac_ex P (vac_conj (vac_all Z (vac_imp (vac_all W (vac_imp (vac_rel W Z b lbW.ne lbZ.ne)
          (vac_rel W Y b lbW.ne lbY.ne))) (vac_rel Z P b lbZ.ne lbP.ne))) (vac_rel P C b lbP.ne lbC.ne)))
          (vac_all P (vac_imp (vac_rel P Y b lbP.ne lbY.ne) (vac_rel P C b lbP.ne lbC.ne))))))
        (vac_rel c C b lbc.ne lbC.ne))
  -- S8: restructure
  have S8 : CProv (ex C (conj (wel c C) (wal Y (wim (neg (neg (wel Y C)))
      (conj (wal P (wim (neg (neg (wel P Y))) (wel P C)))
        (ex P (conj (wel P C) (wal Z (wim (neg (ex W (conj (wel W Z) (neg (wel W Y)))))
          (wel Z P)))))))))) := by
    have mZ := all_mono Z (ValidatorNativeGicCongruence254.cProv_imp_mono (negEx_all W Z Y)
      (self_imp (wel Z P)))
    have mPex := ex_mono P (compose (conj_swap _ _)
      (ValidatorNativeGicCongruence254.cProv_conj_mono (self_imp (wel P C)) mZ))
    have mPsub := all_mono P (ValidatorNativeGicCongruence254.cProv_imp_mono (dneg (wel P Y))
      (self_imp (wel P C)))
    have mIn := compose (conj_swap _ _) (ValidatorNativeGicCongruence254.cProv_conj_mono mPsub mPex)
    have mY := all_mono Y (ValidatorNativeGicCongruence254.cProv_imp_mono (dneg (wel Y C)) mIn)
    have mC := ex_mono C (compose (conj_swap _ _)
      (ValidatorNativeGicCongruence254.cProv_conj_mono (self_imp (wel c C)) mY))
    exact cProv_mp mC S7
  -- S9: generalize the point and rename it to X
  refine cProv_mp (all_rename (ex_under (vac_eq c X C lcC.ne' lXC.ne')
      (conj_under' (relL c X C) (selfU _ _))) ?_ ?_) (cProv_gen c S8)
  · exact vac_ex C (vac_conj (vac_rel X C c lcX.ne lcC.ne) (vac_all Y (vac_imp
      (vac_neg (vac_neg (vac_rel Y C c lcY.ne lcC.ne)))
      (vac_conj (vac_all P (vac_imp (vac_neg (vac_neg (vac_rel P Y c lcP.ne lcY.ne))) (vac_rel P C c lcP.ne lcC.ne)))
        (vac_ex P (vac_conj (vac_rel P C c lcP.ne lcC.ne) (vac_all Z (vac_imp
          (vac_neg (vac_ex W (vac_conj (vac_rel W Z c lcW.ne lcZ.ne) (vac_neg (vac_rel W Y c lcW.ne lcY.ne)))))
          (vac_rel Z P c lcZ.ne lcP.ne)))))))))
  · exact vac_all c (vac_ex C (vac_conj (vac_rel c C X lcX.ne' lXC.ne) (vac_all Y (vac_imp
      (vac_neg (vac_neg (vac_rel Y C X lXY.ne lXC.ne)))
      (vac_conj (vac_all P (vac_imp (vac_neg (vac_neg (vac_rel P Y X lXP.ne lXY.ne))) (vac_rel P C X lXP.ne lXC.ne)))
        (vac_ex P (vac_conj (vac_rel P C X lXP.ne lXC.ne) (vac_all Z (vac_imp
          (vac_neg (vac_ex W (vac_conj (vac_rel W Z X lXW.ne lXZ.ne) (vac_neg (vac_rel W Y X lXW.ne lXY.ne)))))
          (vac_rel Z P X lXZ.ne lXP.ne))))))))))



lemma cast_fin_three : (((3 : Fin 6) : ℕ) : V) = 3 := by
  rw [show ((3 : Fin 6) : ℕ) = 3 from rfl]; simp

/-- The encoded container axiom at stream `t`. -/
lemma encode_containerAx (F t : V) :
    encode F 0 t (⌜NativeSet.containerAx⌝ : V) =
      wal t (ex (t + 2) (conj (wel t (t + 2)) (wal (t + 2 + 2) (wim (neg (neg (wel (t + 2 + 2) (t + 2))))
        (conj (wal (t + 2 + 2 + 2) (wim (neg (neg (wel (t + 2 + 2 + 2) (t + 2 + 2)))) (wel (t + 2 + 2 + 2) (t + 2))))
          (ex (t + 2 + 2 + 2) (conj (wel (t + 2 + 2 + 2) (t + 2)) (wal (t + 2 + 2 + 2 + 2)
            (wim (neg (ex (t + 2 + 2 + 2 + 2 + 2) (conj (wel (t + 2 + 2 + 2 + 2 + 2) (t + 2 + 2 + 2 + 2))
              (neg (wel (t + 2 + 2 + 2 + 2 + 2) (t + 2 + 2))))))
              (wel (t + 2 + 2 + 2 + 2) (t + 2 + 2 + 2))))))))))) := by
  rw [quote_sentence, show (⌜(Rewriting.emb NativeSet.containerAx : SetTheoryProposition)⌝ :
    Bootstrapping.Formula V ℒₛₑₜ) =
    ∀⁰ ∃⁰ (memA 1 0 ⋏ (∀⁰ (nmemA 0 1 ⋎ ((∀⁰ (nmemA 0 1 ⋎ memA 0 2)) ⋏
      (∃⁰ (memA 0 2 ⋏ (∀⁰ ((∃⁰ (memA 0 1 ⋏ nmemA 0 3)) ⋎ memA 0 1)))))))) from rfl]
  simp only [encT_all, encT_exs, encT_and, encT_or, encode_memA, encode_nmemA, Fin.val_zero, Fin.val_one,
    Fin.val_two, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, nth_adjoin_zero, nth_adjoin_one,
    nth_two_cons, nth_three_cons, cast_fin_three]

/-- **The container axiom is a validator theorem** at every odd environment and even stream. -/
theorem container_ax {F s : V} (hF : OddEnv F) (hs : s % 2 = 0) :
    CProv (encode F 0 s (⌜NativeSet.containerAx⌝ : V)) := by
  have h6 : CProv (encode F 0 6 (⌜NativeSet.containerAx⌝ : V)) := by
    rw [encode_containerAx]
    exact container_core (a := 1) (b := 3) (c := 5) (by norm_num) (by norm_num) (by norm_num)
      (lt_add_two _) (lt_add_two _) (lt_add_two _) (lt_add_two _) (lt_add_two _)
  have hp : IsFormula ℒₛₑₜ (⌜NativeSet.containerAx⌝ : V) := by simp
  have e6 : (6 : V) % 2 = 0 := by
    rw [show (6 : V) = 2 * 3 by norm_num]; simp
  exact cProv_mp (encode_formula_relabel hp F 6 s (streamFree_even e6 hF) (streamFree_even hs hF)).1 h6

end LeanProofs.ZFCinPA.R2Fixed
