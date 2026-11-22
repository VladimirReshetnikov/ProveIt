import IPRADerivations.Algebra.QuadraticIntegerOrder

/-!
# The integer scalar embedding in the actual positive quadratic stage

The original scalar map a ↦ (a,0) preserves coefficient arithmetic and
reflects the SAME computed sign-zero equality and order. Signed inputs
are arbitrary difference pairs; neither input normalization nor a
supplied scalar-sign law is assumed. The numerical radicand is positive.
This is one integer ground stage of lem:orderedextension, not the
rational ground field or an iterated radical tower.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticIntegerEmbedding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open QuadraticSignCertificates (encode first second equal cone add negative multiply zeroCode
  first_value second_value zero_first_value zero_second_value multiply_first multiply_second
  negative_first negative_second positivePart negativePart parts_value parts_disjoint parts_zero_value)
open QuadraticConeOrder (equal_of_values equal_symm equal_trans equal_first equal_second
  add_first add_second)
open QuadraticIntegerOrder (positive isZero isNegative difference equivalent less
  cone_positive positive_value_congr zero_value_congr zero_isZero zero_negative
  positive_negative negative_positive positive_zero_absurd one_two_absurd)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def integer (a : ZT n) : PTm n := encode a (ZT.ofNat zero)
@[simp] theorem subst_integer {l : ℕ} (σ : Fin n → PTm l) (a : ZT n) :
    Syn.subst σ (integer a) = integer (a.subst σ) := by simp [integer]

theorem integer_first (a : ZT n) : ZT.toZ Γ (first (integer a)) = ZT.toZ Γ a := by
  exact first_value _ _
theorem integer_second (a : ZT n) : ZT.toZ Γ (second (integer a)) = 0 := by
  rw [integer,second_value,ZT.toZ_ofNat]; ipra_simps
theorem integer_add (a b : ZT n) : Γ ⊢[PRAAx] equal (add (integer a) (integer b)) (integer (a+b)) := by
  apply equal_of_values <;> simp only [add_first,add_second,integer_first,integer_second,ZT.toZ_add] <;> ring
theorem integer_negative (a : ZT n) : Γ ⊢[PRAAx] equal (negative (integer a)) (integer (-a)) := by
  apply equal_of_values <;> simp only [negative_first,negative_second,integer_first,integer_second,ZT.toZ_neg] <;> ring
theorem integer_multiply (d : PTm n) (a b : ZT n) : Γ ⊢[PRAAx]
    equal (multiply d (integer a) (integer b)) (integer (a*b)) := by
  apply equal_of_values <;> simp only [multiply_first,multiply_second,integer_first,integer_second,ZT.toZ_mul] <;> ring
theorem integer_difference (a b : ZT n) : Γ ⊢[PRAAx]
    equal (difference (integer a) (integer b)) (integer (a-b)) := by
  apply equal_of_values <;> simp only [difference,add_first,add_second,negative_first,negative_second,integer_first,integer_second,ZT.toZ_sub] <;> ring
theorem integer_zero (a : ZT n) (ha : Γ ⊢[PRAAx] ZT.eq a (ZT.ofNat zero)) : Γ ⊢[PRAAx] equal (integer a) zeroCode := by
  apply equal_of_values
  · rw [integer_first,zero_first_value,ZT.toZ_eq ha,ZT.toZ_ofNat]; ipra_simps
  · rw [integer_second,zero_second_value]

theorem integer_cone (a : ZT n) (ha : Γ ⊢[PRAAx] zle (ZT.ofNat one) a) : Γ ⊢[PRAAx] cone (integer a) := by
  have hs : Nonneg Γ (ZT.toZ Γ a-1) := by
    simpa only [zsl_def,ZT.toZ_ofNat,Q.mk_one,map_one] using nn_zsl ha
  apply QuadraticConeOrder.cone_of_nonnegative
  · rw [integer_first]
    have h := nn_add nn_one hs
    convert h using 1 <;> ring
  · rw [integer_second]; exact nn_zero
  · simp only [integer_first,integer_second]
    simpa only [_root_.add_zero] using hs
theorem integer_positive (d : PTm n) (a : ZT n) (hd : Γ ⊢[PRAAx] le one d)
    (ha : Γ ⊢[PRAAx] zle (ZT.ofNat one) a) : Γ ⊢[PRAAx] positive d (integer a) :=
  cone_positive _ _ hd (integer_cone a ha)
theorem integer_isZero (d : PTm n) (a : ZT n) (hd : Γ ⊢[PRAAx] le one d)
    (ha : Γ ⊢[PRAAx] ZT.eq a (ZT.ofNat zero)) : Γ ⊢[PRAAx] isZero d (integer a) :=
  zero_value_congr _ _ _ hd (equal_symm (integer_zero a ha)) (zero_isZero d hd)

theorem positive_part_strict (a : ZT n) (hp : Γ ⊢[PRAAx] positivePart a ≐ succ (PTm.pred (positivePart a)))
    (hn : Γ ⊢[PRAAx] negativePart a ≐ zero) : Γ ⊢[PRAAx] zle (ZT.ofNat one) a := by
  apply zle_of_comb (𝔞(PTm.pred (positivePart a)))
  · rw [parts_value,natEq hp,natEq hn,ZT.toZ_ofNat]; ipra_simps; ring
  · exact nn_term _
theorem negative_part_strict (a : ZT n) (hp : Γ ⊢[PRAAx] positivePart a ≐ zero)
    (hn : Γ ⊢[PRAAx] negativePart a ≐ succ (PTm.pred (negativePart a))) : Γ ⊢[PRAAx] zle (ZT.ofNat one) (-a) := by
  apply zle_of_comb (𝔞(PTm.pred (negativePart a)))
  · rw [ZT.toZ_neg,parts_value,natEq hp,natEq hn,ZT.toZ_ofNat]; ipra_simps; ring
  · exact nn_term _
theorem integer_trichotomy (a : ZT n) : Γ ⊢[PRAAx]
    zle (ZT.ofNat one) a ⋎ (zle (ZT.ofNat one) (-a) ⋎ ZT.eq a (ZT.ofNat zero)) := by
  refine .orE (parts_disjoint a) ?_ ?_
  · refine .orE (zero_or_succ (negativePart a)) ?_ ?_
    · exact .orI₂ (.orI₂ (ZT.derive (by
        rw [parts_zero_value a Prf.hyp1 Prf.hyp0,ZT.toZ_ofNat]; ipra_simps)))
    · exact .orI₂ (.orI₁ (negative_part_strict a Prf.hyp1 Prf.hyp0))
  · refine .orE (zero_or_succ (positivePart a)) ?_ ?_
    · exact .orI₂ (.orI₂ (ZT.derive (by
        rw [parts_zero_value a Prf.hyp0 Prf.hyp1,ZT.toZ_ofNat]; ipra_simps)))
    · exact .orI₁ (positive_part_strict a Prf.hyp0 Prf.hyp1)

theorem integer_zero_reflect (d : PTm n) (a : ZT n) (hd : Γ ⊢[PRAAx] le one d)
    (hz : Γ ⊢[PRAAx] isZero d (integer a)) : Γ ⊢[PRAAx] ZT.eq a (ZT.ofNat zero) := by
  refine .orE (integer_trichotomy a) ?_ ?_
  · exact .botE _ (positive_zero_absurd _ _ (integer_positive _ _ hd.wk Prf.hyp0) hz.wk)
  · refine .orE Prf.hyp0 ?_ Prf.hyp0
    exact .botE _ (positive_zero_absurd _ _ (integer_positive _ _ hd.wk.wk Prf.hyp0)
      (zero_value_congr _ _ _ hd.wk.wk (integer_negative a) (zero_negative _ _ hd.wk.wk hz.wk.wk)))
theorem integer_zero_iff (d : PTm n) (a : ZT n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    Fm.iff (isZero d (integer a)) (ZT.eq a (ZT.ofNat zero)) :=
  .andI (.impI (integer_zero_reflect _ _ hd.wk Prf.hyp0)) (.impI (integer_isZero _ _ hd.wk Prf.hyp0))

theorem integer_positive_reflect (d : PTm n) (a : ZT n) (hd : Γ ⊢[PRAAx] le one d)
    (hp : Γ ⊢[PRAAx] positive d (integer a)) : Γ ⊢[PRAAx] zle (ZT.ofNat one) a := by
  refine .orE (integer_trichotomy a) Prf.hyp0 ?_
  refine .orE Prf.hyp0 ?_ ?_
  · have h : zle (ZT.ofNat one) (-a) :: (zle (ZT.ofNat one) (-a) ⋎ ZT.eq a (ZT.ofNat zero)) :: Γ ⊢[PRAAx]
        positive d (negative (integer a)) :=
      positive_value_congr _ _ _ hd.wk.wk (equal_symm (integer_negative a)) (integer_positive _ _ hd.wk.wk Prf.hyp0)
    exact one_two_absurd _ (h.eqSymm.eqTrans (positive_negative _ _ hd.wk.wk hp.wk.wk))
  · exact .botE _ (positive_zero_absurd _ _ hp.wk.wk (integer_isZero _ _ hd.wk.wk Prf.hyp0))
theorem integer_positive_iff (d : PTm n) (a : ZT n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    Fm.iff (positive d (integer a)) (zle (ZT.ofNat one) a) :=
  .andI (.impI (integer_positive_reflect _ _ hd.wk Prf.hyp0)) (.impI (integer_positive _ _ hd.wk Prf.hyp0))

theorem integer_equal (a b : ZT n) (h : Γ ⊢[PRAAx] ZT.eq a b) : Γ ⊢[PRAAx] equal (integer a) (integer b) := by
  apply equal_of_values
  · rw [integer_first,integer_first]; exact ZT.toZ_eq h
  · rw [integer_second,integer_second]
theorem integer_equivalent (d : PTm n) (a b : ZT n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] ZT.eq a b) : Γ ⊢[PRAAx] equivalent d (integer a) (integer b) :=
  QuadraticIntegerOrder.coefficient_equal_equivalent _ _ _ hd (integer_equal _ _ h)
theorem integer_equivalent_reflect (d : PTm n) (a b : ZT n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] equivalent d (integer a) (integer b)) : Γ ⊢[PRAAx] ZT.eq a b := by
  have hz := integer_zero_reflect d (a-b) hd (zero_value_congr _ _ _ hd (integer_difference a b) h)
  apply ZT.derive
  have hv := ZT.toZ_eq hz
  simp only [ZT.toZ_sub,ZT.toZ_ofNat,Q.mk_zero,map_zero] at hv
  linear_combination hv
theorem integer_equivalent_iff (d : PTm n) (a b : ZT n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    Fm.iff (equivalent d (integer a) (integer b)) (ZT.eq a b) :=
  .andI (.impI (integer_equivalent_reflect _ _ _ hd.wk Prf.hyp0)) (.impI (integer_equivalent _ _ _ hd.wk Prf.hyp0))

theorem negative_value_congr (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (he : Γ ⊢[PRAAx] equal x y) (h : Γ ⊢[PRAAx] isNegative d x) : Γ ⊢[PRAAx] isNegative d y :=
  (QuadraticConeOrder.sign_congr _ _ _ hd he).eqSymm.eqTrans h
theorem integer_isNegative (d : PTm n) (a : ZT n) (hd : Γ ⊢[PRAAx] le one d)
    (ha : Γ ⊢[PRAAx] zle (ZT.ofNat one) (-a)) : Γ ⊢[PRAAx] isNegative d (integer a) :=
  negative_value_congr _ _ _ hd (QuadraticConeOrder.negative_negative (integer a))
    (positive_negative _ _ hd (positive_value_congr _ _ _ hd (equal_symm (integer_negative a)) (integer_positive _ _ hd ha)))
theorem integer_negative_reflect (d : PTm n) (a : ZT n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] isNegative d (integer a)) : Γ ⊢[PRAAx] zle (ZT.ofNat one) (-a) :=
  integer_positive_reflect _ _ hd (positive_value_congr _ _ _ hd (integer_negative a) (negative_positive _ _ hd h))
theorem integer_negative_iff (d : PTm n) (a : ZT n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    Fm.iff (isNegative d (integer a)) (zle (ZT.ofNat one) (-a)) :=
  .andI (.impI (integer_negative_reflect _ _ hd.wk Prf.hyp0)) (.impI (integer_isNegative _ _ hd.wk Prf.hyp0))

theorem integer_tag_classification (a : ZT n) : Γ ⊢[PRAAx]
    ((QuadraticSignCertificates.tag a ≐ one) ⋏ zle (ZT.ofNat one) a) ⋎
      (((QuadraticSignCertificates.tag a ≐ two) ⋏ zle (ZT.ofNat one) (-a)) ⋎
        ((QuadraticSignCertificates.tag a ≐ zero) ⋏ ZT.eq a (ZT.ofNat zero))) := by
  refine .orE (parts_disjoint a) ?_ ?_
  · refine .orE (zero_or_succ (negativePart a)) ?_ ?_
    · exact .orI₂ (.orI₂ (.andI (QuadraticSignCertificates.tag_zero a Prf.hyp1 Prf.hyp0)
        (ZT.derive (by rw [parts_zero_value a Prf.hyp1 Prf.hyp0,ZT.toZ_ofNat]; ipra_simps))))
    · exact .orI₂ (.orI₁ (.andI (QuadraticSignCertificates.tag_negative a Prf.hyp1 Prf.hyp0)
        (negative_part_strict a Prf.hyp1 Prf.hyp0)))
  · refine .orE (zero_or_succ (positivePart a)) ?_ ?_
    · exact .orI₂ (.orI₂ (.andI (QuadraticSignCertificates.tag_zero a Prf.hyp0 Prf.hyp1)
        (ZT.derive (by rw [parts_zero_value a Prf.hyp0 Prf.hyp1,ZT.toZ_ofNat]; ipra_simps))))
    · exact .orI₁ (.andI (QuadraticSignCertificates.tag_positive a Prf.hyp0 Prf.hyp1)
        (positive_part_strict a Prf.hyp0 Prf.hyp1))
theorem integer_sign (d : PTm n) (a : ZT n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    QuadraticSignCertificates.sign d (integer a) ≐ QuadraticSignCertificates.tag a := by
  refine .orE (integer_tag_classification a) ?_ ?_
  · exact (integer_positive _ _ hd.wk (.andE₂ Prf.hyp0)).eqTrans (Prf.andE₁ Prf.hyp0).eqSymm
  · refine .orE Prf.hyp0 ?_ ?_
    · exact (integer_isNegative _ _ hd.wk.wk (.andE₂ Prf.hyp0)).eqTrans (Prf.andE₁ Prf.hyp0).eqSymm
    · exact (integer_isZero _ _ hd.wk.wk (.andE₂ Prf.hyp0)).eqTrans (Prf.andE₁ Prf.hyp0).eqSymm

theorem integer_less (d : PTm n) (a b : ZT n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] zle (ZT.ofNat one) (b-a)) : Γ ⊢[PRAAx] less d (integer a) (integer b) :=
  positive_value_congr _ _ _ hd (equal_symm (integer_difference b a)) (integer_positive _ _ hd h)
theorem integer_less_reflect (d : PTm n) (a b : ZT n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] less d (integer a) (integer b)) : Γ ⊢[PRAAx] zle (ZT.ofNat one) (b-a) :=
  integer_positive_reflect _ _ hd (positive_value_congr _ _ _ hd (integer_difference b a) h)
theorem integer_less_iff (d : PTm n) (a b : ZT n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    Fm.iff (less d (integer a) (integer b)) (zle (ZT.ofNat one) (b-a)) :=
  .andI (.impI (integer_less_reflect _ _ _ hd.wk Prf.hyp0)) (.impI (integer_less _ _ _ hd.wk Prf.hyp0))

/-! The embedding program takes both numerical parts of the original
signed input. A separate PR3 output returns it and its actual stage sign. -/
def embedding (p q : PTm n) : PTm n := integer ⟨p,q⟩
def embeddingF : PR 2 := PTm.toPR (embedding (var 0) (var 1))
def embed (p q : PTm n) : PTm n := ap2 embeddingF p q
def output (d p q : PTm n) : PTm n := pairT (embedding p q) (QuadraticSignCertificates.sign d (embedding p q))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (d p q : PTm n) : PTm n := ap3 outputF d p q
@[simp] theorem subst_embedding {l : ℕ} (σ : Fin n → PTm l) (p q : PTm n) :
    Syn.subst σ (embedding p q) = embedding (Syn.subst σ p) (Syn.subst σ q) := by simp [embedding,ZT.subst]
@[simp] theorem subst_embed {l : ℕ} (σ : Fin n → PTm l) (p q : PTm n) :
    Syn.subst σ (embed p q) = embed (Syn.subst σ p) (Syn.subst σ q) := by simp [embed]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (d p q : PTm n) :
    Syn.subst σ (output d p q) = output (Syn.subst σ d) (Syn.subst σ p) (Syn.subst σ q) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (d p q : PTm n) :
    Syn.subst σ (run d p q) = run (Syn.subst σ d) (Syn.subst σ p) (Syn.subst σ q) := by simp [run]
theorem embedding_at (p q : PTm n) : Γ ⊢[PRAAx] embed p q ≐ embedding p q := by
  simpa [embed,embeddingF,ap2] using toPR_eq (Γ := Γ) (embedding (var 0) (var 1) : PTm 2) ![p,q]
theorem program_at (d p q : PTm n) : Γ ⊢[PRAAx] run d p q ≐ output d p q := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![d,p,q]
theorem returned_integer (d p q : PTm n) : Γ ⊢[PRAAx] fstT (run d p q) ≐ embedding p q :=
  (congrFst (program_at _ _ _)).eqTrans (fst_pair _ _)
theorem returned_sign (d p q : PTm n) : Γ ⊢[PRAAx] sndT (run d p q) ≐ QuadraticSignCertificates.sign d (embedding p q) :=
  (congrSnd (program_at _ _ _)).eqTrans (snd_pair _ _)
theorem returned_zero_iff (d p q : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    Fm.iff (sndT (run d p q) ≐ zero) (ZT.eq (⟨p,q⟩ : ZT n) (ZT.ofNat zero)) :=
  .andI (.impI (integer_zero_reflect _ _ hd.wk ((returned_sign _ _ _).wk.eqSymm.eqTrans Prf.hyp0)))
    (.impI ((returned_sign _ _ _).wk.eqTrans (integer_isZero _ _ hd.wk Prf.hyp0)))
theorem returned_positive_iff (d p q : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    Fm.iff (sndT (run d p q) ≐ one) (zle (ZT.ofNat one) (⟨p,q⟩ : ZT n)) :=
  .andI (.impI (integer_positive_reflect _ _ hd.wk ((returned_sign _ _ _).wk.eqSymm.eqTrans Prf.hyp0)))
    (.impI ((returned_sign _ _ _).wk.eqTrans (integer_positive _ _ hd.wk Prf.hyp0)))

theorem integer_scalar_arithmetic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (equal (add (embedding (var 1) (var 2)) (embedding (var 3) (var 4)))
        (integer ((⟨var 1,var 2⟩ : ZT 5)+(⟨var 3,var 4⟩ : ZT 5))) ⋏
      (equal (negative (embedding (var 1) (var 2))) (integer (-(⟨var 1,var 2⟩ : ZT 5))) ⋏
        equal (multiply (var 0) (embedding (var 1) (var 2)) (embedding (var 3) (var 4)))
          (integer ((⟨var 1,var 2⟩ : ZT 5)*(⟨var 3,var 4⟩ : ZT 5))))) :=
  closeUniv 5 (.andI (integer_add _ _) (.andI (integer_negative _) (integer_multiply _ _ _)))
theorem integer_scalar_zero_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ Fm.iff (isZero (var 0) (embedding (var 1) (var 2)))
      (ZT.eq (⟨var 1,var 2⟩ : ZT 3) (ZT.ofNat zero))) :=
  closeUniv 3 (.impI (integer_zero_iff _ _ Prf.hyp0))
theorem integer_scalar_exact_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ QuadraticSignCertificates.sign (var 0) (embedding (var 1) (var 2)) ≐
      QuadraticSignCertificates.tag (⟨var 1,var 2⟩ : ZT 3)) := closeUniv 3 (.impI (integer_sign _ _ Prf.hyp0))
theorem integer_scalar_positive_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ Fm.iff (positive (var 0) (embedding (var 1) (var 2)))
      (zle (ZT.ofNat one) (⟨var 1,var 2⟩ : ZT 3))) :=
  closeUniv 3 (.impI (integer_positive_iff _ _ Prf.hyp0))
theorem integer_scalar_negative_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ Fm.iff (isNegative (var 0) (embedding (var 1) (var 2)))
      (zle (ZT.ofNat one) (-(⟨var 1,var 2⟩ : ZT 3)))) :=
  closeUniv 3 (.impI (integer_negative_iff _ _ Prf.hyp0))
theorem integer_scalar_injective_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ Fm.iff (equivalent (var 0) (embedding (var 1) (var 2)) (embedding (var 3) (var 4)))
      (ZT.eq (⟨var 1,var 2⟩ : ZT 5) (⟨var 3,var 4⟩ : ZT 5))) :=
  closeUniv 5 (.impI (integer_equivalent_iff _ _ _ Prf.hyp0))
theorem integer_scalar_order_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ Fm.iff (less (var 0) (embedding (var 1) (var 2)) (embedding (var 3) (var 4)))
      (zle (ZT.ofNat one) ((⟨var 3,var 4⟩ : ZT 5)-(⟨var 1,var 2⟩ : ZT 5)))) :=
  closeUniv 5 (.impI (integer_less_iff _ _ _ Prf.hyp0))
theorem integer_embedding_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (embed (var 0) (var 1) ≐ embedding (var 0) (var 1)) := closeUniv 2 (embedding_at _ _)
theorem integer_stage_sign_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem returned_integer_zero_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ Fm.iff (sndT (run (var 0) (var 1) (var 2)) ≐ zero)
      (ZT.eq (⟨var 1,var 2⟩ : ZT 3) (ZT.ofNat zero))) := closeUniv 3 (.impI (returned_zero_iff _ _ _ Prf.hyp0))
theorem returned_integer_positive_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ Fm.iff (sndT (run (var 0) (var 1) (var 2)) ≐ one)
      (zle (ZT.ofNat one) (⟨var 1,var 2⟩ : ZT 3))) := closeUniv 3 (.impI (returned_positive_iff _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Algebra.QuadraticIntegerEmbedding
