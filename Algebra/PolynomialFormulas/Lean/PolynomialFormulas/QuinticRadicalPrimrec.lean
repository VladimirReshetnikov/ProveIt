import PolynomialFormulas.QuinticRadicalDecidability

set_option maxHeartbeats 800000

open Denumerable Encodable Function

/-!
# Primitive-recursive certificates for the quintic searches

This module proves that the coefficient transformations and finite searches
implemented in `QuinticRadicalDecidability` are genuinely primitive recursive.
The interval searches are enumerated through the canonical zig-zag coding of
integers, so the proofs do not rely on an unverified `Decidable` shortcut.
-/

namespace LeanProofs.PolynomialFormulas.QuinticRadicalPrimrec

open LeanProofs.PolynomialFormulas.QuinticRadicalDecidability
open LeanProofs.PolynomialFormulas.QuinticRadicalDecidability.IntegerQuintic
open LeanProofs.PolynomialFormulas.QuinticRadicalDecidability.MonicQuintic

/-! ## Primitive-recursive integer arithmetic -/

theorem int_ofNat_primrec : Primrec Int.ofNat := by
  apply Primrec.encode_iff.mp
  exact Primrec.nat_double.of_eq fun n => by
    change 2 * n = Equiv.intEquivNat (Int.ofNat n)
    rfl

theorem int_negSucc_primrec : Primrec Int.negSucc := by
  apply Primrec.encode_iff.mp
  exact Primrec.nat_double_succ.of_eq fun n => by
    change 2 * n + 1 = Equiv.intEquivNat (Int.negSucc n)
    rfl

theorem intToSum_primrec : Primrec Equiv.intEquivNatSumNat := by
  apply Primrec.encode_iff.mp
  exact (Primrec.encode : Primrec fun z : ℤ => Encodable.encode z).of_eq fun z => by
    cases z <;> rfl

theorem sumToInt_primrec : Primrec Equiv.intEquivNatSumNat.symm := by
  apply Primrec.encode_iff.mp
  exact (Primrec.encode : Primrec fun s : ℕ ⊕ ℕ => Encodable.encode s).of_eq fun s => by
    cases s <;> rfl

theorem int_natAbs_primrec : Primrec Int.natAbs := by
  let h : Primrec fun s : ℕ ⊕ ℕ => Sum.elim id Nat.succ s :=
    Primrec.sumCasesOn Primrec.id Primrec₂.right (Primrec.succ.comp Primrec₂.right)
  exact (h.comp intToSum_primrec).of_eq fun z => by cases z <;> rfl

theorem int_negOfNat_primrec : Primrec Int.negOfNat := by
  exact (Primrec.nat_casesOn Primrec.id (Primrec.const 0)
    (int_negSucc_primrec.comp₂ Primrec₂.right)).of_eq fun n => by cases n <;> rfl

theorem int_neg_primrec : Primrec Int.neg := by
  have h : Primrec fun s : ℕ ⊕ ℕ => Sum.elim Int.negOfNat
      (fun n => Int.ofNat (n + 1)) s :=
    Primrec.sumCasesOn Primrec.id
      (int_negOfNat_primrec.comp Primrec₂.right)
      (int_ofNat_primrec.comp (Primrec.succ.comp Primrec₂.right)).to₂
  exact (h.comp intToSum_primrec).of_eq fun z => by
    cases z with
    | ofNat n =>
        change Int.negOfNat n = -(Int.ofNat n)
        rfl
    | negSucc n =>
        change Int.ofNat (n + 1) = -(Int.negSucc n)
        rfl

theorem int_casesOn_primrec {α σ : Type*} [Primcodable α] [Primcodable σ]
    {f : α → ℤ} {g h : α → ℕ → σ} (hf : Primrec f)
    (hg : Primrec₂ g) (hh : Primrec₂ h) :
    Primrec fun a => match f a with
      | .ofNat n => g a n
      | .negSucc n => h a n := by
  exact (Primrec.sumCasesOn (intToSum_primrec.comp hf) hg hh).of_eq fun a => by
    cases hf' : f a with
    | ofNat n => change Sum.casesOn (Equiv.intEquivNatSumNat (Int.ofNat n)) (g a) (h a) = g a n; rfl
    | negSucc n => change Sum.casesOn (Equiv.intEquivNatSumNat (Int.negSucc n)) (g a) (h a) = h a n; rfl

theorem int_subNatNat_primrec : Primrec₂ Int.subNatNat := by
  have h : Primrec fun p : ℕ × ℕ => Int.subNatNat p.1 p.2 := by
    apply (Primrec.nat_casesOn
      (Primrec.nat_sub.comp Primrec.snd Primrec.fst)
      (int_ofNat_primrec.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
      (int_negSucc_primrec.comp₂ Primrec₂.right)).of_eq
    intro p
    simp only [Int.subNatNat]
    split <;> simp_all
  exact h.to₂

theorem int_add_primrec : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  have hpos : Primrec₂ fun (p : ℤ × ℤ) (m : ℕ) =>
      match p.2 with
      | .ofNat n => Int.ofNat (m + n)
      | .negSucc n => Int.subNatNat m (n + 1) := by
    change Primrec fun q : (ℤ × ℤ) × ℕ =>
      match q.1.2 with
      | .ofNat n => Int.ofNat (q.2 + n)
      | .negSucc n => Int.subNatNat q.2 (n + 1)
    apply int_casesOn_primrec (Primrec.snd.comp Primrec.fst)
    · exact (int_ofNat_primrec.comp
        (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
    · exact (int_subNatNat_primrec.comp₂
        (Primrec.snd.comp Primrec.fst).to₂
        (Primrec.succ.comp Primrec.snd).to₂)
  have hneg : Primrec₂ fun (p : ℤ × ℤ) (m : ℕ) =>
      match p.2 with
      | .ofNat n => Int.subNatNat n (m + 1)
      | .negSucc n => Int.negSucc (m + n + 1) := by
    change Primrec fun q : (ℤ × ℤ) × ℕ =>
      match q.1.2 with
      | .ofNat n => Int.subNatNat n (q.2 + 1)
      | .negSucc n => Int.negSucc (q.2 + n + 1)
    apply int_casesOn_primrec (Primrec.snd.comp Primrec.fst)
    · exact (int_subNatNat_primrec.comp₂ Primrec.snd.to₂
        (Primrec.succ.comp (Primrec.snd.comp Primrec.fst)).to₂)
    · exact (int_negSucc_primrec.comp₂
        (Primrec.succ.comp
          (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂)
  exact (int_casesOn_primrec Primrec.fst hpos hneg).to₂.of_eq fun m n => by
    cases m <;> cases n <;> rfl

theorem int_mul_primrec : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ) := by
  have hpos : Primrec₂ fun (p : ℤ × ℤ) (m : ℕ) =>
      match p.2 with
      | .ofNat n => Int.ofNat (m * n)
      | .negSucc n => Int.negOfNat (m * (n + 1)) := by
    change Primrec fun q : (ℤ × ℤ) × ℕ =>
      match q.1.2 with
      | .ofNat n => Int.ofNat (q.2 * n)
      | .negSucc n => Int.negOfNat (q.2 * (n + 1))
    apply int_casesOn_primrec (Primrec.snd.comp Primrec.fst)
    · exact (int_ofNat_primrec.comp
        (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
    · exact (int_negOfNat_primrec.comp
        (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst)
          (Primrec.succ.comp Primrec.snd))).to₂
  have hneg : Primrec₂ fun (p : ℤ × ℤ) (m : ℕ) =>
      match p.2 with
      | .ofNat n => Int.negOfNat ((m + 1) * n)
      | .negSucc n => Int.ofNat ((m + 1) * (n + 1)) := by
    change Primrec fun q : (ℤ × ℤ) × ℕ =>
      match q.1.2 with
      | .ofNat n => Int.negOfNat ((q.2 + 1) * n)
      | .negSucc n => Int.ofNat ((q.2 + 1) * (n + 1))
    apply int_casesOn_primrec (Primrec.snd.comp Primrec.fst)
    · exact (int_negOfNat_primrec.comp
        (Primrec.nat_mul.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd)).to₂
    · exact (int_ofNat_primrec.comp
        (Primrec.nat_mul.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.succ.comp Primrec.snd))).to₂
  exact (int_casesOn_primrec Primrec.fst hpos hneg).to₂.of_eq fun m n => by
    cases m <;> cases n <;> rfl

theorem int_sub_primrec : Primrec₂ ((· - ·) : ℤ → ℤ → ℤ) := by
  exact (int_add_primrec.comp₂ Primrec₂.left
    (int_neg_primrec.comp₂ Primrec₂.right)).of_eq fun _ _ => rfl

theorem int_pow_const_primrec (k : ℕ) : Primrec fun z : ℤ => z ^ k := by
  induction k with
  | zero => simpa using (Primrec.const (α := ℤ) (1 : ℤ))
  | succ k ih => simpa [pow_succ] using int_mul_primrec.comp ih Primrec.id

/-- A coding equivalence for the five integer coefficients of a monic quintic. -/
def monicQuinticEquiv : MonicQuintic ≃ ℤ × (ℤ × (ℤ × (ℤ × ℤ))) where
  toFun f := (f.B, (f.C, (f.D, (f.E, f.H))))
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩
  left_inv f := by cases f; rfl
  right_inv t := by rcases t with ⟨B, C, D, E, H⟩; rfl

instance : Primcodable MonicQuintic :=
  Primcodable.ofEquiv (ℤ × (ℤ × (ℤ × (ℤ × ℤ)))) monicQuinticEquiv

theorem monicQuinticEquiv_primrec : Primrec monicQuinticEquiv :=
  Primrec.of_equiv

theorem monicQuinticEquiv_symm_primrec : Primrec monicQuinticEquiv.symm :=
  Primrec.of_equiv_symm

theorem monicQuintic_B_primrec : Primrec MonicQuintic.B :=
  Primrec.fst.comp monicQuinticEquiv_primrec

theorem monicQuintic_C_primrec : Primrec MonicQuintic.C :=
  (Primrec.fst.comp Primrec.snd).comp monicQuinticEquiv_primrec

theorem monicQuintic_D_primrec : Primrec MonicQuintic.D :=
  (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp monicQuinticEquiv_primrec

theorem monicQuintic_E_primrec : Primrec MonicQuintic.E :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).comp
    monicQuinticEquiv_primrec

theorem monicQuintic_H_primrec : Primrec MonicQuintic.H :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).comp
    monicQuinticEquiv_primrec

theorem monicize_primrec : Primrec monicize := by
  have ht : Primrec fun f : IntegerQuintic =>
      (f 4, (f 3 * f 5, (f 2 * f 5 ^ 2, (f 1 * f 5 ^ 3, f 0 * f 5 ^ 4)))) :=
    Primrec.pair (coeff_primrec 4) <| Primrec.pair
      (int_mul_primrec.comp (coeff_primrec 3) (coeff_primrec 5)) <| Primrec.pair
      (int_mul_primrec.comp (coeff_primrec 2)
        ((int_pow_const_primrec 2).comp (coeff_primrec 5))) <| Primrec.pair
      (int_mul_primrec.comp (coeff_primrec 1)
        ((int_pow_const_primrec 3).comp (coeff_primrec 5)))
      (int_mul_primrec.comp (coeff_primrec 0)
        ((int_pow_const_primrec 4).comp (coeff_primrec 5)))
  exact (monicQuinticEquiv_symm_primrec.comp ht).of_eq fun f => rfl

theorem monicQuintic_height_primrec : Primrec MonicQuintic.height := by
  apply Primrec.of_eq
    (Primrec.nat_max.comp (int_natAbs_primrec.comp monicQuintic_B_primrec) <|
    Primrec.nat_max.comp (int_natAbs_primrec.comp monicQuintic_C_primrec) <|
    Primrec.nat_max.comp (int_natAbs_primrec.comp monicQuintic_D_primrec) <|
    Primrec.nat_max.comp (int_natAbs_primrec.comp monicQuintic_E_primrec)
      (int_natAbs_primrec.comp monicQuintic_H_primrec))
  intro f
  rfl

theorem monicQuintic_rootBound_primrec : Primrec MonicQuintic.rootBound := by
  exact (Primrec.succ.comp monicQuintic_height_primrec).of_eq fun f => rfl

theorem monicQuintic_eval_primrec : Primrec₂ MonicQuintic.eval := by
  let hy (k : ℕ) : Primrec fun p : MonicQuintic × ℤ => p.2 ^ k :=
    (int_pow_const_primrec k).comp Primrec.snd
  have h := int_add_primrec.comp (hy 5) <| int_add_primrec.comp
    (int_mul_primrec.comp (monicQuintic_B_primrec.comp Primrec.fst) (hy 4)) <|
    int_add_primrec.comp
    (int_mul_primrec.comp (monicQuintic_C_primrec.comp Primrec.fst) (hy 3)) <|
    int_add_primrec.comp
    (int_mul_primrec.comp (monicQuintic_D_primrec.comp Primrec.fst) (hy 2)) <|
    int_add_primrec.comp
    (int_mul_primrec.comp (monicQuintic_E_primrec.comp Primrec.fst) (hy 1))
      (monicQuintic_H_primrec.comp Primrec.fst)
  exact h.to₂.of_eq fun f y => by simp [MonicQuintic.eval]; ring

theorem quadraticQ2_primrec : Primrec₂ MonicQuintic.quadraticQ2 := by
  exact (int_sub_primrec.comp₂
    (monicQuintic_B_primrec.comp₂ Primrec₂.left) Primrec₂.right).of_eq fun _ _ => rfl

theorem quadraticQ1_primrec : Primrec fun p : MonicQuintic × (ℤ × ℤ) =>
    p.1.quadraticQ1 p.2.1 p.2.2 := by
  have hq2 : Primrec fun p : MonicQuintic × (ℤ × ℤ) => p.1.quadraticQ2 p.2.1 :=
    quadraticQ2_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hmul := int_mul_primrec.comp (Primrec.fst.comp Primrec.snd) hq2
  exact (int_sub_primrec.comp
    (int_sub_primrec.comp (monicQuintic_C_primrec.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)) hmul).of_eq fun p => by
        simp [MonicQuintic.quadraticQ1]

theorem quadraticQ0_primrec : Primrec fun p : MonicQuintic × (ℤ × ℤ) =>
    p.1.quadraticQ0 p.2.1 p.2.2 := by
  have hq2 : Primrec fun p : MonicQuintic × (ℤ × ℤ) => p.1.quadraticQ2 p.2.1 :=
    quadraticQ2_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hq1 := quadraticQ1_primrec
  exact (int_sub_primrec.comp
    (int_sub_primrec.comp (monicQuintic_D_primrec.comp Primrec.fst)
      (int_mul_primrec.comp (Primrec.fst.comp Primrec.snd) hq1))
    (int_mul_primrec.comp (Primrec.snd.comp Primrec.snd) hq2)).of_eq fun p => by
      simp [MonicQuintic.quadraticQ0]

theorem linearRemainderZero_primrec : PrimrecRel MonicQuintic.linearRemainderZero := by
  apply (Primrec.eq.comp
    (monicQuintic_eval_primrec.comp Primrec.fst
      (int_neg_primrec.comp Primrec.snd))
    (Primrec.const (0 : ℤ))).of_eq
  intro p
  rfl

theorem quadraticRemainderZero_primrec :
    PrimrecPred fun p : MonicQuintic × (ℤ × ℤ) =>
      p.1.quadraticRemainderZero p.2.1 p.2.2 := by
  have hq1 := quadraticQ1_primrec
  have hq0 := quadraticQ0_primrec
  have hleft : PrimrecPred fun p : MonicQuintic × (ℤ × ℤ) =>
      p.1.E = p.2.1 * p.1.quadraticQ0 p.2.1 p.2.2 +
        p.2.2 * p.1.quadraticQ1 p.2.1 p.2.2 :=
    Primrec.eq.comp (monicQuintic_E_primrec.comp Primrec.fst)
      (int_add_primrec.comp
        (int_mul_primrec.comp (Primrec.fst.comp Primrec.snd) hq0)
        (int_mul_primrec.comp (Primrec.snd.comp Primrec.snd) hq1))
  have hright : PrimrecPred fun p : MonicQuintic × (ℤ × ℤ) =>
      p.1.H = p.2.2 * p.1.quadraticQ0 p.2.1 p.2.2 :=
    Primrec.eq.comp (monicQuintic_H_primrec.comp Primrec.fst)
      (int_mul_primrec.comp (Primrec.snd.comp Primrec.snd) hq0)
  exact (hleft.and hright).of_eq fun p => by
    rfl

theorem intEquivNat_lt_iff_mem_symmetricInterval (z : ℤ) (r : ℕ) :
    Equiv.intEquivNat z < 2 * r + 1 ↔ z ∈ symmetricInterval r := by
  rw [mem_symmetricInterval]
  cases z with
  | ofNat n =>
      change 2 * n < 2 * r + 1 ↔ -(r : ℤ) ≤ (n : ℤ) ∧ (n : ℤ) ≤ (r : ℤ)
      omega
  | negSucc n =>
      change 2 * n + 1 < 2 * r + 1 ↔
        -(r : ℤ) ≤ Int.negSucc n ∧ Int.negSucc n ≤ (r : ℤ)
      omega

theorem ofNat_int_mem_symmetricInterval_iff (n r : ℕ) :
    ofNat ℤ n ∈ symmetricInterval r ↔ n < 2 * r + 1 := by
  have hofNat : ofNat ℤ n = Equiv.intEquivNat.symm n := rfl
  simpa only [hofNat, Equiv.apply_symm_apply] using
    (intEquivNat_lt_iff_mem_symmetricInterval (Equiv.intEquivNat.symm n) r).symm

theorem primrecPred_exists_lt {α : Type*} [Primcodable α]
    {R : ℕ → α → Prop} [DecidableRel R] (hR : PrimrecRel R)
    {bound : α → ℕ} (hbound : Primrec bound) :
    PrimrecPred fun a => ∃ n < bound a, R n a := by
  exact (hR.exists_mem_list.comp (Primrec.list_range.comp hbound) Primrec.id).of_eq fun a => by
    simp

theorem primrecPred_exists₂_lt {α : Type*} [Primcodable α]
    {R : ℕ → ℕ → α → Prop} [∀ i j a, Decidable (R i j a)]
    {outerBound : α → ℕ} {innerBound : ℕ → α → ℕ}
    (hR : PrimrecPred fun q : ℕ × (ℕ × α) => R q.2.1 q.1 q.2.2)
    (hOuter : Primrec outerBound) (hInner : Primrec₂ innerBound) :
    PrimrecPred fun a => ∃ i < outerBound a,
      ∃ j < innerBound i a, R i j a := by
  have hRrel : PrimrecRel fun j : ℕ => fun p : ℕ × α => R p.1 j p.2 := hR
  have hInner' : Primrec fun p : ℕ × α => innerBound p.1 p.2 := hInner
  have hExistInner : PrimrecPred fun p : ℕ × α =>
      ∃ j < innerBound p.1 p.2, R p.1 j p.2 :=
    primrecPred_exists_lt hRrel hInner'
  have hOuterRel : PrimrecRel fun i : ℕ => fun a : α =>
      ∃ j < innerBound i a, R i j a := hExistInner
  exact primrecPred_exists_lt hOuterRel hOuter

def symmetricCodeBound (r : ℕ) : ℕ := 2 * r + 1

theorem symmetricCodeBound_primrec : Primrec symmetricCodeBound := by
  exact (Primrec.succ.comp
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)).of_eq fun _ => rfl

theorem exists_code_linear_iff (f : MonicQuintic) :
    (∃ n < symmetricCodeBound f.rootBound,
      f.linearRemainderZero (ofNat ℤ n)) ↔
      ∃ c ∈ symmetricInterval f.rootBound, f.linearRemainderZero c := by
  constructor
  · rintro ⟨n, hn, hz⟩
    exact ⟨ofNat ℤ n, (ofNat_int_mem_symmetricInterval_iff n f.rootBound).mpr hn, hz⟩
  · rintro ⟨c, hc, hz⟩
    refine ⟨Equiv.intEquivNat c, ?_, ?_⟩
    · exact (intEquivNat_lt_iff_mem_symmetricInterval c f.rootBound).mpr hc
    · have hdecode : ofNat ℤ (Equiv.intEquivNat c) = c := by
        change Equiv.intEquivNat.symm (Equiv.intEquivNat c) = c
        exact Equiv.symm_apply_apply _ _
      simpa only [hdecode] using hz

theorem hasBoundedLinearFactor_primrec : Primrec MonicQuintic.hasBoundedLinearFactor := by
  have hdecode : Primrec fun n : ℕ => ofNat ℤ n := Primrec.ofNat ℤ
  have hrel : PrimrecRel fun n : ℕ => fun f : MonicQuintic =>
      f.linearRemainderZero (ofNat ℤ n) := by
    exact linearRemainderZero_primrec.comp Primrec.snd (hdecode.comp Primrec.fst)
  have hbound : Primrec fun f : MonicQuintic => symmetricCodeBound f.rootBound :=
    symmetricCodeBound_primrec.comp monicQuintic_rootBound_primrec
  have hp : PrimrecPred fun f : MonicQuintic =>
      ∃ n < symmetricCodeBound f.rootBound,
        f.linearRemainderZero (ofNat ℤ n) :=
    primrecPred_exists_lt hrel hbound
  exact hp.decide.of_eq fun f => by
    rw [show f.hasBoundedLinearFactor = decide
      (∃ c ∈ symmetricInterval f.rootBound, f.linearRemainderZero c) by rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact exists_code_linear_iff f

theorem exists_code_quadratic_iff (f : MonicQuintic) :
    (∃ nb < symmetricCodeBound (2 * f.rootBound),
      ∃ nc < symmetricCodeBound (f.rootBound ^ 2),
        f.quadraticRemainderZero (ofNat ℤ nb) (ofNat ℤ nc)) ↔
      ∃ b ∈ symmetricInterval (2 * f.rootBound),
        ∃ c ∈ symmetricInterval (f.rootBound ^ 2),
          f.quadraticRemainderZero b c := by
  constructor
  · rintro ⟨nb, hnb, nc, hnc, hz⟩
    exact ⟨ofNat ℤ nb,
      (ofNat_int_mem_symmetricInterval_iff nb (2 * f.rootBound)).mpr hnb,
      ofNat ℤ nc,
      (ofNat_int_mem_symmetricInterval_iff nc (f.rootBound ^ 2)).mpr hnc, hz⟩
  · rintro ⟨b, hb, c, hc, hz⟩
    refine ⟨Equiv.intEquivNat b, ?_, Equiv.intEquivNat c, ?_, ?_⟩
    · exact (intEquivNat_lt_iff_mem_symmetricInterval b (2 * f.rootBound)).mpr hb
    · exact (intEquivNat_lt_iff_mem_symmetricInterval c (f.rootBound ^ 2)).mpr hc
    · have hbdecode : ofNat ℤ (Equiv.intEquivNat b) = b := by
        change Equiv.intEquivNat.symm (Equiv.intEquivNat b) = b
        exact Equiv.symm_apply_apply _ _
      have hcdecode : ofNat ℤ (Equiv.intEquivNat c) = c := by
        change Equiv.intEquivNat.symm (Equiv.intEquivNat c) = c
        exact Equiv.symm_apply_apply _ _
      simpa only [hbdecode, hcdecode] using hz

theorem hasBoundedQuadraticFactor_primrec :
    Primrec MonicQuintic.hasBoundedQuadraticFactor := by
  have hdecode : Primrec fun n : ℕ => ofNat ℤ n := Primrec.ofNat ℤ
  have hmap : Primrec fun q : ℕ × (ℕ × MonicQuintic) =>
      (q.2.2, (ofNat ℤ q.2.1, ofNat ℤ q.1)) :=
    Primrec.pair (Primrec.snd.comp Primrec.snd) <| Primrec.pair
      (hdecode.comp (Primrec.fst.comp Primrec.snd)) (hdecode.comp Primrec.fst)
  have htest : PrimrecPred fun q : ℕ × (ℕ × MonicQuintic) =>
      q.2.2.quadraticRemainderZero (ofNat ℤ q.2.1) (ofNat ℤ q.1) :=
    quadraticRemainderZero_primrec.comp hmap
  have hbRadius : Primrec fun f : MonicQuintic => 2 * f.rootBound :=
    Primrec.nat_mul.comp (Primrec.const 2) monicQuintic_rootBound_primrec
  have hbBound : Primrec fun f : MonicQuintic =>
      symmetricCodeBound (2 * f.rootBound) :=
    symmetricCodeBound_primrec.comp hbRadius
  have hcRadiusMul : Primrec fun f : MonicQuintic => f.rootBound * f.rootBound :=
    Primrec.nat_mul.comp monicQuintic_rootBound_primrec monicQuintic_rootBound_primrec
  have hcRadius : Primrec fun f : MonicQuintic => f.rootBound ^ 2 :=
    hcRadiusMul.of_eq fun f => by simp [pow_two]
  have hcBound : Primrec₂ fun _nb : ℕ => fun f : MonicQuintic =>
      symmetricCodeBound (f.rootBound ^ 2) :=
    (symmetricCodeBound_primrec.comp hcRadius).comp₂ Primrec₂.right
  have hp : PrimrecPred fun f : MonicQuintic =>
      ∃ nb < symmetricCodeBound (2 * f.rootBound),
        ∃ nc < symmetricCodeBound (f.rootBound ^ 2),
          f.quadraticRemainderZero (ofNat ℤ nb) (ofNat ℤ nc) :=
    primrecPred_exists₂_lt htest hbBound hcBound
  exact hp.decide.of_eq fun f => by
    rw [show f.hasBoundedQuadraticFactor = decide
      (∃ b ∈ symmetricInterval (2 * f.rootBound),
        ∃ c ∈ symmetricInterval (f.rootBound ^ 2),
          f.quadraticRemainderZero b c) by rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact exists_code_quadratic_iff f

theorem hasBoundedProperFactor_primrec : Primrec MonicQuintic.hasBoundedProperFactor := by
  exact (Primrec.or.comp hasBoundedLinearFactor_primrec
    hasBoundedQuadraticFactor_primrec).of_eq fun _ => rfl

theorem fin_sum_int_primrec {α : Type*} [Primcodable α] {n : ℕ}
    {f : α → Fin n → ℤ} (hf : ∀ i, Primrec fun a => f a i) :
    Primrec fun a => ∑ i, f a i := by
  induction n with
  | zero => simpa using (Primrec.const (α := α) (0 : ℤ))
  | succ n ih =>
      have htail : Primrec fun a => ∑ i : Fin n, f a i.succ :=
        ih (fun i => hf i.succ)
      exact (int_add_primrec.comp (hf 0) htail).of_eq fun a => by
        rw [Fin.sum_univ_succ]

namespace IntegerSextic

open LeanProofs.PolynomialFormulas.QuinticRadicalDecidability.IntegerSextic

theorem coeff_primrec (i : Fin 7) : Primrec fun A : IntegerSextic => A i :=
  Primrec.fin_app.comp Primrec.id (Primrec.const i)

theorem homogeneousEval_primrec :
    Primrec fun p : IntegerSextic × (ℤ × ℤ) =>
      p.1.homogeneousEval p.2.1 p.2.2 := by
  have hsum : Primrec fun p : IntegerSextic × (ℤ × ℤ) =>
      ∑ i : Fin 7, p.1 i * p.2.1 ^ (i : ℕ) * p.2.2 ^ (6 - (i : ℕ)) :=
    fin_sum_int_primrec (n := 7) fun i =>
      int_mul_primrec.comp
        (int_mul_primrec.comp ((coeff_primrec i).comp Primrec.fst)
          ((int_pow_const_primrec (i : ℕ)).comp (Primrec.fst.comp Primrec.snd)))
        ((int_pow_const_primrec (6 - (i : ℕ))).comp (Primrec.snd.comp Primrec.snd))
  exact hsum.of_eq fun p => rfl

theorem denominator_code_mem_iff (A : IntegerSextic) (n : ℕ) :
    Int.ofNat (n + 1) ∈ A.denominatorCandidates ↔ n < (A 6).natAbs := by
  rw [mem_denominatorCandidates]
  simp only [Int.ofNat_eq_natCast]
  norm_cast
  omega

def HasCodedRationalRoot (A : IntegerSextic) : Prop :=
  A 0 = 0 ∨
    ∃ nu < symmetricCodeBound (A 0).natAbs,
      ∃ nv < (A 6).natAbs,
        A.homogeneousEval (ofNat ℤ nu) (Int.ofNat (nv + 1)) = 0

instance (A : IntegerSextic) : Decidable (HasCodedRationalRoot A) :=
  inferInstanceAs (Decidable
    (A 0 = 0 ∨
      ∃ nu < symmetricCodeBound (A 0).natAbs,
        ∃ nv < (A 6).natAbs,
          A.homogeneousEval (ofNat ℤ nu) (Int.ofNat (nv + 1)) = 0))

theorem hasCodedRationalRoot_iff (A : IntegerSextic) :
    HasCodedRationalRoot A ↔ A.HasBoundedRationalRoot := by
  constructor
  · rintro (hzero | ⟨nu, hnu, nv, hnv, heval⟩)
    · exact Or.inl hzero
    · exact Or.inr ⟨ofNat ℤ nu,
        (ofNat_int_mem_symmetricInterval_iff nu (A 0).natAbs).mpr hnu,
        Int.ofNat (nv + 1), (denominator_code_mem_iff A nv).mpr hnv, heval⟩
  · rintro (hzero | ⟨u, hu, v, hv, heval⟩)
    · exact Or.inl hzero
    · right
      have hupos : Equiv.intEquivNat u < symmetricCodeBound (A 0).natAbs :=
        (intEquivNat_lt_iff_mem_symmetricInterval u (A 0).natAbs).mpr hu
      have hvBounds := mem_denominatorCandidates.mp hv
      have hvnonneg : 0 ≤ v := le_trans (by norm_num) hvBounds.1
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hvnonneg
      have hmpos : 1 ≤ m := by exact_mod_cast hvBounds.1
      refine ⟨Equiv.intEquivNat u, hupos, m - 1, ?_, ?_⟩
      · have hmle : m ≤ (A 6).natAbs := by exact_mod_cast hvBounds.2
        omega
      · have hmsucc : m - 1 + 1 = m := by omega
        have hudecode : ofNat ℤ (Equiv.intEquivNat u) = u := by
          change Equiv.intEquivNat.symm (Equiv.intEquivNat u) = u
          exact Equiv.symm_apply_apply _ _
        simpa only [hudecode, hmsucc, Int.ofNat_eq_natCast] using heval

theorem hasCodedRationalRoot_primrec : PrimrecPred HasCodedRationalRoot := by
  have hdecode : Primrec fun n : ℕ => ofNat ℤ n := Primrec.ofNat ℤ
  have hpositive : Primrec fun n : ℕ => Int.ofNat (n + 1) :=
    int_ofNat_primrec.comp Primrec.succ
  have hmap : Primrec fun q : ℕ × (ℕ × IntegerSextic) =>
      (q.2.2, (ofNat ℤ q.2.1, Int.ofNat (q.1 + 1))) :=
    Primrec.pair (Primrec.snd.comp Primrec.snd) <| Primrec.pair
      (hdecode.comp (Primrec.fst.comp Primrec.snd)) (hpositive.comp Primrec.fst)
  have htest : PrimrecPred fun q : ℕ × (ℕ × IntegerSextic) =>
      q.2.2.homogeneousEval (ofNat ℤ q.2.1) (Int.ofNat (q.1 + 1)) = 0 :=
    Primrec.eq.comp (homogeneousEval_primrec.comp hmap) (Primrec.const (0 : ℤ))
  have hnumRadius : Primrec fun A : IntegerSextic => (A 0).natAbs :=
    int_natAbs_primrec.comp (coeff_primrec 0)
  have hnumBound : Primrec fun A : IntegerSextic =>
      symmetricCodeBound (A 0).natAbs :=
    symmetricCodeBound_primrec.comp hnumRadius
  have hdenBound : Primrec₂ fun _nu : ℕ => fun A : IntegerSextic => (A 6).natAbs :=
    (int_natAbs_primrec.comp (coeff_primrec 6)).comp₂ Primrec₂.right
  have hexists : PrimrecPred fun A : IntegerSextic =>
      ∃ nu < symmetricCodeBound (A 0).natAbs,
        ∃ nv < (A 6).natAbs,
          A.homogeneousEval (ofNat ℤ nu) (Int.ofNat (nv + 1)) = 0 :=
    primrecPred_exists₂_lt htest hnumBound hdenBound
  have hzero : PrimrecPred fun A : IntegerSextic => A 0 = 0 :=
    Primrec.eq.comp (coeff_primrec 0) (Primrec.const (0 : ℤ))
  exact (hzero.or hexists).of_eq fun A => by rfl

theorem hasBoundedRationalRoot_primrec :
    PrimrecPred LeanProofs.PolynomialFormulas.QuinticRadicalDecidability.IntegerSextic.HasBoundedRationalRoot :=
  hasCodedRationalRoot_primrec.of_eq hasCodedRationalRoot_iff

theorem rationalRootSearch_primrec :
    Primrec LeanProofs.PolynomialFormulas.QuinticRadicalDecidability.IntegerSextic.rationalRootSearch := by
  exact hasCodedRationalRoot_primrec.decide.of_eq fun A => by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, rationalRootSearch_iff]
    exact hasCodedRationalRoot_iff A

end IntegerSextic

end LeanProofs.PolynomialFormulas.QuinticRadicalPrimrec
