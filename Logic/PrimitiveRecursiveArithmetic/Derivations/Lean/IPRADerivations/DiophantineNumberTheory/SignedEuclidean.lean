import IPRADerivations.Core.IntCancel
import IPRADerivations.AnalyticNumberTheory.Totatives
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.SubstCommand

/-!
# Actual Euclidean division of signed integer pairs

Minkowski packet, `paper/02_finite_proof.tex`, signed quotient/remainder
and equation `eq:z`.  The input is an arbitrary natural pair `p,n`, denoting
the integer `p-n`, and an internal positive modulus `m`. Canonical signs or
normal forms are unnecessary.

Divide `p` and `n` by `m` using the checked natural division programs.
The actual borrow bit is `sg((n mod m) ∸ (p mod m))`. The signed quotient is
`(p div m) - ((n div m)+borrow)` and the natural residue is
`((p mod m)+borrow*m) ∸ (n mod m)`. All operations are fixed PR terms.
The signed reconstruction and residue bound are proved from natural division
and the two borrow branches, rather than assumed as a signed division law.

Equality statements below concern the decoded integers. In particular they
do not identify two potentially different natural-pair representations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.SignedEuclidean

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def borrow (p r : PTm n) : PTm n := sg (monus r p)
def residue (p r m : PTm n) : PTm n := monus (p + borrow p r * m) r

ipra_subst borrow [sg]
ipra_subst residue

/-- Both branches are checked, including equal remainders and zero residues. -/
theorem residue_data (p r m : PTm n) (hp : Γ ⊢[PRAAx] lt p m) (hr : Γ ⊢[PRAAx] lt r m) :
    Γ ⊢[PRAAx] le r (p + borrow p r * m) ⋏ lt (residue p r m) m := by
  refine .orE (lt_or_le p r) ?_ ?_
  · let Δ := lt p r :: Γ
    have bit : Δ ⊢[PRAAx] borrow p r ≐ one := sg_lt Prf.hyp0
    have sum : Δ ⊢[PRAAx] p + borrow p r * m ≐ p + m :=
      (congrAdd (.eqRefl _) (congrMul bit (.eqRefl _))).eqTrans (congrAdd (.eqRefl _) (one_mul _))
    have fits : Δ ⊢[PRAAx] le r (p + borrow p r * m) :=
      le_congr (.eqRefl _) sum.eqSymm (le_trans (le_of_lt hr.wk) (le_add_left _ _))
    have reconstruct := eq_add_of_le fits
    have upper : Δ ⊢[PRAAx] le (succ (residue p r m)) m := by
      have shifted := add_le_add_right (residue p r m) (Prf.hyp0 : Δ ⊢[PRAAx] lt p r)
      have reconstructed : Δ ⊢[PRAAx] r + residue p r m ≐ p + m := reconstruct.eqSymm.eqTrans sum
      exact le_of_add_le_add_right (le_congr (by ipra_ring)
        (reconstructed.eqTrans (add_comm _ _)) shifted)
    exact .andI fits upper
  · let Δ := le r p :: Γ
    have bit : Δ ⊢[PRAAx] borrow p r ≐ zero := sg_le Prf.hyp0
    have sum : Δ ⊢[PRAAx] p + borrow p r * m ≐ p :=
      (congrAdd (.eqRefl _) (congrMul bit (.eqRefl _))).eqTrans
        ((congrAdd (.eqRefl _) (zero_mul _)).eqTrans (add_zero _))
    have fits : Δ ⊢[PRAAx] le r (p + borrow p r * m) := le_congr (.eqRefl _) sum.eqSymm Prf.hyp0
    have small : Δ ⊢[PRAAx] le (residue p r m) p :=
      le_of_eq_add (d := r) ((sum.eqSymm.eqTrans (eq_add_of_le fits)).eqTrans (add_comm _ _))
    exact .andI fits (lt_of_le_of_lt small hp.wk)

def quotient (a : ZT n) (m : PTm n) : ZT n :=
  ⟨quo a.pos m, quo a.neg m + borrow (rem a.pos m) (rem a.neg m)⟩

def remainder (a : ZT n) (m : PTm n) : PTm n := residue (rem a.pos m) (rem a.neg m) m

ipra_subst quotient [ZT.subst]
ipra_subst remainder [ZT.subst]

theorem positive_form (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] m ≐ succ (pred m) := by
  refine .orE (zero_or_succ m) ?_ Prf.hyp0
  exact lt_zero_absurd _ (lt_congr (.eqRefl zero) Prf.hyp0 hm.wk)

/-- An internal positive modulus instantiates the existing proved natural law. -/
theorem natural_divmod (p m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] (p ≐ m * quo p m + rem p m) ⋏ lt (rem p m) m := by
  have positive := positive_form m hm
  have h := div_mod (Γ := Γ) p (pred m)
  exact .andI ((Prf.andE₁ h).eqTrans
    (congrAdd (congrMul positive.eqSymm (congrAp2 quoF (.eqRefl _) positive.eqSymm))
      (congrAp2 remF (.eqRefl _) positive.eqSymm)))
    (lt_congr (congrAp2 remF (.eqRefl _) positive.eqSymm) positive.eqSymm (Prf.andE₂ h))

/-- Actual signed Euclidean division: `a=m*q+r` and `0≤r<m`. -/
theorem euclidean (a : ZT n) (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] ZT.eq a (ZT.ofNat m * quotient a m + ZT.ofNat (remainder a m)) ⋏ lt (remainder a m) m := by
  have positive := natural_divmod a.pos m hm
  have negative := natural_divmod a.neg m hm
  have fits := residue_data (rem a.pos m) (rem a.neg m) m (.andE₂ positive) (.andE₂ negative)
  refine .andI ?_ (.andE₂ fits)
  apply ZT.derive
  have ep := natEq (.andE₁ positive)
  have en := natEq (.andE₁ negative)
  have er := natEq (eq_add_of_le (.andE₁ fits))
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat]
  simp only [quotient, ZT.toZ]
  simp only [remainder, residue]
  ipra_simps
  linear_combination ep - en + er

/-- Equal computed residues give exact division of the signed difference. -/
theorem same_remainder_difference (a b : ZT n) (m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hr : Γ ⊢[PRAAx] remainder a m ≐ remainder b m) :
    Γ ⊢[PRAAx] ZT.eq (a - b) (ZT.ofNat m * (quotient a m - quotient b m)) := by
  ipra_lc ZT.toZ_eq (.andE₁ (euclidean a m hm)) - ZT.toZ_eq (.andE₁ (euclidean b m hm)) + natEq hr

/-- Under an equal-residue collision, zero quotient difference identifies
decoded integers, without identifying their possibly different pair codes. -/
theorem equal_of_quotient_difference_zero (a b : ZT n) (m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hr : Γ ⊢[PRAAx] remainder a m ≐ remainder b m)
    (hq : Γ ⊢[PRAAx] ZT.eq (quotient a m - quotient b m) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq a b := by
  ipra_lc ZT.toZ_eq (same_remainder_difference a b m hm hr) + (Groth.ι (Q.mk Γ m)) * ZT.toZ_eq hq

theorem quotient_difference_nonzero (a b : ZT n) (m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hr : Γ ⊢[PRAAx] remainder a m ≐ remainder b m) (hne : Γ ⊢[PRAAx] neg (ZT.eq a b)) :
    Γ ⊢[PRAAx] neg (ZT.eq (quotient a m - quotient b m) (ZT.natLit 0)) :=
  .impI (.impE hne.wk (equal_of_quotient_difference_zero a b m hm.wk hr.wk Prf.hyp0))

theorem remainder_range (a : ZT n) (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] lt (remainder a m) m := .andE₂ (euclidean a m hm)

/-- Modulus one is included without a separate nontrivial-modulus assumption. -/
theorem remainder_one (a : ZT n) : Γ ⊢[PRAAx] remainder a one ≐ zero := by
  have h := remainder_range (Γ := Γ) a one (le_refl one)
  exact (monus_zero _).eqSymm.eqTrans ((succ_monus_succ _ _).eqSymm.eqTrans h)

theorem quotient_one (a : ZT n) : Γ ⊢[PRAAx] ZT.eq (quotient a one) a := by
  apply ZT.derive
  have e := ZT.toZ_eq (.andE₁ (euclidean (Γ := Γ) a one (le_refl one)))
  have r := natEq (remainder_one (Γ := Γ) a)
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat] at e
  simp only [Q.mk_one, map_one] at e
  simp only [Q.mk_zero, map_zero] at r
  rw [r] at e
  simpa using e.symm

/-! ## One actual PR program on an arbitrary signed pair code -/

def decode (code : PTm n) : ZT n := ⟨fstT code, sndT code⟩
def pack (a : ZT n) : PTm n := pairT a.pos a.neg
def result (a : ZT n) (m : PTm n) : PTm n := pairT (pack (quotient a m)) (remainder a m)

ipra_subst decode [ZT.subst]
ipra_subst pack [ZT.subst]
ipra_subst result

/-- The first argument is an arbitrary pair-coded integer; the second is
the modulus. The output is the pair `(signedQuotientCode,naturalResidue)`. -/
def divmodF : PR 2 := PTm.toPR (result (decode (var 0)) (var 1))

def computedQuotient (code m : PTm n) : ZT n := decode (fstT (ap2 divmodF code m))
def computedRemainder (code m : PTm n) : PTm n := sndT (ap2 divmodF code m)

ipra_subst computedQuotient
ipra_subst computedRemainder

theorem program_at (code m : PTm n) :
    Γ ⊢[PRAAx] ap2 divmodF code m ≐ result (decode code) m := by
  have h := toPR_eq (Γ := Γ) (result (decode (var 0)) (var 1)) ![code, m]
  simpa [divmodF, ap2] using h

theorem computed_quotient (code m : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (computedQuotient code m) (quotient (decode code) m) := by
  have e : Γ ⊢[PRAAx] fstT (ap2 divmodF code m) ≐ pack (quotient (decode code) m) :=
    (congrFst (program_at code m)).eqTrans (fst_pair _ _)
  apply ZT.derive
  change Groth.ι (Q.mk Γ (fstT (fstT (ap2 divmodF code m)))) -
    Groth.ι (Q.mk Γ (sndT (fstT (ap2 divmodF code m)))) = _
  rw [natEq ((congrFst e).eqTrans (fst_pair _ _)),
    natEq ((congrSnd e).eqTrans (snd_pair _ _))]
  rfl

theorem computed_remainder (code m : PTm n) :
    Γ ⊢[PRAAx] computedRemainder code m ≐ remainder (decode code) m :=
  (congrSnd (program_at code m)).eqTrans (snd_pair _ _)

/-- Correctness mentions the decoded output of the actual PR symbol. -/
theorem program_correct (code m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] ZT.eq (decode code)
      (ZT.ofNat m * computedQuotient code m + ZT.ofNat (computedRemainder code m)) ⋏
      lt (computedRemainder code m) m := by
  have actual := euclidean (decode code) m hm
  refine .andI ?_ (lt_congr (computed_remainder code m).eqSymm (.eqRefl _) (.andE₂ actual))
  apply ZT.derive
  have e := ZT.toZ_eq (.andE₁ actual)
  have q := ZT.toZ_eq (computed_quotient (Γ := Γ) code m)
  have r := natEq (computed_remainder (Γ := Γ) code m)
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat] at e ⊢
  rw [q, r]
  exact e

/-- The collision identity on the decoded output of the actual PR program. -/
theorem computed_collision (a b m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hr : Γ ⊢[PRAAx] computedRemainder a m ≐ computedRemainder b m) :
    Γ ⊢[PRAAx] ZT.eq (decode a - decode b)
      (ZT.ofNat m * (computedQuotient a m - computedQuotient b m)) := by
  ipra_lc ZT.toZ_eq (.andE₁ (program_correct a m hm)) - ZT.toZ_eq (.andE₁ (program_correct b m hm)) + natEq hr

theorem computed_zero_difference (a b m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hr : Γ ⊢[PRAAx] computedRemainder a m ≐ computedRemainder b m)
    (hq : Γ ⊢[PRAAx] ZT.eq (computedQuotient a m - computedQuotient b m) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (decode a) (decode b) := by
  ipra_lc ZT.toZ_eq (computed_collision a b m hm hr) + (Groth.ι (Q.mk Γ m)) * ZT.toZ_eq hq

theorem computed_nonzero_difference (a b m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hr : Γ ⊢[PRAAx] computedRemainder a m ≐ computedRemainder b m)
    (hne : Γ ⊢[PRAAx] neg (ZT.eq (decode a) (decode b))) :
    Γ ⊢[PRAAx] neg (ZT.eq (computedQuotient a m - computedQuotient b m) (ZT.natLit 0)) :=
  .impI (.impE hne.wk (computed_zero_difference a b m hm.wk hr.wk Prf.hyp0))

def euclideanFormula : Fm PTm 3 :=
  le one (var 2) ⟶
    (ZT.eq (⟨var 0, var 1⟩ : ZT 3)
      (ZT.ofNat (var 2) * quotient ⟨var 0, var 1⟩ (var 2) + ZT.ofNat (remainder ⟨var 0, var 1⟩ (var 2))) ⋏
      lt (remainder ⟨var 0, var 1⟩ (var 2)) (var 2))

theorem euclidean_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 euclideanFormula :=
  closeUniv 3 (.impI (euclidean ⟨var 0, var 1⟩ (var 2) Prf.hyp0))

def collisionFormula : Fm PTm 5 :=
  le one (var 4) ⟶ (remainder ⟨var 0, var 1⟩ (var 4) ≐ remainder ⟨var 2, var 3⟩ (var 4)) ⟶
    ZT.eq ((⟨var 0, var 1⟩ : ZT 5) - ⟨var 2, var 3⟩)
      (ZT.ofNat (var 4) * (quotient ⟨var 0, var 1⟩ (var 4) - quotient ⟨var 2, var 3⟩ (var 4)))

theorem same_remainder_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 collisionFormula :=
  closeUniv 5 (.impI (.impI (same_remainder_difference ⟨var 0, var 1⟩ ⟨var 2, var 3⟩ (var 4) Prf.hyp1 Prf.hyp0)))

theorem zero_difference_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 4) ⟶ (remainder ⟨var 0, var 1⟩ (var 4) ≐ remainder ⟨var 2, var 3⟩ (var 4)) ⟶
        ZT.eq (quotient ⟨var 0, var 1⟩ (var 4) - quotient ⟨var 2, var 3⟩ (var 4)) (ZT.natLit 0) ⟶
          ZT.eq (⟨var 0, var 1⟩ : ZT 5) ⟨var 2, var 3⟩) :=
  closeUniv 5 (.impI (.impI (.impI (equal_of_quotient_difference_zero
    ⟨var 0, var 1⟩ ⟨var 2, var 3⟩ (var 4) Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem modulus_one_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((remainder ⟨var 0, var 1⟩ one ≐ zero) ⋏ ZT.eq (quotient ⟨var 0, var 1⟩ one) (⟨var 0, var 1⟩ : ZT 2)) :=
  closeUniv 2 (.andI (remainder_one _) (quotient_one _))

theorem program_metadata_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((ap2 divmodF (var 0) (var 1) ≐ result (decode (var 0)) (var 1)) ⋏
        (ZT.eq (computedQuotient (var 0) (var 1)) (quotient (decode (var 0)) (var 1)) ⋏
          (computedRemainder (var 0) (var 1) ≐ remainder (decode (var 0)) (var 1)))) :=
  closeUniv 2 (.andI (program_at _ _) (.andI (computed_quotient _ _) (computed_remainder _ _)))

theorem program_correct_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (le one (var 1) ⟶
        (ZT.eq (decode (var 0))
          (ZT.ofNat (var 1) * computedQuotient (var 0) (var 1) + ZT.ofNat (computedRemainder (var 0) (var 1))) ⋏
          lt (computedRemainder (var 0) (var 1)) (var 1))) :=
  closeUniv 2 (.impI (program_correct (var 0) (var 1) Prf.hyp0))

/-- Three internal arguments: the two arbitrary signed pair codes and the
positive modulus. The final implications preserve geometric nonzeroness. -/
theorem program_collision_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le one (var 2) ⟶
        (computedRemainder (var 0) (var 2) ≐ computedRemainder (var 1) (var 2)) ⟶
        (ZT.eq (decode (var 0) - decode (var 1))
          (ZT.ofNat (var 2) * (computedQuotient (var 0) (var 2) - computedQuotient (var 1) (var 2))) ⋏
        ((ZT.eq (computedQuotient (var 0) (var 2) - computedQuotient (var 1) (var 2)) (ZT.natLit 0) ⟶
            ZT.eq (decode (var 0)) (decode (var 1))) ⋏
          (neg (ZT.eq (decode (var 0)) (decode (var 1))) ⟶
            neg (ZT.eq (computedQuotient (var 0) (var 2) - computedQuotient (var 1) (var 2)) (ZT.natLit 0)))))) :=
  closeUniv 3 (.impI (.impI (.andI (computed_collision _ _ _ Prf.hyp1 Prf.hyp0)
    (.andI (.impI (computed_zero_difference _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))
      (.impI (computed_nonzero_difference _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

theorem program_modulus_one_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      ((computedRemainder (var 0) one ≐ zero) ⋏
        ZT.eq (computedQuotient (var 0) one) (decode (var 0))) := by
  apply closeUniv 1
  refine .andI ((computed_remainder _ _).eqTrans (remainder_one _)) ?_
  apply ZT.derive
  exact (ZT.toZ_eq (computed_quotient (Γ := []) (var 0 : PTm 1) one)).trans
    (ZT.toZ_eq (quotient_one (Γ := []) (decode (var 0 : PTm 1))))

end LeanProofs.IPRA.DiophantineNumberTheory.SignedEuclidean
