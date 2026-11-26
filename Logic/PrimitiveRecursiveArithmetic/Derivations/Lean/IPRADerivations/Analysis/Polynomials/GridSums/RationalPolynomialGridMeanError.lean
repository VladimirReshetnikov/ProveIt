import IPRADerivations.Analysis.Polynomials.GridSums.RationalPolynomialGridSum

/-!
# A finite error for the actual polynomial grid mean

The power-sum bounds have one-sided errors. Combining their signed
coefficient multiples controls the two cleared errors of the
polynomial mean. The allowance is the sum of absolute coefficients
times the single power-sum allowance.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.RationalPolynomialGridMeanError

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open BernoulliBounds (qsplit zint toZ_zint natAbs_cast_of_nonneg natAbs_cast_of_neg)
open RationalPowerMoments (naturalSum)
open RationalPolynomialGridSum (prefixNumerator rowDen)
open Syn
open scoped Fm

variable {n d : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" x:max => Groth.ι (Q.mk Γ x)

def weight {d : ℕ} (i : Fin (d+1)) : ℕ := (d+1).factorial/(i.val+1)

theorem weight_mul (i : Fin (d+1)) : weight i*(i.val+1) = (d+1).factorial :=
  Nat.div_mul_cancel (Nat.dvd_factorial (by omega) i.isLt)

def meanNumerator (a : Fin (d+1) → ℤ) : ℤ := ∑ i, a i * (weight i : ℤ)
def radius (a : Fin (d+1) → ℤ) : ℕ := ∑ i, (a i).natAbs

private def slack (i : Fin (d+1)) (M : PTm n) : Groth (Q Γ) :=
  (weight i : Groth (Q Γ))*𝔞(pw M (num (d+1))) -
    ((d+1).factorial : Groth (Q Γ))*𝔞(naturalSum (num i) M)*𝔞(pw M (num (d-i)))

private theorem monomial_slacks (i : Fin (d+1)) (M : PTm n) :
    Nonneg Γ (slack (Γ := Γ) i M) ∧
      Nonneg Γ (((d+1).factorial : Groth (Q Γ))*𝔞(pw M (num d)) - slack (Γ := Γ) i M) := by
  let e := weight i
  let R := pw M (num (d-i.val))
  have pol := PowerSums.moment (Γ := Γ) (num i.val) M
  have lo := sl_def pol.andE₁
  have hi := sl_def pol.andE₂
  have w : (e : Groth (Q Γ))*((i.val+1 : ℕ) : Groth (Q Γ)) = ((d+1).factorial : Groth (Q Γ)) := by
    rw [← Nat.cast_mul]
    exact congrArg (fun k : ℕ => (k : Groth (Q Γ))) (weight_mul i)
  have hd : d+1-(i.val+1) = d-i.val := by omega
  have top := natEq (qsplit (Γ := Γ) (d+1) (i.val+1) (by omega) M)
  rw [hd] at top
  have base := natEq (qsplit (Γ := Γ) d i.val (by omega) M)
  have exp : Γ ⊢[PRAAx] succ (num i.val) ≐ (num (i.val+1) : PTm n) := by
    apply deriveNat
    simp [Q.mk_num, Q.mk_succ, Nat.cast_succ]
  have ps : 𝔞(pw M (succ (num i.val))) = 𝔞(pw M (num (i.val+1))) :=
    natEq (congrAp2 powF exp (.eqRefl M))
  simp only [Q.mk_mul,Q.mk_add,Q.mk_succ,Q.mk_num,map_add,map_mul,map_one,map_natCast] at lo hi top base
  simp only [ps] at lo hi
  have reduce : slack (Γ := Γ) i M = (e : Groth (Q Γ))*𝔞(R)*sl pol.andE₁ := by
    rw [lo]
    simp only [slack,top,R,← w,e,Nat.cast_add,Nat.cast_one,naturalSum]
    ring
  constructor
  · exact reduce ▸ nn_mul (nn_mul (nn_natCast _) (nn_term _)) (nn_sl _)
  · have err : ((d+1).factorial : Groth (Q Γ))*𝔞(pw M (num d)) - slack (Γ := Γ) i M =
        (e : Groth (Q Γ))*𝔞(R)*sl pol.andE₂ := by
      rw [hi,reduce,lo]
      simp only [base,R,← w,e,Nat.cast_add,Nat.cast_one]
      ring
    exact err ▸ nn_mul (nn_mul (nn_natCast _) (nn_term _)) (nn_sl _)

private theorem signed_slacks (a : ℤ) (e C : Groth (Q Γ)) (he : Nonneg Γ e)
    (hC : Nonneg Γ C) (hd : Nonneg Γ (C-e)) :
    Nonneg Γ ((a.natAbs : Groth (Q Γ))*C + (a : Groth (Q Γ))*e) ∧
      Nonneg Γ ((a.natAbs : Groth (Q Γ))*C - (a : Groth (Q Γ))*e) := by
  have plus := nn_mul (nn_natCast a.natAbs) (nn_add hC he)
  have minus := nn_mul (nn_natCast a.natAbs) hd
  by_cases ha : 0 ≤ a
  · constructor
    · convert plus using 1
      rw [natAbs_cast_of_nonneg ha]
      ring
    · convert minus using 1
      rw [natAbs_cast_of_nonneg ha]
      ring
  · have ha' : a < 0 := lt_of_not_ge ha
    constructor
    · convert minus using 1
      rw [natAbs_cast_of_neg ha']
      ring
    · convert plus using 1
      rw [natAbs_cast_of_neg ha']
      ring

theorem cleared_error (a : Fin (d+1) → ℤ) (M : PTm n) :
    let I := zint (meanNumerator a)*ZT.ofNat (pw M (num (d+1)))
    let G := ZT.ofNat (num (d+1).factorial)*prefixNumerator a M M
    let R := ZT.ofNat (num (radius a)*num (d+1).factorial*pw M (num d))
    (Γ ⊢[PRAAx] zle I (G+R)) ∧ (Γ ⊢[PRAAx] zle G (I+R)) := by
  let C := ((d+1).factorial : Groth (Q Γ))*𝔞(pw M (num d))
  let errors (i : Fin (d+1)) := (a i : Groth (Q Γ))*slack (Γ := Γ) i M
  let bounds (i : Fin (d+1)) := ((a i).natAbs : Groth (Q Γ))*C
  have hC : Nonneg Γ C := nn_mul (nn_natCast _) (nn_term _)
  have hb (i : Fin (d+1)) : Nonneg Γ (bounds i+errors i) ∧ Nonneg Γ (bounds i-errors i) :=
    signed_slacks (a i) _ C (monomial_slacks i M).1 hC (monomial_slacks i M).2
  have se : ∑ i, errors i =
      (meanNumerator a : Groth (Q Γ))*𝔞(pw M (num (d+1))) -
        ((d+1).factorial : Groth (Q Γ))*ZT.toZ Γ (prefixNumerator a M M) := by
    simp only [errors,slack,_root_.mul_sub,Finset.sum_sub_distrib,meanNumerator,Int.cast_sum,Int.cast_mul,
      Int.cast_natCast,prefixNumerator,ZT.toZ_sumFin,ZT.toZ_mul,toZ_zint,ZT.toZ_ofNat,Q.mk_mul,map_mul]
    rw [Finset.sum_mul,Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  have sb : ∑ i, bounds i = (radius a : Groth (Q Γ))*C := by
    simp [bounds,radius,Nat.cast_sum,Finset.sum_mul]
  have plus := nn_sum Finset.univ (fun i => bounds i+errors i) (fun i _ => (hb i).1)
  have minus := nn_sum Finset.univ (fun i => bounds i-errors i) (fun i _ => (hb i).2)
  rw [Finset.sum_add_distrib,sb,se] at plus
  rw [Finset.sum_sub_distrib,sb,se] at minus
  dsimp only
  constructor
  · apply zle_of_comb _ _ minus
    simp only [ZT.toZ_add,ZT.toZ_mul,toZ_zint,ZT.toZ_ofNat,Q.mk_mul,Q.mk_num,map_natCast,map_mul,C]
    ring
  · apply zle_of_comb _ _ plus
    simp only [ZT.toZ_add,ZT.toZ_mul,toZ_zint,ZT.toZ_ofNat,Q.mk_mul,Q.mk_num,map_natCast,map_mul,C]
    ring

end LeanProofs.IPRA.Analysis.RationalPolynomialGridMeanError
