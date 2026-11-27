import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalPowerBounds.RationalReciprocalPowerTail
import IPRADerivations.Analysis.Inequalities.NonnegativeArithmetic.RationalNonnegativePowers

/-!
# Two-sided finite brackets for the inverse-square integral

For the actual finite sum of reciprocal squares from N+1 to N+L,
the rational antiderivative differences at both adjacent sets of
endpoints bracket the sum. The upper estimate is the original C17
conservation law at degree two. The lower estimate is the opposite
one-cell comparison, iterated by quantifier-free induction.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSquareIntegral

open_ipra
open GaussianEuclideanDistanceName (fraction fraction_represents fraction_order)
open GaussianRationalHorner (positive_product)
open RationalReciprocalPowerTail (tail tail_zero tail_succ reciprocalPower potential add_zero_right)
open RationalNonnegativePowers (fraction_congr)
open RationalArithmetic (add)
open RationalArgmin (rationalLE rationalLE_congr reflexive transitive)
open RationalAlgebra (add_congr add_associative add_commutative)
open GaussianRationalSyntheticBounds (add_monotone)

variable {n : ℕ} {Γ : List (Fm PTm n)}


def inverse (j : PTm n) : PTm n := fraction one j

ipra_subst inverse

theorem inverse_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] inverse a ≐ inverse b := fraction_congr (.eqRefl _) h

theorem potential_two (j : PTm n) : Γ ⊢[PRAAx] potential two j ≐ inverse j := by
  have e : Γ ⊢[PRAAx] pred two ≐ one := pred_succ one
  exact fraction_congr (.eqRefl _) ((congrMul e ((congrAp2 powF e (.eqRefl j)).eqTrans (pw_one j))).eqTrans (one_mul j))

theorem reciprocal_square (j : PTm n) : Γ ⊢[PRAAx] reciprocalPower two j ≐ fraction one (j*j) :=
  fraction_congr (.eqRefl _) ((pw_succ j one).eqTrans (congrMul (pw_one j) (.eqRefl _)))

private theorem fraction_sum (A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] add (fraction A B) (fraction C D) ≐ fraction (A*D+C*B) (B*D) := by
  have hBD := positive_product _ _ hB hD
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ hBD)
    (RationalRepresentations.represents_add _ _ _ _ _ _ (fraction_represents _ _ hB) (fraction_represents _ _ hD))
    (fraction_represents _ _ hBD) hBD hBD
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_add]
  ipra_simps

theorem lower_step (j : PTm n) (h : Γ ⊢[PRAAx] le one j) : Γ ⊢[PRAAx]
    rationalLE (inverse j) (add (reciprocalPower two j) (inverse (succ j))) := by
  have h₂ := positive_product j j h h
  have hn : Γ ⊢[PRAAx] le one (succ j) := zero_lt_succ _
  have ep := (add_congr (reciprocal_square j) (.eqRefl (inverse (succ j)))).eqTrans
    (fraction_sum one (j*j) one (succ j) h₂ hn)
  have crossed : Γ ⊢[PRAAx] le ((j*j*succ j)*one) ((one*succ j+one*(j*j))*j) := by
    ipra_le Groth.ι (IPRA.Q.mk Γ j)
  exact rationalLE_congr (.eqRefl _) ep.eqSymm (fraction_order _ _ _ _ h (positive_product _ _ h₂ hn) crossed)

def lowerLaw (N L : PTm n) : Fm PTm n :=
  rationalLE (inverse (succ N)) (add (tail two N L) (inverse (succ (N+L))))

ipra_subst lowerLaw

private theorem lower_zero (N : PTm n) : Γ ⊢[PRAAx] lowerLaw N zero := by
  have e : Γ ⊢[PRAAx] add (tail two N zero) (inverse (succ (N+zero))) ≐ inverse (succ N) :=
    (add_congr (tail_zero two N) (inverse_congr (congrSucc (add_zero N)))).eqTrans
    ((add_commutative _ _).eqTrans (add_zero_right _ (RationalNormalForm.normalize_well_formed _ _ (zero_lt_succ _))))
  exact rationalLE_congr (.eqRefl _) e.eqSymm (reflexive _)

private theorem lower_succ (N L : PTm n) (ih : Γ ⊢[PRAAx] lowerLaw N L) :
    Γ ⊢[PRAAx] lowerLaw N (succ L) := by
  let j := succ (N+L)
  have h := lower_step (Γ := Γ) j (zero_lt_succ _)
  have hn := add_monotone (tail two N L) (tail two N L) _ _ (reflexive _) h
  have e : Γ ⊢[PRAAx] add (tail two N (succ L)) (inverse (succ (N+succ L))) ≐
      add (tail two N L) (add (reciprocalPower two j) (inverse (succ j))) :=
    (add_congr (tail_succ two N L) (inverse_congr (congrSucc (by dsimp [j]; ipra_ring)))).eqTrans
      (add_associative _ _ _)
  exact transitive ih (rationalLE_congr (.eqRefl _) e.eqSymm hn)

theorem lower_bound (N L : PTm n) : Γ ⊢[PRAAx] lowerLaw N L := by
  have all : Γ ⊢[PRAAx] .all (lowerLaw (Syn.shift N) (var 0)) := by
    ipra_qfind [subst_lowerLaw]
    · exact lower_zero (Γ := Γ) N
    · exact lower_succ (Syn.shift N) (var 0) Prf.hyp0
  simpa only [subst_lowerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE L

theorem upper_bound (N L : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] rationalLE (add (tail two N L) (inverse (N+L))) (inverse N) :=
  rationalLE_congr (add_congr (.eqRefl _) (potential_two _)) (potential_two _)
    (RationalReciprocalPowerTail.finite_conservation two N L (le_refl two) hN)

def error (N : PTm n) : PTm n := fraction one (N*succ N)

theorem inverse_difference (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] add (inverse (succ N)) (error N) ≐ inverse N := by
  have hS : Γ ⊢[PRAAx] le one (succ N) := zero_lt_succ _
  have hD := positive_product N (succ N) hN hS
  refine (fraction_sum one (succ N) one (N*succ N) hS hD).eqTrans ?_
  have hE := positive_product _ _ hS hD
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ hE) (RationalNormalForm.normalize_well_formed _ _ hN)
    (fraction_represents _ _ hE) (fraction_represents _ _ hN) hE hN
  apply ZT.derive
  simp only [ZT.toZ_mul, ZT.toZ_ofNat]
  ipra_simps
  ring

theorem finite_error (N L : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] rationalLE (add (tail two N L) (inverse (N+L))) (inverse N) ⋏
      rationalLE (inverse N) (add (add (tail two N L) (inverse (N+L))) (error N)) := by
  have hNL := le_trans hN (le_add_right N L)
  have ordered : Γ ⊢[PRAAx] rationalLE (inverse (succ (N+L))) (inverse (N+L)) :=
    fraction_order one (succ (N+L)) one (N+L) (zero_lt_succ _) hNL
      (le_congr (by ipra_ring) (by ipra_ring) (le_succ_self (N+L)))
  have h := transitive (lower_bound N L)
    (add_monotone (tail two N L) (tail two N L) _ _ (reflexive _) ordered)
  exact .andI (upper_bound N L hN) (rationalLE_congr (inverse_difference N hN) (.eqRefl _)
    (add_monotone _ _ (error N) (error N) h (reflexive _)))

theorem actual_square_integral_brackets_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (le one (var 0) ⟶ lowerLaw (var 0) (var 1) ⋏
        rationalLE (add (tail two (var 0) (var 1)) (inverse (var 0+var 1))) (inverse (var 0))) :=
  closeUniv 2 (.impI (.andI (lower_bound _ _) (upper_bound _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSquareIntegral
