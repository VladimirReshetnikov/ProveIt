import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalPowerBounds.RationalReciprocalPowerTail

/-!
# Adjacent brackets for every reciprocal-power integral

The two antiderivative endpoint conventions bracket the actual
finite reciprocal-power tail. The lower comparison complements the
existing finite conservation law at arbitrary internal exponent.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPowerIntegral

open_ipra
open GaussianEuclideanDistanceName (fraction fraction_represents fraction_order)
open RationalReciprocalPowerTail (reciprocalPower potential tail tail_zero tail_succ
  potential_congr reciprocal_congr exponent_form potential_denominator_positive add_zero_right)
open RationalNonnegativePowers (fraction_congr)
open RationalArithmetic (add)
open RationalArgmin (rationalLE rationalLE_congr reflexive transitive)
open RationalAlgebra (positive_product add_congr add_associative add_commutative)
open GaussianRationalSyntheticBounds (add_monotone)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem native_antiderivative_lower (k q : PTm n) : Γ ⊢[PRAAx]
    le (k*pw (succ k) (succ q)) (pw k (succ (succ q))+succ q*pw (succ k) (succ q)) := by
  have h := PowerSums.upper (Γ := Γ) k q
  have a := natEq (pw_succ (Γ := Γ) k (succ q))
  have b := natEq (pw_succ (Γ := Γ) (succ k) q)
  ipra_le 𝔞(k)*sl h+𝔞(succ q)*𝔞(pw (succ k) q) using
    rw [a,b]
    ring

theorem one_step_successors (q k : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    rationalLE (potential (succ (succ q)) k)
      (add (reciprocalPower (succ (succ q)) k) (potential (succ (succ q)) (succ k))) := by
  let p := succ q
  let W := succ k
  have hp : Γ ⊢[PRAAx] le one p := zero_lt_succ q
  have hK := GaussianFactorBudget.power_positive (Γ := Γ) k p hk
  have hQ := GaussianFactorBudget.power_positive (Γ := Γ) k (succ p) hk
  have hE := positive_product hp hK
  have hD := positive_product hp (GaussianFactorBudget.power_positive W p (zero_lt_succ _))
  have sumrep := RationalRepresentations.represents_add (Γ := Γ)
    (fraction one (pw k (succ p))) (fraction one (p*pw W p)) _ _ _ _
    (fraction_represents _ _ hQ) (fraction_represents _ _ hD)
  have rep : Γ ⊢[PRAAx] RationalArithmetic.represents
      (add (fraction one (pw k (succ p))) (fraction one (p*pw W p)))
      (ZT.ofNat (p*pw W p+pw k (succ p))) (pw k (succ p)*(p*pw W p)) := by
    apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := sumrep)
    apply ZT.derive
    simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
    ring
  have native := native_antiderivative_lower (Γ := Γ) k q
  have step := natEq (pw_succ (Γ := Γ) k p)
  have cmp : Γ ⊢[PRAAx]
      le (one*(pw k (succ p)*(p*pw W p))) ((p*pw k p)*(p*pw W p+pw k (succ p))) := by
    ipra_le 𝔞(p)*𝔞(pw k p)*sl native using
      dsimp [p,W] at *
      ipra_simps
      rw [step]
      ring
  have result := GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    hE (positive_product hQ hD) (fraction_represents one _ hE) rep
    (le_congr (mul_comm _ _) (mul_comm _ _) cmp)
  have ep := LeanProofs.IPRA.pred_succ (Γ := Γ) (succ q)
  exact rationalLE_congr
    (fraction_congr (.eqRefl _) (congrMul ep.eqSymm (congrAp2 powF ep.eqSymm (.eqRefl _))))
    (add_congr (.eqRefl _) (fraction_congr (.eqRefl _)
      (congrMul ep.eqSymm (congrAp2 powF ep.eqSymm (.eqRefl _))))) result

theorem one_step (m k : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    rationalLE (potential m k) (add (reciprocalPower m k) (potential m (succ k))) := by
  have em := exponent_form m hm
  exact rationalLE_congr (potential_congr em.eqSymm (.eqRefl _))
    (add_congr (reciprocal_congr em.eqSymm (.eqRefl _)) (potential_congr em.eqSymm (.eqRefl _)))
    (one_step_successors (monus m two) k hk)

def lowerLaw (m N L : PTm n) : Fm PTm n :=
  rationalLE (potential m (succ N)) (add (tail m N L) (potential m (succ (N+L))))

ipra_subst lowerLaw

private theorem lower_zero (m N : PTm n) (hm : Γ ⊢[PRAAx] le two m) : Γ ⊢[PRAAx] lowerLaw m N zero := by
  have e : Γ ⊢[PRAAx] add (tail m N zero) (potential m (succ (N+zero))) ≐ potential m (succ N) :=
    (add_congr (tail_zero m N) (potential_congr (.eqRefl _) (congrSucc (add_zero N)))).eqTrans
    ((add_commutative _ _).eqTrans (add_zero_right _ (RationalNormalForm.normalize_well_formed _ _
      (potential_denominator_positive m (succ N) hm (zero_lt_succ _)))))
  exact rationalLE_congr (.eqRefl _) e.eqSymm (reflexive _)

private theorem lower_succ (m N L : PTm n) (hm : Γ ⊢[PRAAx] le two m)
    (ih : Γ ⊢[PRAAx] lowerLaw m N L) : Γ ⊢[PRAAx] lowerLaw m N (succ L) := by
  let j := succ (N+L)
  have h := one_step m j hm (zero_lt_succ _)
  have hn := add_monotone (tail m N L) (tail m N L) _ _ (reflexive _) h
  have e : Γ ⊢[PRAAx] add (tail m N (succ L)) (potential m (succ (N+succ L))) ≐
      add (tail m N L) (add (reciprocalPower m j) (potential m (succ j))) :=
    (add_congr (tail_succ m N L) (potential_congr (.eqRefl _) (congrSucc (by dsimp [j]; ipra_ring)))).eqTrans
      (add_associative _ _ _)
  exact transitive ih (rationalLE_congr (.eqRefl _) e.eqSymm hn)

theorem lower_bound (m N L : PTm n) (hm : Γ ⊢[PRAAx] le two m) : Γ ⊢[PRAAx] lowerLaw m N L := by
  have all : Γ ⊢[PRAAx] .all (lowerLaw (Syn.shift m) (Syn.shift N) (var 0)) := by
    ipra_qfind [subst_lowerLaw]
    · exact lower_zero m N hm
    · have hms : Γ.map Fm.shift ⊢[PRAAx] le two (Syn.shift m) := by simpa [Fm.shift,Syn.shift] using hm.shift
      exact lower_succ (Syn.shift m) (Syn.shift N) (var 0) hms.wk Prf.hyp0
  simpa only [subst_lowerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE L

theorem integral_brackets_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le two (var 0) ⟶ le one (var 1) ⟶ lowerLaw (var 0) (var 1) (var 2) ⋏
        rationalLE (add (tail (var 0) (var 1) (var 2)) (potential (var 0) (var 1+var 2)))
          (potential (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (.andI (lower_bound _ _ _ Prf.hyp1)
    (RationalReciprocalPowerTail.finite_conservation _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPowerIntegral
