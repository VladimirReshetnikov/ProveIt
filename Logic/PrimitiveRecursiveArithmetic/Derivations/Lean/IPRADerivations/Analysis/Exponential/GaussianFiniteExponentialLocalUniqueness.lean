import IPRADerivations.Analysis.Exponential.Estimates.GaussianExponentialLinearRemainder
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialReference
import IPRADerivations.Analysis.Integration.Partitions.GaussianRationalPanelTailDistance

/-!
# Finite contraction when the original exponential is close to one

This estimate uses the unchanged factorial scalar sum at an arbitrary
positive cutoff. Its linear remainder bounds the input by the square
of its current radius plus the output error. A finite induction gives
as many halvings as the output precision pays for.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianFiniteExponentialLocalUniqueness

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (qadd canonical positive_product)
open GaussianRationalSyntheticDivision (qone qsub_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPolynomialExponential (scalarSum)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_symmetric distance_radius_mono)

open GaussianExponentialLinearRemainder (original_finite_linear_remainder)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem improvement (q K A B E : PTm n)
    (hc : Γ ⊢[PRAAx] canonical q) (hk : Γ ⊢[PRAAx] le one K)
    (hb : Γ ⊢[PRAAx] le one B) (hab : Γ ⊢[PRAAx] le A B)
    (hE : Γ ⊢[PRAAx] le one E)
    (hq : Γ ⊢[PRAAx] bounded q A B)
    (he : Γ ⊢[PRAAx] distanceBounded (scalarSum q K) qone one E) :
    Γ ⊢[PRAAx] bounded q (A*A*E+B*B) (B*B*E) := by
  let S := scalarSum q K
  let X := qadd qone q
  let D := B*B
  have hd := positive_product B B hb hb
  have error := original_finite_linear_remainder q A B K hb hab hq hc hk
  have joined := GaussianRationalPanelTailDistance.triangle X S qone (A*A) D one E hd hE
    (distance_symmetric _ _ _ _ hd error) he
  have e := (qsub_congr (GaussianReciprocalHorner.qadd_commutative (Γ := Γ) qone q) (.eqRefl qone)).eqTrans
    (GaussianReciprocalHorner.qsub_add_cancel q qone hc)
  exact bound_congr e (by dsimp [D]; ipra_ring) (.eqRefl _) joined

def tolerance (p : PTm n) : PTm n := num 16*unit p
def radiusDen (k : PTm n) : PTm n := num 4*unit k
def invariant (q p k : PTm n) : Fm PTm n := le k p ⟶ bounded q one (radiusDen k)

ipra_subst tolerance
ipra_subst radiusDen
ipra_subst invariant

theorem tolerance_lower (p : PTm n) : Γ ⊢[PRAAx] le (num 16) (tolerance p) := by
  unfold tolerance
  ipra_le 16*sl (unit_positive p)

theorem radius_lower (k : PTm n) : Γ ⊢[PRAAx] le (num 4) (radiusDen k) := by
  unfold radiusDen
  ipra_le 4*sl (unit_positive k)

private theorem initial_radius (q K p : PTm n) (hc : Γ ⊢[PRAAx] canonical q)
    (hk : Γ ⊢[PRAAx] le one K) (hq : Γ ⊢[PRAAx] bounded q (num 3) (num 4))
    (he : Γ ⊢[PRAAx] distanceBounded (scalarSum q K) qone one (tolerance p)) :
    Γ ⊢[PRAAx] bounded q one (num 4) := by
  let E := tolerance p
  have e := tolerance_lower (Γ := Γ) p
  have hE : Γ ⊢[PRAAx] le one E := le_trans (by ipra_le 15) e
  have first := improvement q K (num 3) (num 4) E hc hk (by ipra_le 3) (by ipra_le 1) hE hq he
  have a : Γ ⊢[PRAAx] bounded q (num 5) (num 8) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ (by ipra_le 15) hE) (by ipra_le 7)
      (by ipra_le 8*sl e) first
  have second := improvement q K (num 5) (num 8) E hc hk (by ipra_le 7) (by ipra_le 3) hE a he
  have b : Γ ⊢[PRAAx] bounded q one two :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ (by ipra_le 63) hE) (by ipra_le 1)
      (by ipra_le 14*sl e + 96) second
  have third := improvement q K one two E hc hk (by ipra_le 1) (by ipra_le 1) hE b he
  have c : Γ ⊢[PRAAx] bounded q (num 3) (num 8) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ (by ipra_le 3) hE) (by ipra_le 7)
      (by ipra_le 4*sl e + 32) third
  have fourth := improvement q K (num 3) (num 8) E hc hk (by ipra_le 7) (by ipra_le 5) hE c he
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (by ipra_le 63) hE) (by ipra_le 3)
    (by ipra_le 28*sl e + 192) fourth

private theorem halve (q K p k : PTm n) (hc : Γ ⊢[PRAAx] canonical q)
    (hk : Γ ⊢[PRAAx] le one K) (ht : Γ ⊢[PRAAx] le k p)
    (he : Γ ⊢[PRAAx] distanceBounded (scalarSum q K) qone one (tolerance p))
    (h : Γ ⊢[PRAAx] bounded q one (radiusDen k)) :
    Γ ⊢[PRAAx] bounded q one (radiusDen (succ k)) := by
  let B := radiusDen k
  let E := tolerance p
  have b := radius_lower (Γ := Γ) k
  have hB : Γ ⊢[PRAAx] le one B := le_trans (by ipra_le 3) b
  have hE : Γ ⊢[PRAAx] le one E := le_trans (by ipra_le 15) (tolerance_lower p)
  have u := GaussianExponentialReference.unit_monotone ht
  have fit : Γ ⊢[PRAAx] le (num 4*B) E := by
    unfold B radiusDen E tolerance
    ipra_le 16*sl u
  have raw := improvement q K one B E hc hk hB hB hE h he
  have next : Γ ⊢[PRAAx] radiusDen (succ k) ≐ two*B :=
    (congrMul (.eqRefl _) (pw_succ two k)).eqTrans (by dsimp [B,radiusDen,unit]; ipra_ring)
  have hnext : Γ ⊢[PRAAx] le one (radiusDen (succ k)) := le_trans (by ipra_le 3) (radius_lower _)
  have pay : Γ ⊢[PRAAx] le ((one*one*E+B*B)*(two*B)) (one*(B*B*E)) := by
    apply RationalValueBounds.positive_cancel (c := two) (by ipra_le 1)
    ipra_le 𝔞 B*𝔞 E*sl b+(𝔞 B)^2*sl fit
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hB hB) hE)
    hnext (le_congr (congrMul (.eqRefl _) next).eqSymm (.eqRefl _) pay) raw

theorem contraction (q K p : PTm n) (hc : Γ ⊢[PRAAx] canonical q)
    (hk : Γ ⊢[PRAAx] le one K) (hq : Γ ⊢[PRAAx] bounded q (num 3) (num 4))
    (he : Γ ⊢[PRAAx] distanceBounded (scalarSum q K) qone one (tolerance p)) :
    Γ ⊢[PRAAx] bounded q one (unit p) := by
  have base := initial_radius q K p hc hk hq he
  have denom : Γ ⊢[PRAAx] radiusDen (zero : PTm n) ≐ num 4 :=
    (congrMul (.eqRefl _) (pw_zero two)).eqTrans (by ipra_ring)
  have initial := bound_congr (.eqRefl _) (.eqRefl _) denom.eqSymm base
  have all : Γ ⊢[PRAAx] .all (invariant (Syn.shift q) (Syn.shift p) (var 0)) := by
    ipra_qfind (by simp [invariant,bounded,RationalArgmin.rationalLE,Fm.QF,le_QF]) [subst_invariant]
    · exact .impI initial.wk
    · let s := fun t : PTm n => Syn.shift t
      let Δ := (le (succ (var 0)) (s p) :: invariant (s q) (s p) (var 0) :: Γ.map Fm.shift)
      have c : Δ ⊢[PRAAx] canonical (s q) := by simpa [Fm.shift,Syn.shift,s,Δ] using hc.shift.wk.wk
      have k : Δ ⊢[PRAAx] le one (s K) := by simpa [Fm.shift,Syn.shift,s,Δ] using hk.shift.wk.wk
      have e : Δ ⊢[PRAAx] distanceBounded (scalarSum (s q) (s K)) qone one (tolerance (s p)) := by
        simpa [Fm.shift,Syn.shift,s,Δ,one] using he.shift.wk.wk
      refine .impI (halve (s q) (s K) (s p) (var 0) c k ?_ e ?_)
      · exact le_trans (le_succ_self _) Prf.hyp0
      · exact .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
  have v : Γ ⊢[PRAAx] invariant q p p := by
    simpa only [subst_invariant,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE p
  have hp := unit_positive (Γ := Γ) p
  exact bounded_radius_mono _ _ _ _ _ (le_trans (by ipra_le 3) (radius_lower _)) hp
    (by unfold radiusDen; ipra_le 3*𝔞(unit p)) (.impE v (le_refl p))

theorem actual_finite_exponential_small_unit_contraction_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((canonical (var 0) ⋏ (le one (var 1) ⋏ bounded (var 0) (num 3) (num 4))) ⟶
        distanceBounded (scalarSum (var 0) (var 1)) qone one (tolerance (var 2)) ⟶
        bounded (var 0) one (unit (var 2))) :=
  closeUniv 3 (.impI (.impI (contraction _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianFiniteExponentialLocalUniqueness
