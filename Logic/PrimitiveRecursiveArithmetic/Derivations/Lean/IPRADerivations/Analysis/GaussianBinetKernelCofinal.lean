import IPRADerivations.Analysis.GaussianBinetKernelTail

/-!
# The cofinal Binet kernel name

At precision `p`, evaluate the first `2^p` rows of the actual Binet
kernel using finite-sum precision `p+1`. The sharp finite interval
bound gives a regular name and the independent cutoff error `1/(8N)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelCofinal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetKernelRows (inputData rowF rowBody regular_rows subst_inputData)
open GaussianBinetKernelTail (finiteF finiteData ordered_observations)
open GaussianBinetKernelTailMajorant (eight_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "eight" => num 8

def cutoff (p : PTm n) : PTm n := unit p
def sample (p A B : PTm n) : PTm n := ap2 finiteF (succ p) (finiteData (cutoff p) A B)
def nameF : PR 2 := PTm.toPR (sample (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2)

@[simp] theorem subst_cutoff {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (cutoff p) = cutoff (Syn.subst σ p) := by simp [cutoff]

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p A B : PTm n) :
    Syn.subst σ (sample p A B) = sample (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [sample, finiteData]

theorem sample_at (p A B : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (inputData A B) ≐ sample p A B := by
  let x := inputData A B
  have e : Γ ⊢[PRAAx] ap2 nameF p x ≐ sample p (fstT x) (sndT x) := by
    simpa only [nameF, ap2, subst_sample, subst_fstT, subst_sndT, Syn.subst_var,
      Matrix.cons_val_zero, Matrix.cons_val_one] using
      toPR_eq (Γ := Γ) (sample (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![p,x]
  exact e.eqTrans (congrAp2 finiteF (.eqRefl _) (congrPairT (.eqRefl _)
    (congrPairT (fst_pair A B) (snd_pair A B))))

private theorem unit_successor (p : PTm n) : Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p :=
  (pw_succ two p).eqTrans (mul_comm _ _)

theorem late_observations (p q N A B : PTm n) (hN : Γ ⊢[PRAAx] le (cutoff p) N)
    (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (inputData A B)) (ap2 finiteF q (finiteData N A B)) (unit p+unit q) (unit p*unit q) := by
  let U := unit p
  let V := unit q
  let D := eight*U
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) q
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ eight_positive hU
  have raw := ordered_observations q (succ p) N (cutoff p) A B hU hN hB
  have den := denominator_positive D q (succ p) hD
  have pad : Γ ⊢[PRAAx] le (rateNumerator one D q (succ p)*(U*V)) ((U+V)*rateDenominator D q (succ p)) := by
    refine le_of_eq_add (d := num 6*(U*U)*(V*V)) ?_
    have ep := natEq (unit_successor (Γ := Γ) p)
    apply deriveNat
    dsimp only [rateNumerator, rateDenominator, U, V, D]
    ipra_simps
    rw [ep]
    ring
  exact distance_congr (sample_at p A B).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ den (positive_product _ _ hU hV) pad (distance_symmetric _ _ _ _ den raw))

private theorem lower_second_error (x y p q : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded x y (unit p+unit (succ q)) (unit p*unit (succ q))) :
    Γ ⊢[PRAAx] distanceBounded x y (unit p+unit q) (unit p*unit q) := by
  have hp := unit_positive (Γ := Γ) p
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp (unit_positive (succ q)))
    (positive_product _ _ hp (unit_positive q)) ?_ h
  refine le_of_eq_add (d := unit p*unit p*unit q) ?_
  have eq := natEq (unit_successor (Γ := Γ) q)
  apply deriveNat
  ipra_simps
  rw [eq]
  ring

theorem observations (p q A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (inputData A B)) (ap2 nameF q (inputData A B)) (unit p+unit q) (unit p*unit q) := by
  refine (le_total (cutoff p) (cutoff q)).orE ?_ ?_
  · exact lower_second_error _ _ p q
      (distance_congr (.eqRefl _) (sample_at q A B).eqSymm (.eqRefl _) (.eqRefl _)
        (late_observations p (succ q) (cutoff q) A B Prf.hyp0 hB.wk))
  · have rev := lower_second_error _ _ q p
      (distance_congr (.eqRefl _) (sample_at p A B).eqSymm (.eqRefl _) (.eqRefl _)
        (late_observations q (succ p) (cutoff p) A B Prf.hyp0 hB.wk))
    exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p)) rev)

theorem regular (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] pointCN nameF (inputData A B) := by
  refine .allI (.allI ?_)
  let s (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hb : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using hB.shift.shift
  simpa only [GaussianEuclideanDistanceName.pointCN, GaussianEuclideanPointDistance.unit,
    GaussianCoefficientNameBounds.unit, Δ, s, Syn.shift, subst_inputData] using
    observations (var 1) (var 0) (s A) (s B) hb

private theorem cutoff_diagonal (p N A B : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (inputData A B)) (ap2 finiteF p (finiteData N A B))
      (diagonalNumerator one (eight*N) two p) (diagonalDenominator (eight*N) p) := by
  let U := unit p
  let D := eight*N
  have hU := unit_positive (Γ := Γ) p
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ eight_positive hN
  have ready := positive_product _ _ hD hU
  refine (le_total N (cutoff p)).orE ?_ ?_
  · have raw := ordered_observations (succ p) p (cutoff p) N A B hN.wk Prf.hyp0 hB.wk
    have hz := denominator_positive D (succ p) p hD
    apply distance_congr (sample_at p A B).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    apply distance_radius_mono _ _ _ _ _ _ hz.wk ready.wk ?_ raw
    refine le_of_eq_add (d := D*D*U*U) ?_
    have eq := natEq (unit_successor (Γ := (le N (cutoff p)) :: Γ) p)
    apply deriveNat
    dsimp only [diagonalNumerator, diagonalDenominator, rateNumerator, rateDenominator, D, U]
    ipra_simps
    rw [eq]
    ring
  · apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU.wk hU.wk) ready.wk ?_
      (late_observations p p N A B Prf.hyp0 hB.wk)
    exact le_of_eq_add (d := U*U*U) (by dsimp only [diagonalNumerator, diagonalDenominator, U, D]; ipra_ring)

theorem cutoff_rate (N A B : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    independentRate nameF finiteF (inputData A B) (finiteData N A B) one (eight*N) := by
  apply GaussianNamedLipschitzRate.independent_rate nameF finiteF _ _ one (eight*N) two
    (positive_product _ _ eight_positive hN) (regular A B hB)
    (GaussianNamedFiniteSumFamily.regular rowF rowBody N (inputData A B) (regular_rows N A B hB))
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let s (v : PTm n) := Syn.shift v
  have hn : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift] using hN.shift
  have hb : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using hB.shift
  simpa only [diagonalEnvelope,Syn.shift,s,finiteData,GaussianNamedFiniteSumFamily.subst_data,subst_inputData,
    PTm.subst_mul,PTm.subst_num,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    cutoff_diagonal (var 0) (s N) (s A) (s B) hn hb

theorem actual_Binet_kernel_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ pointCN nameF (inputData (var 0) (var 1))) :=
  closeUniv 2 (.impI (regular _ _ Prf.hyp0))

theorem actual_Binet_kernel_cutoff_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le one (var 2) ⟶ independentRate nameF finiteF
      (inputData (var 1) (var 2)) (finiteData (var 0) (var 1) (var 2)) one (eight*var 0)) :=
  closeUniv 3 (.impI (.impI (cutoff_rate _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetKernelCofinal
