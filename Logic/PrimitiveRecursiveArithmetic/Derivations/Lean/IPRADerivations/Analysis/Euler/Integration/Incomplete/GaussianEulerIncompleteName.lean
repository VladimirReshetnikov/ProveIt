import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteCofinalRate

/-!
# Regular names for the original incomplete Euler integrals

Each program queries its own compact piece at the same numerical cutoff
and precision used in the cofinal proof. The two original tails justify
regularity of these varying-cutoff programs on the positive half-plane.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteName

open_ipra
open GaussianEulerIncompleteCofinalRate (lowerSample upperSample source sample_regularity)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (z R B A a b : PTm n) : PTm n := pairT (pairT z R) (pairT (pairT B A) (pairT a b))

private def decoded (p x : PTm n) : Fin 7 → PTm n :=
  ![p, fstT (fstT x), sndT (fstT x), fstT (fstT (sndT x)), sndT (fstT (sndT x)),
    fstT (sndT (sndT x)), sndT (sndT (sndT x))]

private def reader (body : PTm 7) (p x : PTm n) : PTm n := Syn.subst (decoded p x) body
private def lowerBody : PTm 7 := lowerSample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
private def upperBody : PTm 7 := upperSample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
def lowerF : PR 2 := PTm.toPR (reader lowerBody (var 0) (var 1))
def upperF : PR 2 := PTm.toPR (reader upperBody (var 0) (var 1))

ipra_subst data

private theorem decoder_at (p z R B A a b : PTm n) (i : Fin 7) :
    Γ ⊢[PRAAx] decoded p (data z R B A a b) i ≐ (![p,z,R,B,A,a,b] : Fin 7 → PTm n) i := by
  let x := data z R B A a b
  have head : Γ ⊢[PRAAx] fstT x ≐ pairT z R := fst_pair _ _
  have tail : Γ ⊢[PRAAx] sndT x ≐ pairT (pairT B A) (pairT a b) := snd_pair _ _
  have middle : Γ ⊢[PRAAx] fstT (sndT x) ≐ pairT B A := tail.fstE
  have endp : Γ ⊢[PRAAx] sndT (sndT x) ≐ pairT a b := tail.sndE
  fin_cases i
  · exact .eqRefl _
  · exact head.fstE
  · exact head.sndE
  · exact middle.fstE
  · exact middle.sndE
  · exact endp.fstE
  · exact endp.sndE

private theorem reader_at (body : PTm 7) (p z R B A a b : PTm n) :
    Γ ⊢[PRAAx] ap2 (PTm.toPR (reader body (var 0) (var 1))) p (data z R B A a b) ≐
      Syn.subst (![p,z,R,B,A,a,b] : Fin 7 → PTm n) body := by
  let x := data z R B A a b
  have program := toPR_eq (Γ := Γ) (reader body (var 0) (var 1) : PTm 2) ![p,x]
  have substReader : Syn.subst (![p,x] : Fin 2 → PTm n) (reader body (var 0) (var 1)) = reader body p x := by
    unfold reader
    rw [Syn.subst_subst]
    congr 1
    funext i
    fin_cases i <;> simp [decoded]
  have readback : Γ ⊢[PRAAx] ap2 (PTm.toPR (reader body (var 0) (var 1))) p x ≐ reader body p x := by
    simpa only [ap2, substReader] using program
  exact readback.eqTrans (Prf.eqCongr body (decoder_at p z R B A a b))

theorem lower_at (p z R B A a b : PTm n) :
    Γ ⊢[PRAAx] ap2 lowerF p (data z R B A a b) ≐ lowerSample p z R B A a b := by
  simpa [lowerF, lowerBody] using reader_at (Γ := Γ) lowerBody p z R B A a b

theorem upper_at (p z R B A a b : PTm n) :
    Γ ⊢[PRAAx] ap2 upperF p (data z R B A a b) ≐ upperSample p z R B A a b := by
  simpa [upperF, upperBody] using reader_at (Γ := Γ) upperBody p z R B A a b

theorem original_observations (p q z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) :
    Γ ⊢[PRAAx]
      distanceBounded (ap2 lowerF p (data z R B A a b)) (ap2 lowerF q (data z R B A a b)) (unit p+unit q) (unit p*unit q) ⋏
      distanceBounded (ap2 upperF p (data z R B A a b)) (ap2 upperF q (data z R B A a b)) (unit p+unit q) (unit p*unit q) := by
  have hPair := sample_regularity p q z R B A a b h
  exact .andI
    (distance_congr (lower_at p z R B A a b).eqSymm (lower_at q z R B A a b).eqSymm (.eqRefl _) (.eqRefl _) hPair.andE₁)
    (distance_congr (upper_at p z R B A a b).eqSymm (upper_at q z R B A a b).eqSymm (.eqRefl _) (.eqRefl _) hPair.andE₂)

theorem original_regular_names (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) :
    Γ ⊢[PRAAx] pointCN lowerF (data z R B A a b) ⋏ pointCN upperF (data z R B A a b) := by
  let up (x : PTm n) := Syn.shift (Syn.shift x)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (up z) (up R) (up B) (up A) (up a) (up b) := by
    simpa only [Fm.shift, Syn.shift, GaussianEulerIncompleteCofinalRate.subst_source, up] using h.shift.shift
  have samples := original_observations (var 1) (var 0) (up z) (up R) (up B) (up A) (up a) (up b) hs
  refine .andI (.allI (.allI ?_)) (.allI (.allI ?_))
  · simpa only [pointCN, GaussianEuclideanPointDistance.unit, unit, Syn.shift, subst_data, up] using samples.andE₁
  · simpa only [pointCN, GaussianEuclideanPointDistance.unit, unit, Syn.shift, subst_data, up] using samples.andE₂

theorem actual_original_incomplete_Euler_regular_names_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        pointCN lowerF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ⋏
        pointCN upperF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_regular_names _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteName
