import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.Windows.GaussianGammaZetaMellinNestedBound

/-!
# The original Mellin improper integral as a regular name

The powered lower cutoff and the integer upper cutoff are advanced
by an explicit primitive-recursive schedule. Two observations of
the original integral compare through one enclosing compact panel.
-/

set_option autoImplicit false
set_option maxHeartbeats 1350000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinImproper

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaIntegralCutoffs (top height omitted_tail_budget)
open GaussianGammaZetaMellinCutoffWindows (datum)
open GaussianGammaZetaMellinUpperPoint (coefficientBound)
open GaussianNameEquivalence (point_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianExponentialReference (unit_monotone)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "F" => GaussianGammaZetaMellinCompact.nameF
local notation "S" => GaussianEulerLowerPowerCoefficients.source

def cutoff (p R : PTm n) : PTm n :=
  p+(two*coefficientBound (R+one))*unit p

def data (z R B j : PTm n) : PTm n := pairT (pairT z R) (pairT B j)

def value (p z R B j : PTm n) : PTm n :=
  let r := p+num 4
  ap2 F r (datum z R B (succ j) (cutoff r R))

def nameF : PR 2 := PTm.toPR (value (var 0) (fstT (fstT (var 1))) (sndT (fstT (var 1)))
  (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)

ipra_subst cutoff [one, two]

ipra_subst data

ipra_subst value

theorem sample_at (p z R B j : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data z R B j) ≐ value p z R B j := by
  let x := data z R B j
  let body : PTm 2 := value (var 0) (fstT (fstT (var 1))) (sndT (fstT (var 1)))
    (fstT (sndT (var 1))) (sndT (sndT (var 1)))
  let a := fstT (fstT x)
  let b := sndT (fstT x)
  let c := fstT (sndT x)
  let d := sndT (sndT x)
  have read : Γ ⊢[PRAAx] ap2 nameF p x ≐ value p a b c d := by
    have e : Syn.subst ![p,x] body = value p a b c d := by
      dsimp only [body]
      rw [subst_value]
      simp only [subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
      rfl
    change Γ ⊢[PRAAx] ap2 (PTm.toPR body) p x ≐ _
    rw [← e]
    exact toPR_eq (Γ := Γ) body ![p,x]
  let w : PTm 5 := value (var 0) (var 1) (var 2) (var 3) (var 4)
  let u : Fin 5 → PTm n := ![p,a,b,c,d]
  let v : Fin 5 → PTm n := ![p,z,R,B,j]
  have left := fst_pair (Γ := Γ) (pairT z R) (pairT B j)
  have right := snd_pair (Γ := Γ) (pairT z R) (pairT B j)
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) w (σ := u) (σ' := v) (fun i => by
    fin_cases i
    · exact .eqRefl _
    · exact (congrFst left).eqTrans (fst_pair _ _)
    · exact (congrSnd left).eqTrans (snd_pair _ _)
    · exact (congrFst right).eqTrans (fst_pair _ _)
    · exact (congrSnd right).eqTrans (snd_pair _ _))
  have uEq : Syn.subst u w = value p a b c d := by dsimp only [w]; rw [subst_value]; rfl
  have vEq : Syn.subst v w = value p z R B j := by dsimp only [w]; rw [subst_value]; rfl
  rw [uEq,vEq] at e
  exact read.eqTrans e

theorem cutoff_budgets (v R A p : PTm n) (hp : Γ ⊢[PRAAx] le (cutoff v R) p) :
    Γ ⊢[PRAAx] le ((two*A)*unit v) (unit (height p A R)) ⋏
      le ((two*coefficientBound (R+one))*unit v) (top p A R) := by
  let K := two*coefficientBound (R+one)
  let W := unit v
  let Q := unit p
  let C := GaussianGammaIntegralCutoffs.tailCoefficient R
  have v₁ : Γ ⊢[PRAAx] le v p := le_trans (le_add_right v (K*W)) hp
  have h₁ : Γ ⊢[PRAAx] le (two*W) (num 3*Q) := by
    have e := unit_monotone v₁
    ipra_le 2*sl e+𝔞(Q)
  have h₂ := le_trans h₁ (GaussianCompactRiemannName.dyadic_six_lower p)
  have first : Γ ⊢[PRAAx] le (A*(two*W)) ((A+C)*unit (p+num 6)) :=
    le_mul_mono (le_add_right A C) h₂
  have lower : Γ ⊢[PRAAx] le ((two*A)*W) (unit (height p A R)) :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) first) (le_of_lt (omitted_tail_budget p A R))
  have greater : Γ ⊢[PRAAx] le p (height p A R) := by
    unfold height
    exact le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have up : Γ ⊢[PRAAx] le (height p A R) (top p A R) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right _ (le_succ_self one))
  exact .andI lower (le_trans (le_add_left (K*W) v) (le_trans hp (le_trans greater up)))

theorem reference_to_enclosing (h r z R B j q : PTm n)
    (hz : Γ ⊢[PRAAx] S z R B (succ j)) (hq : Γ ⊢[PRAAx] lt (cutoff h R) q)
    (hr : Γ ⊢[PRAAx] le h r) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F h (datum z R B (succ j) (cutoff h R)))
      (ap2 F r (datum z R B (succ j) q)) (num 11) (unit h) := by
  let p := cutoff h R
  let W := unit h
  let U := unit r
  let x := datum z R B (succ j) p
  let y := datum z R B (succ j) q
  have paid := cutoff_budgets (Γ := Γ) h R (succ j) p (le_refl p)
  have hw := unit_positive (Γ := Γ) h
  have hu := unit_positive (Γ := Γ) r
  have both := positive_product _ _ hw hu
  have later := unit_monotone (Γ := Γ) hr
  have left : Γ ⊢[PRAAx] distanceBounded (ap2 F h x) (ap2 F r x) two W :=
    distance_radius_mono _ _ _ _ _ _ both hw
      (by change Γ ⊢[PRAAx] le ((W+U)*W) (two*(W*U)); ipra_le 𝔞(W)*sl later)
      (point_at F x h r (GaussianGammaZetaMellinCutoffWindows.regular z R B (succ j) p hz))
  have raw := GaussianGammaZetaMellinNestedBound.ordered_observation_bound r h z R B j p q hz hq
    paid.andE₁ paid.andE₂
  have right : Γ ⊢[PRAAx] distanceBounded (ap2 F r x) (ap2 F r y) (num 9) W :=
    distance_radius_mono _ _ _ _ _ _ both hw
      (by change Γ ⊢[PRAAx] le ((two*U+num 7*W)*W) (num 9*(W*U)); ipra_le 7*𝔞(W)*sl later)
      (distance_symmetric _ _ _ _ both raw)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hw left right)

private theorem padded_unit (p : PTm n) : Γ ⊢[PRAAx] unit (p+num 4) ≐ num 16*unit p := by
  have e : Γ ⊢[PRAAx] unit (num 4 : PTm n) ≐ num 16 :=
    LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound.pw_num 2 4
  exact ((pw_add two p (num 4)).eqTrans (congrMul (.eqRefl _) e)).eqTrans (mul_comm _ _)

theorem independent_observations (p s z R B j : PTm n) (hz : Γ ⊢[PRAAx] S z R B (succ j)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B j)) (ap2 nameF s (data z R B j))
      (unit p+unit s) (unit p*unit s) := by
  let h := p+num 4
  let k := s+num 4
  let r := h+k
  let q := succ (cutoff h R+cutoff k R)
  let x := value p z R B j
  let y := value s z R B j
  let g := ap2 F r (datum z R B (succ j) q)
  let A := unit p
  let B' := unit s
  let U := unit h
  let V := unit k
  let D := U*V
  have hU := unit_positive (Γ := Γ) h
  have hV := unit_positive (Γ := Γ) k
  have hD := positive_product _ _ hU hV
  have hp : Γ ⊢[PRAAx] lt (cutoff h R) q :=
    (succ_monus_succ _ _).eqTrans (le_add_right _ _)
  have hs : Γ ⊢[PRAAx] lt (cutoff k R) q :=
    (succ_monus_succ _ _).eqTrans (le_add_left _ _)
  have left : Γ ⊢[PRAAx] distanceBounded x g (num 11*V) D :=
    distance_radius_mono _ _ _ _ _ _ hU hD (le_of_eq_add (d := zero) (by dsimp only [D,U]; ipra_ring))
      (reference_to_enclosing h r z R B j q hz hp (le_add_right _ _))
  have right : Γ ⊢[PRAAx] distanceBounded g y (num 11*U) D :=
    distance_symmetric _ _ _ _ hD
      (distance_radius_mono _ _ _ _ _ _ hV hD (le_of_eq_add (d := zero) (by dsimp only [D,V]; ipra_ring))
        (reference_to_enclosing k r z R B j q hz hs (le_add_left _ _)))
  have room₁ : Γ ⊢[PRAAx] le (num 11*A) U :=
    le_congr (.eqRefl _) (padded_unit p).eqSymm (by ipra_le 5*𝔞(A))
  have room₂ : Γ ⊢[PRAAx] le (num 11*B') V :=
    le_congr (.eqRefl _) (padded_unit s).eqSymm (by ipra_le 5*𝔞(B'))
  have close : Γ ⊢[PRAAx] distanceBounded x y (A+B') (A*B') :=
    distance_radius_mono _ _ _ _ _ _ hD (positive_product _ _ (unit_positive p) (unit_positive s))
      (by change Γ ⊢[PRAAx] le ((num 11*V+num 11*U)*(A*B')) ((A+B')*(U*V))
          ipra_le 𝔞(V*B')*sl room₁+𝔞(U*A)*sl room₂)
      (distance_triangle_same x g y _ _ _ hD left right)
  exact distance_congr (sample_at p z R B j).eqSymm (sample_at s z R B j).eqSymm
    (.eqRefl _) (.eqRefl _) close

theorem regular (z R B j : PTm n) (hz : Γ ⊢[PRAAx] S z R B (succ j)) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B j) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have guard : Δ ⊢[PRAAx] S (sh z) (sh R) (sh B) (succ (sh j)) := by
    simpa [Δ, sh, Fm.shift, Syn.shift] using hz.shift.shift
  refine .allI (.allI ?_)
  simpa only [pointCN, subst_data, Syn.shift, sh, Δ, GaussianEuclideanPointDistance.unit, GaussianCoefficientNameBounds.unit] using
    independent_observations (var 1) (var 0) (sh z) (sh R) (sh B) (sh j) guard

theorem actual_original_Mellin_improper_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (S (var 0) (var 1) (var 2) (succ (var 3)) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (regular _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinImproper
