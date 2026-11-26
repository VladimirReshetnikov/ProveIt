import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasMesh
import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasQuotientProperness
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalDistanceOrder

/-!
# Read the periodic mesh estimate at fixed positive rational charts

A supplied primitive-recursive mesh schedule locates a fixed rational
point at a residue in every precision mesh. Mixed-clock chart properness
pays two dyadic units at each endpoint when the mesh observation is at
least as precise as the requested output. The grid itself pays one unit,
giving an envelope for equivalence of the two full quotient names.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasMeshConstancy

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesVignerasCyclicDerivative (LowerJet)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same distance_two_errors)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Q" => GaussianBarnesVignerasLogQuotient.nameF
local notation "cd" => GaussianBarnesVignerasIntegerPeriod.data
local notation "I" => GaussianBarnesVignerasIntegerPeriod.input
local notation "M" => GaussianBarnesVignerasIntegerPeriod.margin
local notation "Bnd" => GaussianBarnesVignerasIntegerPeriod.bound

def positive_chart (f : PR 2) (t : PTm 2) (a b : PTm n) : Fm PTm n :=
  GaussianNamedPositiveLogarithm.source f (I t a b) (M t a b) (Bnd t a b)

@[simp] theorem subst_positive_chart {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (t : PTm 2) (a b : PTm n) :
    (positive_chart f t a b).subst σ = positive_chart f t (Syn.subst σ a) (Syn.subst σ b) := by
  simp [positive_chart,GaussianBarnesVignerasIntegerPeriod.input,GaussianBarnesVignerasIntegerPeriod.margin,
    GaussianBarnesVignerasIntegerPeriod.bound]

def mesh_certificate (f g : PR 2) (t v : PTm 2) (J : LowerJet) (a b N i E p r y : PTm n) : Fm PTm n :=
  (le one N ⋏ (lt i N ⋏ le p r)) ⋏ (((N+i)*b ≐ a*N) ⋏
  (GaussianBarnesVignerasMesh.mesh_source f g t v J N E p r y ⋏
   ((positive_chart f t (N+i) N ⋏ positive_chart f t (N+zero) N) ⋏
   (crossEquivalent f f (I t a b) (I t (N+i) N) ⋏ crossEquivalent f f (I t (N+zero) N) (I t one one)))))

/-- At the requested precision the mesh code returns the period, residue, Taylor slack,
observation precision and jet data as a right-nested tuple. -/
def schedule (f g : PR 2) (t v s : PTm 2) (J : LowerJet) (a b x : PTm n) : Fm PTm n :=
  .all (let p := var 0
        let u := inst2 s p (Syn.shift x)
        let z := sndT u
        let w := sndT z
        let h := sndT w
        mesh_certificate f g t v J (Syn.shift a) (Syn.shift b) (fstT u) (fstT z) (fstT w) p (fstT h) (sndT h))

theorem mixed_close (f : PR 2) (x y p r : PTm n)
    (h : Γ ⊢[PRAAx] crossEquivalent f f x y) (hpr : Γ ⊢[PRAAx] le p r) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 f r y) two (unit p) :=
  distance_two_errors _ _ _ _ _ (unit_positive p) (unit_positive r) (unit_positive p) (le_refl _)
    (GaussianBalancedRadiusArithmetic.unit_monotone p r hpr)
    (cross_at f f x y p r h)

theorem fixed_distance (f g : PR 2) (t v : PTm 2) (J : LowerJet) (a b N i E p r y : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hA : Γ ⊢[PRAAx] positive_chart f t a b) (h₁ : Γ ⊢[PRAAx] positive_chart f t one one)
    (h : Γ ⊢[PRAAx] mesh_certificate f g t v J a b N i E p r y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (Q f) p (cd t a b)) (ap2 (Q f) p (cd t one one)) (num 5) (unit p) := by
  have hN := h.andE₁.andE₁
  have hi := h.andE₁.andE₂.andE₁
  have hpr := h.andE₁.andE₂.andE₂
  have c := h.andE₂.andE₂.andE₂
  have hni := le_trans hN (le_add_right N i)
  have hnz := le_trans hN (le_add_right N zero)
  let x := cd t a b
  let u := cd t (N+i) N
  let v₀ := cd t (N+zero) N
  let y₀ : PTm n := cd t one one
  have first : Γ ⊢[PRAAx] crossEquivalent (Q f) (Q f) x u :=
    GaussianBarnesVignerasQuotientProperness.proper f a b (N+i) N _ _ _ _ _ _
      ha hb hni hN hA c.andE₁.andE₁ h.andE₂.andE₁.eqSymm c.andE₂.andE₁
  have last : Γ ⊢[PRAAx] crossEquivalent (Q f) (Q f) v₀ y₀ :=
    GaussianBarnesVignerasQuotientProperness.proper f (N+zero) N one one _ _ _ _ _ _
      hnz hN (le_refl one) (le_refl one) c.andE₁.andE₂ h₁ (by ipra_ring) c.andE₂.andE₂
  have hfirst := mixed_close (Q f) x u p r first hpr
  have hlast := distance_symmetric _ _ _ _ (unit_positive p)
    (mixed_close (Q f) y₀ v₀ p r (cross_symm _ _ _ _ last) hpr)
  have middle := GaussianBarnesVignerasMesh.dyadic_distance f g t v J N E p r y i hN hi h.andE₂.andE₂.andE₁
  have together := distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) hfirst middle) hlast
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) together

theorem constant (f g : PR 2) (t v s : PTm 2) (J : LowerJet) (a b x : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hA : Γ ⊢[PRAAx] positive_chart f t a b) (h₁ : Γ ⊢[PRAAx] positive_chart f t one one)
    (h : Γ ⊢[PRAAx] schedule f g t v s J a b x) : Γ ⊢[PRAAx] crossEquivalent (Q f) (Q f) (cd t a b) (cd t one one) := by
  apply GaussianNameRingLaws.equivalent_of_envelope (Q f) (Q f) (cd t a b) (cd t one one) (num 5)
    (GaussianBarnesVignerasLogQuotient.regular f a b _ _ _ ha hb hA)
    (GaussianBarnesVignerasLogQuotient.regular f one one _ _ _ (le_refl one) (le_refl one) h₁)
  refine .allI ?_
  let A := Syn.shift a
  let B := Syn.shift b
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let u := inst2 s p (Syn.shift x)
  let z := sndT u
  let w := sndT z
  let k := sndT w
  have ap : Δ ⊢[PRAAx] le one A := by simpa [A,Δ,Fm.shift,Syn.shift,one] using ha.shift
  have bp : Δ ⊢[PRAAx] le one B := by simpa [B,Δ,Fm.shift,Syn.shift,one] using hb.shift
  have pA : Δ ⊢[PRAAx] positive_chart f t A B := by simpa [A,B,Δ,Fm.shift,Syn.shift] using hA.shift
  have p₁ : Δ ⊢[PRAAx] positive_chart f t one one := by simpa [Δ,Fm.shift,Syn.shift,one] using h₁.shift
  have cert : Δ ⊢[PRAAx] mesh_certificate f g t v J A B (fstT u) (fstT z) (fstT w) p (fstT k) (sndT k) := h.allOpen
  have obs := fixed_distance f g t v J A B (fstT u) (fstT z) (fstT w) p (fstT k) (sndT k) ap bp pA p₁ cert
  change Δ ⊢[PRAAx] distanceBounded (ap2 (Q f) p (Syn.shift (cd t a b)))
    (ap2 (Q f) p (Syn.shift (cd t one one))) (Syn.shift (num 5 : PTm n)) (unit p)
  simpa only [Syn.shift,GaussianBarnesVignerasIntegerPeriod.subst_data,one,
    LeanProofs.IPRA.PTm.subst_num,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,A,B] using obs

theorem actual_Barnes_candidate_quotient_constancy_from_meshes_closed (f g : PR 2) (t v s : PTm 2) (J : LowerJet) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (let a := var 0
       let b := var 1
       let x := var 2
       ((le one a ⋏ le one b) ⋏ (positive_chart f t a b ⋏ positive_chart f t one one)) ⟶
        schedule f g t v s J a b x ⟶ crossEquivalent (Q f) (Q f) (cd t a b) (cd t one one)) :=
  closeUniv 3 (.impI (.impI (constant f g t v s J _ _ _ Prf.hyp1.andE₁.andE₁ Prf.hyp1.andE₁.andE₂
    Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasMeshConstancy
