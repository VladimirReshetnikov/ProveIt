import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalValue
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductFamilyCongruence
import IPRADerivations.Analysis.Exponential.GaussianExponentialRadiusIndependence
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaAdjacentCutoff

/-!
# Disk independence of the original finite Barnes product

Each literal factor at a fixed index has one polynomial multiplier
and one original exponential argument. Two certified disk radii
select different exponential clocks for that argument. Rowwise
equivalence carries through the original finite product and its
unchanged original prefactor at every common cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteRadius

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalHead (source)
open GaussianBarnesCanonicalValue (prefixF)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedFiniteProductFamilyCongruence (equalRows family_product_cross)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFactor.nameF
local notation "fd" => GaussianBarnesCanonicalFactor.data
local notation "E" => GaussianBarnesCanonicalFactor.exponentialF
local notation "ed" => GaussianBarnesCanonicalFactor.exponentialData
local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "pd" => GaussianBarnesCanonicalPrefactor.data
local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "hd" => GaussianBarnesCanonicalHead.data
local notation "params" => GaussianBarnesCanonicalHead.parameters
local notation "body" => GaussianBarnesCanonicalHead.body

theorem factor_cross (z R S B k : PTm n)
    (hR : Γ ⊢[PRAAx] GaussianBarnesCanonicalFactor.source z R B k)
    (hS : Γ ⊢[PRAAx] GaussianBarnesCanonicalFactor.source z S B k) :
    Γ ⊢[PRAAx] crossEquivalent F F (fd z R B k) (fd z S B k) := by
  let w := GaussianBarnesCanonicalFactor.powerValue z B k
  let c := GaussianBarnesCanonicalFactor.correction z B k
  let A := GaussianBarnesCanonicalFactor.exponentRadius R
  let C := GaussianBarnesCanonicalFactor.exponentRadius S
  have left := GaussianBarnesCanonicalFactor.exponential_input z R B k hR
  have right := GaussianBarnesCanonicalFactor.exponential_input z S B k hS
  have e := GaussianExponentialRadiusIndependence.same_input_cross constantF A C c left right
  have reg := constant_regular (Γ := Γ) w
  exact GaussianGammaAdjacentCutoff.multiply_cross constantF constantF E E w w (ed z R B k) (ed z S B k)
    reg reg (GaussianRadiusExponentialName.name_regular constantF A c left)
    (GaussianRadiusExponentialName.name_regular constantF C c right) (cross_refl constantF w reg) e

theorem rows_cross (z R S B N r : PTm n) (hR : Γ ⊢[PRAAx] source z R B) (hS : Γ ⊢[PRAAx] source z S B) :
    Γ ⊢[PRAAx] equalRows F F body body r (params z R B N) (params z S B N) := by
  refine .allI (.impI ?_)
  let sh (x : PTm n) := Syn.shift x
  let Δ := lt (var 0) (sh r) :: Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  let k := succ (sh N+i)
  have l : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hR.shift.wk
  have r' : Δ ⊢[PRAAx] source (sh z) (sh S) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hS.shift.wk
  have e := factor_cross (sh z) (sh R) (sh S) (sh B) k
    (.andI l.andE₁ (.andI (zero_lt_succ _) l.andE₂))
    (.andI r'.andE₁ (.andI (zero_lt_succ _) r'.andE₂))
  have dR := GaussianBarnesCanonicalHead.body_at (Γ := Δ) i (sh z) (sh R) (sh B) (sh N)
  have dS := GaussianBarnesCanonicalHead.body_at (Γ := Δ) i (sh z) (sh S) (sh B) (sh N)
  simpa only [equalRows,GaussianBarnesCanonicalHead.subst_parameters,Syn.shift,Δ,sh,i] using
    GaussianGammaCompactCutoffAlignment.cross_data_congr F F _ _ _ _ dR.eqSymm dS.eqSymm e

theorem segment_cross (z R S B N r : PTm n)
    (hR : Γ ⊢[PRAAx] source z R B) (hS : Γ ⊢[PRAAx] source z S B) :
    Γ ⊢[PRAAx] crossEquivalent H H (hd z R B N r) (hd z S B N r) :=
  family_product_cross F F body body r (params z R B N) (params z S B N)
    (GaussianBarnesCanonicalHead.rows_regular z R B N r hR)
    (GaussianBarnesCanonicalHead.rows_regular z S B N r hS)
    (rows_cross z R S B N r hR hS)

def prefixData (z R B r : PTm n) : PTm n := multiplyData P H (pd z B) (hd z R B zero r)

@[simp] theorem subst_prefixData {m : ℕ} (σ : Fin n → PTm m) (z R B r : PTm n) :
    Syn.subst σ (prefixData z R B r) =
      prefixData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) := by
  simp [prefixData]

theorem prefix_cross (z R S B r : PTm n)
    (hR : Γ ⊢[PRAAx] source z R B) (hS : Γ ⊢[PRAAx] source z S B) :
    Γ ⊢[PRAAx] crossEquivalent prefixF prefixF (prefixData z R B r) (prefixData z S B r) := by
  have hp := GaussianBarnesCanonicalPrefactor.regular (Γ := Γ) z B
  exact GaussianGammaAdjacentCutoff.multiply_cross P P H H (pd z B) (pd z B) (hd z R B zero r) (hd z S B zero r)
    hp hp (GaussianBarnesCanonicalHead.regular z R B zero r hR) (GaussianBarnesCanonicalHead.regular z S B zero r hS)
    (cross_refl P (pd z B) hp) (segment_cross z R S B zero r hR hS)

theorem actual_Barnes_factor_radius_independence_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (GaussianBarnesCanonicalFactor.source (var 0) (var 1) (var 3) (var 4) ⟶
        GaussianBarnesCanonicalFactor.source (var 0) (var 2) (var 3) (var 4) ⟶
        crossEquivalent F F (fd (var 0) (var 1) (var 3) (var 4)) (fd (var 0) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (factor_cross _ _ _ _ _ Prf.hyp0.wk Prf.hyp0)))

theorem actual_Barnes_segment_radius_independence_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 1) (var 3) ⟶ source (var 0) (var 2) (var 3) ⟶
        crossEquivalent H H (hd (var 0) (var 1) (var 3) (var 4) (var 5))
          (hd (var 0) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (.impI (segment_cross _ _ _ _ _ _ Prf.hyp0.wk Prf.hyp0)))

theorem actual_original_Barnes_finite_product_radius_independence_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 1) (var 3) ⟶ source (var 0) (var 2) (var 3) ⟶
        crossEquivalent prefixF prefixF (prefixData (var 0) (var 1) (var 3) (var 4))
          (prefixData (var 0) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (prefix_cross _ _ _ _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteRadius
