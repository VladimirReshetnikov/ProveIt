import ZFCinPA.ValidatorNativeGicSlots254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA
open ValidatorEnvironmentLabels254 ValidatorEnvironmentVacuity254
open ValidatorProvability254 ValidatorQuantifierCore254
open ValidatorNativeGic254 ValidatorNativeGicSlots254
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.ValidatorNativeGicSlots254.encode_gic_support_slots
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGicSlots254.encode_gic_coverage_slots
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGicSlots254.pad_even
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGicSlots254.even_avoids_odd_env
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGicSlots254.even_free_avoids_odd_env
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGicSlots254.even_stream_avoid
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGicSlots254.padded_matrix_resources
#print axioms LeanProofs.ZFCinPA.ValidatorNativeGicSlots254.cProv_paddedGic_odd

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example {K : V} (hK : IsSemiformula ℒₛₑₜ 2 K) (F t : V) :
    encode F ((t+6)∷(t+4)∷(t+2)∷t∷0) (t+8)
      (subst ℒₛₑₜ ((gicSubst01Const : ℕ) : V) K)=
        encode F ((t+6)∷(t+4)∷0) (t+8) K := encode_gic_support_slots hK F t
example {K : V} (hK : IsSemiformula ℒₛₑₜ 2 K) (F t : V) :
    encode F ((t+6)∷(t+4)∷(t+2)∷t∷0) (t+8)
      (subst ℒₛₑₜ ((gicSubst10Const : ℕ) : V) K)=
        encode F ((t+4)∷(t+6)∷0) (t+8) K := encode_gic_coverage_slots hK F t
example (p : V) : pad p % 2=0 := pad_even p
example {z F : V} (hz : z % 2=0) (hF : OddEnv F) : Avoid z F := even_avoids_odd_env hz hF
example {z F : V} (hz : z % 2=0) (hF : OddEnv F) : FreeAvoid z F := even_free_avoids_odd_env hz hF
example {z s : V} (hz : z % 2=0) (hs : s % 2=1) : StreamAvoid z s := even_stream_avoid hz hs

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]
example {K F a b s : V} (hK : IsSemiformula ℒₛₑₜ 2 K) (hF : OddEnv F)
    (ha : a % 2=1) (hb : b % 2=1) (hs : s % 2=1) :
    let P := encode F (a∷b∷0) s K
    Vac (pad P) P ∧ Vac (pad P) (pad P) ∧ pad P≠a ∧ pad P≠b :=
  padded_matrix_resources hK hF ha hb hs
example {K F a b s : V} (hK : IsSemiformula ℒₛₑₜ 2 K) (hF : OddEnv F)
    (ha : a % 2=1) (hb : b % 2=1) (hs : s % 2=1) :
    let P := encode F (a∷b∷0) s K
    CProv (internalGic a b (pad P) (pad P)) := cProv_paddedGic_odd hK hF ha hb hs
example {K a b s : V} (hK : IsSemiformula ℒₛₑₜ 2 K)
    (ha : a % 2=1) (hb : b % 2=1) (hs : s % 2=1) :
    Vac (pad (encode 0 (a∷b∷0) s K)) (encode 0 (a∷b∷0) s K) :=
  (padded_matrix_resources hK (show OddEnv (0 : V) by simp [OddEnv]) ha hb hs).1
example {K F : V} (hK : IsSemiformula ℒₛₑₜ 2 K) (hF : OddEnv F) (x y z : V) :
    let P := encode F ((2*x+1)∷(2*y+1)∷0) (2*z+1) K
    CProv (internalGic (2*x+1) (2*y+1) (pad P) (pad P)) :=
  cProv_paddedGic_odd hK hF (by simp) (by simp) (by simp)
