import ZFCinPA.ValidatorEnvironmentSubstitution254
import ZFCinPA.NativeGicDelta1
import ZFCinPA.ValidatorNativeGic254
import ZFCinPA.ValidatorEnvironmentVacuity254

set_option autoImplicit false
noncomputable section

/-!
The two native GIC matrix slot orders, for arbitrary internal matrices, and
parity-separated vacancy for the literal validator G instance. Matrix labels
are chosen before padding its code. This does not identify the complete
encoded native body with that literal instance or close the schema recognizer.
-/
namespace LeanProofs.ZFCinPA.ValidatorNativeGicSlots254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254
open ValidatorEnvironmentLabels254 ValidatorEnvironmentSubstitution254
open ValidatorEnvironmentVacuity254 ValidatorNativeGic254
open ValidatorProvability254 ValidatorQuantifierCore254
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private lemma encode_subst01 {K : V} (hK : IsSemiformula ℒₛₑₜ 2 K)
    (F B s : V) :
    encode F B s (subst ℒₛₑₜ ((gicSubst01Const : ℕ) : V) K) =
      encode F (B.[0]∷B.[1]∷0) s K := by
  rw [val_gicSubst01Const]
  simpa using encode_subst_pair hK
    (Bootstrapping.Semiterm.bvar (V := V) (L := ℒₛₑₜ) (0 : Fin 4)).isSemiterm
    (Bootstrapping.Semiterm.bvar (V := V) (L := ℒₛₑₜ) (1 : Fin 4)).isSemiterm F B s

private lemma encode_subst10 {K : V} (hK : IsSemiformula ℒₛₑₜ 2 K)
    (F B s : V) :
    encode F B s (subst ℒₛₑₜ ((gicSubst10Const : ℕ) : V) K) =
      encode F (B.[1]∷B.[0]∷0) s K := by
  rw [val_gicSubst10Const]
  simpa using encode_subst_pair hK
    (Bootstrapping.Semiterm.bvar (V := V) (L := ℒₛₑₜ) (1 : Fin 4)).isSemiterm
    (Bootstrapping.Semiterm.bvar (V := V) (L := ℒₛₑₜ) (0 : Fin 4)).isSemiterm F B s

/-- Support uses the innermost variable first, then the next variable. -/
theorem encode_gic_support_slots {K : V} (hK : IsSemiformula ℒₛₑₜ 2 K) (F t : V) :
    encode F ((t+6)∷(t+4)∷(t+2)∷t∷0) (t+8)
      (subst ℒₛₑₜ ((gicSubst01Const : ℕ) : V) K) =
        encode F ((t+6)∷(t+4)∷0) (t+8) K := by
  simpa using encode_subst01 hK F ((t+6)∷(t+4)∷(t+2)∷t∷0) (t+8)

/-- Coverage reverses those slots. The internal matrix is unchanged. -/
theorem encode_gic_coverage_slots {K : V} (hK : IsSemiformula ℒₛₑₜ 2 K) (F t : V) :
    encode F ((t+6)∷(t+4)∷(t+2)∷t∷0) (t+8)
      (subst ℒₛₑₜ ((gicSubst10Const : ℕ) : V) K) =
        encode F ((t+4)∷(t+6)∷0) (t+8) K := by
  simpa using encode_subst10 hK F ((t+6)∷(t+4)∷(t+2)∷t∷0) (t+8)

/-- Every stored free label is odd; the encoder's fallback label is already 1. -/
def OddEnv (F : V) : Prop := ∀ i<len F, F.[i] % 2=1

lemma pad_even (p : V) : pad p % 2=0 := by
  have hp : pad p=2*(2*cantor (wim p 1) 1) := by
    unfold pad wim tagged
    ring
  rw [hp]
  simp

private lemma even_ne_odd {z x : V} (hz : z % 2=0) (hx : x % 2=1) : z≠x := by
  intro h
  have hm := congrArg (fun q : V => q % 2) h
  simp [hz,hx] at hm

lemma even_avoids_odd_env {z F : V} (hz : z % 2=0) (hF : OddEnv F) : Avoid z F := by
  intro i hi
  exact even_ne_odd hz (hF i hi)

lemma even_free_avoids_odd_env {z F : V} (hz : z % 2=0) (hF : OddEnv F) :
    FreeAvoid z F :=
  ⟨even_ne_odd hz (by simp),even_avoids_odd_env hz hF⟩

lemma even_stream_avoid {z s : V} (hz : z % 2=0) (hs : s % 2=1) :
    StreamAvoid z s := by
  intro k
  apply even_ne_odd hz
  simpa using hs

/-- Padding is chosen after the encoded matrix; parity supplies vacancy without
making the original label stream depend on the resulting code. -/
theorem padded_matrix_resources [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {K F a b s : V}
    (hK : IsSemiformula ℒₛₑₜ 2 K) (hF : OddEnv F)
    (ha : a % 2=1) (hb : b % 2=1) (hs : s % 2=1) :
    let P := encode F (a∷b∷0) s K
    let c := pad P
    Vac c P ∧ Vac c (pad P) ∧ c≠a ∧ c≠b := by
  let P := encode F (a∷b∷0) s K
  change Vac (pad P) P ∧ Vac (pad P) (pad P) ∧ pad P≠a ∧ pad P≠b
  have hc := pad_even P
  have hca := even_ne_odd hc ha
  have hcb := even_ne_odd hc hb
  have hB : Avoid (pad P) (a∷b∷0) :=
    avoid_cons (avoid_cons (avoid_nil (pad P)) hcb) hca
  have hP : Vac (pad P) P :=
    encode_vac hK F (a∷b∷0) s (pad P) (by simp [one_add_one_eq_two])
      (even_free_avoids_odd_env hc hF) hB (even_stream_avoid hc hs)
  exact ⟨hP,vac_imp (vac_imp hP (vac_falsum (pad P))) (vac_falsum (pad P)),hca,hcb⟩

/-- The literal validator instance, with the same fixed matrix and padded code.
The complete native GIC body encoding and its universal closure are separate. -/
theorem cProv_paddedGic_odd [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {K F a b s : V}
    (hK : IsSemiformula ℒₛₑₜ 2 K) (hF : OddEnv F)
    (ha : a % 2=1) (hb : b % 2=1) (hs : s % 2=1) :
    let P := encode F (a∷b∷0) s K
    CProv (internalGic a b (pad P) (pad P)) := by
  have h := padded_matrix_resources hK hF ha hb hs
  exact cProv_internalGic a b _ h.2.2.1 h.2.2.2

end LeanProofs.ZFCinPA.ValidatorNativeGicSlots254
