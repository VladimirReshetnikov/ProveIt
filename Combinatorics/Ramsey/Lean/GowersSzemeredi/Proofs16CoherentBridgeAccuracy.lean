import GowersSzemeredi.Proofs16CoherentRadiusProfile

/-! A concrete accuracy schedule pays for quasirandom weak transitivity
at any prescribed positive bridge density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def coherentBridgeAccuracy (H m k : Nat) (eta : Real) : Real :=
  min ((1/(H : Real)^m)/2) ((1/(H : Real)^m)*eta/(8*((2*H : Nat) : Real)^k))

theorem coherentBridgeAccuracy_pos (H m k : Nat) [NeZero H] {eta : Real} (he : 0 < eta) :
    0 < coherentBridgeAccuracy H m k eta := by
  have hH : (0 : Real) < H := by exact_mod_cast NeZero.pos H
  unfold coherentBridgeAccuracy
  apply lt_min <;> push_cast <;> positivity

theorem coherentBridgeAccuracy_le_half (H m k : Nat) (eta : Real) :
    coherentBridgeAccuracy H m k eta ≤ (1/(H : Real)^m)/2 := min_le_left _ _

theorem coherentBridgeAccuracy_small (H m k : Nat) [NeZero H] {eta : Real} (he : 0 < eta) :
    4*((2*H : Nat) : Real)^k*coherentBridgeAccuracy H m k eta < (1/(H : Real)^m)*eta := by
  have hH : (0 : Real) < H := by exact_mod_cast NeZero.pos H
  have hp : (0 : Real) < ((2*H : Nat) : Real)^k := by push_cast; positivity
  have hb : 0 < (1/(H : Real)^m)*eta := by positivity
  have h := (le_div_iff₀ (by positivity : (0 : Real) < 8*((2*H : Nat) : Real)^k)).mp
    (show coherentBridgeAccuracy H m k eta ≤ (1/(H : Real)^m)*eta/(8*((2*H : Nat) : Real)^k) from min_le_right _ _)
  nlinarith only [h,hb]

end LeanProofs.GowersSzemeredi
