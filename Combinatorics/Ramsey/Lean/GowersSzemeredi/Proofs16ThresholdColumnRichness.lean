import GowersSzemeredi.Proofs16ThresholdPopularAnchors

/-! Hereditary mixed-quadruple richness above a specified subset density.
The half factor is retained exactly in the later counting arguments. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def ThresholdColumnRichness {N : Nat} [NeZero N] (A : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r beta eta : Real) : Prop :=
  ∀ U V : Finset (ZMod N), U ⊆ A → V ⊆ A →
    ∀ beta1 beta2 : Real, beta ≤ beta1 → beta ≤ beta2 →
      beta1*N ≤ (U.card : Real) → beta2*N ≤ (V.card : Real) →
      (beta1*beta2*eta)^2*(N : Real)^3/2 ≤ ((mixedExactColumnQuadruples U V T L r).card : Real)

theorem ThresholdColumnRichness.card_bound {N : Nat} [NeZero N]
    {A : Finset (ZMod N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {r beta eta : Real}
    (h : ThresholdColumnRichness A T L r beta eta) {C : Finset (ZMod N)}
    (hCA : C ⊆ A) (hC : beta*N ≤ (C.card : Real)) :
    (eta^2/2)*(C.card : Real)^4 ≤ N*((exactColumnQuadruples C T L r).card : Real) := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hb : beta ≤ (C.card : Real)/N := (le_div_iff₀ hn).mpr hC
  have hm := h C C hCA hCA ((C.card : Real)/N) ((C.card : Real)/N) hb hb
    (by rw [div_mul_cancel₀ _ hn.ne']) (by rw [div_mul_cancel₀ _ hn.ne'])
  rw [mixedExactColumnQuadruples_self] at hm
  calc _ = N*((((C.card : Real)/N)*((C.card : Real)/N)*eta)^2*(N : Real)^3/2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hm hn.le

theorem ThresholdColumnRichness.popular_anchors {N : Nat} [NeZero N]
    {A : Finset (ZMod N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {r beta eta b : Real}
    (h : ThresholdColumnRichness A T L r beta eta) (hb : 0 < b) (he : 0 < eta)
    (hA : b*N ≤ (A.card : Real)) (hcut : beta ≤ b/2) :
    b*N/2 ≤ ((popularColumnAnchors A T L r (eta^2*b^3/32)).card : Real) := by
  have hm := popular_column_anchors_dense_above A T L r hb (by positivity : 0 < eta^2/2) hA
    (fun C hCA hC => h.card_bound hCA ((by
      have hc := mul_le_mul_of_nonneg_right hcut (Nat.cast_nonneg N : (0 : Real) ≤ N)
      linarith : beta*N ≤ b*N/2).trans hC))
  have heq : (eta^2/2)*b^3/16 = eta^2*b^3/32 := by ring
  simpa only [heq] using hm

end LeanProofs.GowersSzemeredi
