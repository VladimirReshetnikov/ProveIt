import GowersSzemeredi.Proofs16RelationWordExactness

/-! One endpoint radius and rank budget for every compatible word up to a
fixed length. The radius loses a fixed power of the relation image bound. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A common radius for words of at most `k+1` triples. -/
def boundedImageWordRadius (r : Real) (M k : Nat) : Real :=
  r/((9 : Real)^(k+1)*(M^(2*k+1) : Nat))

theorem boundedImageWordRadius_pos {r : Real} (hr : 0 < r) {M : Nat} (hM : 0 < M)
    (k : Nat) : 0 < boundedImageWordRadius r M k := by
  unfold boundedImageWordRadius
  positivity

theorem boundedImageWordRadius_le {r : Real} (hr : 0 ≤ r) {M : Nat} (hM : 0 < M)
    (k j : Nat) (hj : j ≤ k) :
    boundedImageWordRadius r M k ≤ (r/(9 : Real)^(j+1))/(M^(2*j+1) : Nat) := by
  have hMp : (0 : Real) < (M^(2*j+1) : Nat) := by positivity
  have hpowM : M^(2*j+1) ≤ M^(2*k+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hden : (9 : Real)^(j+1)*(M^(2*j+1) : Nat) ≤
      (9 : Real)^(k+1)*(M^(2*k+1) : Nat) := by
    have hpow9 : (9 : Real)^(j+1) ≤ (9 : Real)^(k+1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact mul_le_mul hpow9 (by exact_mod_cast hpowM) (by positivity) (by positivity)
  rw [div_div]
  exact div_le_div_of_nonneg_left hr (by positivity) hden

/-- Uniform exactness and rank for all bounded-length relation words. -/
theorem coherent_relation_word_exact_uniform {N ell k M : Nat} [NeZero N] [Fact N.Prime]
    (A B : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N)
    (F : ZMod N → ZMod N → ZMod N) (R : ZMod N → ZMod N → ZMod N → ZMod N → Prop)
    {r : Real} (hr : 0 ≤ r) (hM : 0 < M)
    (htheta : ∀ i, IsFreimanLinearOn A (theta i))
    (hF : ∀ x ∈ A, IsFreimanLinearOn (freimanFrequencyBohr B theta r x) (F x) ∧ F x 0 = 0)
    (hR : ∀ a b c d, R a b c d → ColumnQuadImageRelation
      (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F r M a b c d)
    (hMN : M^(2*k+1) < N)
    (a : ZMod N) (as : List (ZMod N)) (w : ColumnWord N (a::as).length)
    (ha : ∀ x ∈ a::as, x ∈ A) (hw : w ∈ relationWordRepresentations A R (a::as))
    (hlen : as.length ≤ k) :
    (relationWordEndpointSpectrum (fun u => B ∪ Finset.univ.image (fun j => theta j u))
      (a::as) w).card ≤ 4*(k+1)*(B.card+ell) ∧
    ∀ y ∈ bohr (relationWordEndpointSpectrum
      (fun u => B ∪ Finset.univ.image (fun j => theta j u)) (a::as) w)
      (boundedImageWordRadius r M k),
      columnAnchorEval (fun x => F x y) (a::as) = columnWordEval (fun x => F x y) w := by
  constructor
  · have hT : ∀ u ∈ A, (B ∪ Finset.univ.image (fun j => theta j u)).card ≤ B.card+ell := by
      intro u _
      exact (Finset.card_union_le B (Finset.univ.image (fun j => theta j u))).trans (Nat.add_le_add_left
        (by simpa using (Finset.card_image_le :
          (Finset.univ.image (fun j => theta j u)).card ≤ (Finset.univ : Finset (Fin ell)).card)) _)
    have hs := relationWordEndpointSpectrum_card_le A _ (a::as) w ha
      (relationWordRepresentations_spec A R (a::as) w hw).1 hT
    apply hs.trans
    simp only [List.length_cons]
    gcongr
  · have hpow : M^(2*as.length+1) ≤ M^(2*k+1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hexact := coherent_relation_word_exact A B theta F R hr M htheta hF hR a as w ha hw
      (hpow.trans_lt hMN)
    intro y hy
    apply hexact y
    apply bohr_mono_radius _ _ hy
    simpa only [List.length_cons] using boundedImageWordRadius_le hr hM k as.length hlen

end LeanProofs.GowersSzemeredi
