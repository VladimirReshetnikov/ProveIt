import GowersSzemeredi.Proofs16RetiledRecurrence
import GowersSzemeredi.Proofs16RecurrenceThreshold
import GowersSzemeredi.Proofs16Lemma1Side

/-! Declarations of `Proofs16RetiledRecurrence` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- The base recurrence and signed tiling combine into proper product cells
with short final axes, retaining the frequency-times-step estimate. -/
theorem proper_retiled_product_recurrence {N k q m v : Nat} [NeZero N]
    (P : Box N k) (B I : ModAP N) (i : Fin k) (u : (ZMod N)ˣ)
    (hP : P.IsProper) (hI : I.IsProper)
    (hBstep : B.step = (↑u : ZMod N)) (hIstep : I.step = B.step)
    (hsub : (P.axis i).carrier ⊆ B.carrier) (hshort : 2 * B.length ≤ N)
    (hL : B.length ≤ I.length)
    (mu : Fin q → Point N k → ZMod N) (hmu : ∀ a, IsMultilinear (mu a))
    (hm : section16WidthThreshold k q ≤ m) (hmP : m ≤ P.width)
    (hv : 2 ≤ v)
    (hvscale : (v : Real) ^ 2 + 1 ≤ (m : Real) ^ section16RecurrenceExponent k q) :
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
      ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      (∀ j, (T j).carrier ⊆ P.carrier) ∧
      (∀ j, 0 < (J j).length ∧ (J j).length ≤ v) ∧
      ∀ a j x, x ∈ (T j).carrier →
        (centeredAbs (mu a x * (J j).step) : Real) ≤
          2 * (m : Real) ^ (-section16RecurrenceExponent k q) * N := by
  exact proper_retiled_product_of_recurrence P B I i u hI hBstep hIstep hsub hshort hL
    mu _ _ (proper_lemma_16_1 N k q m P hP mu hm hmP hmu) hv hvscale

/-- Frequency coverage converts the retiled base recurrence into linearity
on every final-axis cell. This allows the base and final input steps to differ. -/
theorem proper_retiled_product_linearity {N k q m v : Nat} [NeZero N]
    (P : Box N k) (B I : ModAP N) (i : Fin k) (u : (ZMod N)ˣ)
    (hP : P.IsProper) (hI : I.IsProper)
    (hBstep : B.step = (↑u : ZMod N)) (hIstep : I.step = B.step)
    (hsub : (P.axis i).carrier ⊆ B.carrier) (hshort : 2 * B.length ≤ N)
    (hL : B.length ≤ I.length)
    (mu : Fin q → Point N k → ZMod N) (hmu : ∀ a, IsMultilinear (mu a))
    (hm : section16WidthThreshold k q ≤ m) (hmP : m ≤ P.width)
    (hv : 2 ≤ v)
    (hvscale : (v : Real) ^ 2 + 1 ≤ (m : Real) ^ section16RecurrenceExponent k q)
    (K : Point N k → Finset (ZMod N)) (zeta : Real) (G : Finset (Point N k))
    (A : Point N k → Finset (ZMod N)) (f : Point N k → ZMod N → ZMod N)
    (hcover : ∀ x ∈ P.carrier, x ∈ G → ∀ r ∈ K x, ∃ a, r = mu a x)
    (hlinear : ∀ x ∈ G, ∀ J : ModAP N, J.length ≤ v → J.step ∈ bohr (K x) (zeta / v) →
      LinearOn (J.carrier ∩ A x) (f x))
    (hbudget : 2 * (m : Real) ^ (-section16RecurrenceExponent k q) ≤ zeta / v) :
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
      ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      ∀ j x, x ∈ (T j).carrier → x ∈ G → LinearOn ((J j).carrier ∩ A x) (f x) := by
  obtain ⟨M, S, T, J, hpart, hproper, hproduct, hTsub, hJlength, hsmall⟩ :=
    proper_retiled_product_recurrence P B I i u hP hI hBstep hIstep hsub hshort hL
      mu hmu hm hmP hv hvscale
  refine ⟨M, S, T, J, hpart, hproper, hproduct, ?_⟩
  intro j x hx hxG
  exact hlinear x hxG (J j) (hJlength j).2
    (product_recurrence_bohr_mem mu K x (J j).step _ zeta v
      (hcover x (hTsub j hx) hxG) (fun a => hsmall a j x hx) hbudget)

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- At the actual Section 16 radius, a target above one automatically
supplies the recurrence threshold, the length-minus-one margin, and the
Bohr budget needed by the retiled construction. -/
theorem section16_retiled_linearity_above_one {N k q m : Nat} [NeZero N]
    (hk : 1 ≤ k) (hm : 0 < m) (theta gamma : Real)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (P : Box N k) (B I : ModAP N) (i : Fin k) (u : (ZMod N)ˣ)
    (hP : P.IsProper) (hI : I.IsProper) (hmP : m ≤ P.width)
    (hBstep : B.step = (↑u : ZMod N)) (hIstep : I.step = B.step)
    (hsub : (P.axis i).carrier ⊆ B.carrier) (hshort : 2 * B.length ≤ N)
    (hL : B.length ≤ I.length)
    (mu : Fin q → Point N k → ZMod N) (hmu : ∀ a, IsMultilinear (mu a))
    (K : Point N k → Finset (ZMod N)) (G : Finset (Point N k))
    (A : Point N k → Finset (ZMod N)) (f : Point N k → ZMod N → ZMod N)
    (hcover : ∀ x ∈ P.carrier, x ∈ G → ∀ r ∈ K x, ∃ a, r = mu a x)
    (hlinear : ∀ x ∈ G, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K x) (section16Zeta theta gamma k / v) →
      LinearOn (J.carrier ∩ A x) (f x))
    (hlarge : 1 < (section16Zeta theta gamma k / 2) *
      Real.sqrt ((m : Real) ^ section16RecurrenceExponent k q)) :
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
      ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ (section16Zeta theta gamma k / 2) *
        Real.sqrt ((m : Real) ^ section16RecurrenceExponent k q) ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      ∀ j x, x ∈ (T j).carrier → x ∈ G → LinearOn ((J j).carrier ∩ A x) (f x) := by
  have hmr : (0 : Real) < m := by exact_mod_cast hm
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half k ht ht1 hg hg1
  obtain ⟨v, hv, hvwidth, hvscale, hvbudget⟩ := section16_short_scale_margin
    ((m : Real) ^ section16RecurrenceExponent k q) (section16Zeta theta gamma k)
    (Real.rpow_pos_of_pos hmr _) hz hzHalf hlarge
  have hthreshold := section16_threshold_of_large_width hk hm ht ht1 hg hg1 hlarge
  have hbudget : 2 * (m : Real) ^ (-section16RecurrenceExponent k q) ≤ section16Zeta theta gamma k / v := by
    simpa only [Real.rpow_neg hmr.le, div_eq_mul_inv] using hvbudget
  obtain ⟨M, S, T, J, hpart, hproper, hproduct, hlin⟩ := proper_retiled_product_linearity
    P B I i u hP hI hBstep hIstep hsub hshort hL mu hmu hthreshold hmP hv hvscale
    K (section16Zeta theta gamma k) G A f hcover
    (fun x hx J hJ hd => hlinear x hx v (by omega) J hJ hd) hbudget
  refine ⟨M, S, T, J, hpart, ?_, hproduct, hlin⟩
  exact fun j => ⟨(hproper j).1, hvwidth.trans (by exact_mod_cast (hproper j).2)⟩

end LeanProofs.GowersSzemeredi
