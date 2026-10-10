import GowersSzemeredi.Proofs16RetiledLinearityBound
import GowersSzemeredi.Proofs16PolynomialRecurrenceComparison

/-! The reciprocal-polynomial recurrence bound survives final-axis tiling.

For a finite family covering the relevant frequencies, the recurrence
partition gives proper product cells on which the final-coordinate function
is linear. The minimum width is `(zeta / 2) * sqrt (m ^ epsilon)`, including
integer rounding and the length-minus-one margin needed by the tiling.

The dimension constants and eventual crossover remain existential. Frequency
coverage and local linearity are explicit hypotheses; this does not supply
the missing higher-dimensional structural theorem.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A recurrence partition at scale `s` and error `2 / s` gives linear
final-axis cells of width at least `(zeta / 2) * sqrt s`. -/
theorem retiled_linearity_of_recurrence_scale {N k q : Nat} [NeZero N]
    (P : Box N k) (B I : ModAP N) (i : Fin k) (u : (ZMod N)ˣ)
    (hI : I.IsProper)
    (hBstep : B.step = (↑u : ZMod N)) (hIstep : I.step = B.step)
    (hsub : (P.axis i).carrier ⊆ B.carrier) (hshort : 2 * B.length ≤ N)
    (hL : B.length ≤ I.length)
    (mu : Fin q → Point N k → ZMod N) (s zeta : Real) (hs : 0 < s)
    (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    (hrec : ∃ M : Nat, ∃ R : Fin M → Box N k,
      IsBoxPartition R P ∧ (∀ j, (R j).IsProper) ∧
      (∀ j, s ≤ (R j).width) ∧
      ∀ a j x, x ∈ (R j).carrier →
        (centeredAbs (mu a x * (R j).commonDiff) : Real) ≤ (2 / s) * N)
    (K : Point N k → Finset (ZMod N)) (G : Finset (Point N k))
    (A : Point N k → Finset (ZMod N)) (f : Point N k → ZMod N → ZMod N)
    (hcover : ∀ x ∈ P.carrier, x ∈ G → ∀ r ∈ K x, ∃ a, r = mu a x)
    (hlinear : ∀ x ∈ G, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K x) (zeta / v) → LinearOn (J.carrier ∩ A x) (f x))
    (hlarge : 1 < (zeta / 2) * Real.sqrt s) :
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
      ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ (zeta / 2) * Real.sqrt s ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      ∀ j x, x ∈ (T j).carrier → x ∈ G → LinearOn ((J j).carrier ∩ A x) (f x) := by
  obtain ⟨v, hv, hvwidth, hvscale, hvbudget⟩ :=
    section16_short_scale_margin s zeta hs hz hzHalf hlarge
  obtain ⟨M, S, T, J, hpart, hproper, hproduct, hTsub, hJlength, hsmall⟩ :=
    proper_retiled_product_of_recurrence P B I i u hI hBstep hIstep hsub hshort hL
      mu s (2 / s) hrec hv hvscale
  refine ⟨M, S, T, J, hpart, ?_, hproduct, ?_⟩
  · intro j
    exact ⟨(hproper j).1, hvwidth.trans (by exact_mod_cast (hproper j).2)⟩
  · intro j x hx hxG
    exact hlinear x hxG v (by omega) (J j) (hJlength j).2
      (product_recurrence_bohr_mem mu K x (J j).step _ zeta v
        (hcover x (hTsub j hx) hxG) (fun a => hsmall a j x hx) hvbudget)

/-- The statement of `exists_polynomial_retiled_linearity_profile` at fixed constants. -/
def PolynomialRetiledLinearityProfileAt (k : Nat) (K p : Nat) : Prop :=
  ∀ q : Nat,
      Section16RetiledLinearityBound k q (section16SimultaneousExponent k p q)
        (section16SimultaneousThreshold k K p q)

/-- `exists_polynomial_retiled_linearity_profile` at the constants of its input. -/
theorem polynomialRetiledLinearityProfileAt_of (k : Nat) {K p : Nat} (hK : 2 ≤ K) (hp : 0 < p)
    (hrec : PolynomialSection16RecurrenceProfileAt k K p) : PolynomialRetiledLinearityProfileAt k K p := by
  unfold PolynomialRetiledLinearityProfileAt
  intro q N m _ P B I i u hP hI hBstep hIstep hsub hshort hL mu hmu hm hmP
    F G A f zeta hz hzHalf hcover hlinear hlarge
  have hm0 : 0 < m := (pow_pos (Nat.mul_pos (by omega : 0 < K) (by omega)) _).trans_le hm
  have hmR : (0 : Real) < m := by exact_mod_cast hm0
  apply retiled_linearity_of_recurrence_scale P B I i u hI hBstep hIstep hsub hshort hL
    mu _ zeta (Real.rpow_pos_of_pos hmR _) hz hzHalf _ F G A f hcover hlinear hlarge
  simpa only [Real.rpow_neg hmR.le, div_eq_mul_inv] using
    hrec N q m P hP mu hmu hm hmP

/-- The new simultaneous recurrence supplies the retiled linearity bound
with reciprocal-polynomial dependence on the number of covering phases. -/
theorem exists_polynomial_retiled_linearity_profile (k : Nat) :
    ∃ K p : Nat, 2 ≤ K ∧ 0 < p ∧ ∀ q : Nat,
      Section16RetiledLinearityBound k q (section16SimultaneousExponent k p q)
        (section16SimultaneousThreshold k K p q) := by
  obtain ⟨K, p, hK, hp, hrec⟩ := exists_polynomial_section16_recurrence_profile k
  exact ⟨K, p, hK, hp, polynomialRetiledLinearityProfileAt_of k hK hp hrec⟩

/-- Raising the input threshold preserves a retiled linearity bound. -/
theorem Section16RetiledLinearityBound.mono_threshold {k q t₁ t₂ : Nat} {epsilon : Real}
    (h : Section16RetiledLinearityBound k q epsilon t₁) (ht : t₁ ≤ t₂) :
    Section16RetiledLinearityBound k q epsilon t₂ := by
  intro N m _ P B I i u hP hI hBstep hIstep hsub hshort hL mu hmu hm hmP
  exact h N m P B I i u hP hI hBstep hIstep hsub hshort hL mu hmu (ht.trans hm) hmP

/-- For all sufficiently large phase families, the larger recurrence
exponent also reaches the retiled linearity conclusion under the old threshold. -/
theorem exists_eventually_stronger_retiled_linearity (k : Nat) :
    ∃ K p q0 : Nat, 2 ≤ K ∧ 0 < p ∧ ∀ q : Nat, q0 ≤ q →
      section16RecurrenceExponent k q < section16SimultaneousExponent k p q ∧
      Section16RetiledLinearityBound k q (section16SimultaneousExponent k p q)
        (section16WidthThreshold k q) := by
  obtain ⟨K, p, hK, hp, hretile⟩ := exists_polynomial_retiled_linearity_profile k
  obtain ⟨q0, hq0⟩ := Filter.eventually_atTop.mp
    ((eventually_section16RecurrenceExponent_lt_simultaneous k p hp).and
      (eventually_section16SimultaneousThreshold_le_old k K p))
  exact ⟨K, p, q0, hK, hp, fun q hq =>
    ⟨(hq0 q hq).1, (hretile q).mono_threshold (hq0 q hq).2⟩⟩

end LeanProofs.GowersSzemeredi
