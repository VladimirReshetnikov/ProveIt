import GowersSzemeredi.Proofs16SeparatedRespect
import GowersSzemeredi.Proofs07AdditiveRestriction

/-! From a separated family to a Freiman homomorphism on a dense set: the
`ℤ/N` polynomial form of the Theorem 2.26 step in Milićević's Lemma 9.2.

* `phiAdditiveCount_ge_of_respected`: tuples `(x, x′, a, b)` with
  `f(x+a) − f(x′+a) = f(x+b) − f(x′+b)` map at most `N`-to-one onto the
  `f`-additive quadruples `(x+a, x′+b, x′+a, x+b)`. So `κN⁴` of them give
  `κN³ ≤ phiAdditiveCount univ f`.
* `freiman_of_separated`: let `c N²|Ω|` triples separate `f` and `g`. Then
  `f` is a Freiman `8`-homomorphism on some `B` of size at least
  `2^(-1882)·c^4656·N`. This uses `respected_quadruples_of_separated` and
  Gowers's Corollary 7.6 (`corollary_7_6_holds`, with `γ = c⁴` and
  `α = 1`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem phiAdditiveCount_ge_of_respected {N : Nat} [NeZero N] (f : ZMod N → ZMod N) {κ : Real}
    (h : κ * (N : Real) ^ 4 ≤ ((Finset.univ : Finset (ZMod N × ZMod N × ZMod N × ZMod N)).filter
      fun t => f (t.1 + t.2.2.1) - f (t.2.1 + t.2.2.1) =
        f (t.1 + t.2.2.2) - f (t.2.1 + t.2.2.2)).card) :
    κ * (N : Real) ^ 3 ≤ phiAdditiveCount Finset.univ f := by
  let R := (Finset.univ : Finset (ZMod N × ZMod N × ZMod N × ZMod N)).filter fun t =>
    f (t.1 + t.2.2.1) - f (t.2.1 + t.2.2.1) = f (t.1 + t.2.2.2) - f (t.2.1 + t.2.2.2)
  let φ : ZMod N × ZMod N × ZMod N × ZMod N → (Fin 4 → ZMod N) := fun t =>
    ![t.1 + t.2.2.1, t.2.1 + t.2.2.2, t.2.1 + t.2.2.1, t.1 + t.2.2.2]
  have himg : R.image φ ⊆ (Finset.univ : Finset (Fin 4 → ZMod N)).filter
      (IsPhiAdditive Finset.univ f) := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
    have he := (Finset.mem_filter.mp ht).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ => Finset.mem_univ _, ?_, ?_⟩
    · simp only [IsAdditiveQuadruple, φ, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      ring
    · simp only [φ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      linear_combination he
  have hfib : ∀ q ∈ R.image φ, (R.filter fun t => φ t = q).card ≤ N := by
    intro q _
    calc (R.filter fun t => φ t = q).card ≤ (Finset.univ : Finset (ZMod N)).card := by
          apply Finset.card_le_card_of_injOn (fun t => t.1)
          · intro _ _; exact Finset.mem_univ _
          · intro t ht t' ht' h
            have h : t.1 = t'.1 := h
            have e := (Finset.mem_filter.mp ht).2
            have e' := (Finset.mem_filter.mp ht').2
            rw [← e'] at e
            have e0 := congrFun e 0
            have e2 := congrFun e 2
            have e3 := congrFun e 3
            simp only [φ, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.cons_val_three,
              Matrix.head_cons, Matrix.tail_cons] at e0 e2 e3
            have ha : t.2.2.1 = t'.2.2.1 := by
              have := e0; rw [h] at this; exact add_left_cancel this
            have hb : t.2.2.2 = t'.2.2.2 := by
              have := e3; rw [h] at this; exact add_left_cancel this
            have hx' : t.2.1 = t'.2.1 := by
              have := e2; rw [ha] at this; exact add_right_cancel this
            exact Prod.ext h (Prod.ext hx' (Prod.ext ha hb))
      _ = N := by rw [Finset.card_univ, ZMod.card]
  have h1 := Finset.card_le_mul_card_image (f := φ) R N hfib
  have h2 : (R.image φ).card ≤ phiAdditiveCount Finset.univ f := by
    unfold phiAdditiveCount countWhere
    exact (Finset.card_le_card himg).trans (le_of_eq (by congr 1))
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have h3 : κ * (N : Real) ^ 4 ≤ N * phiAdditiveCount Finset.univ f := by
    calc κ * (N : Real) ^ 4 ≤ R.card := h
      _ ≤ N * (R.image φ).card := by exact_mod_cast h1
      _ ≤ N * phiAdditiveCount Finset.univ f :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast h2) hNpos.le
  have : (N : Real) * (κ * (N : Real) ^ 3) ≤ N * phiAdditiveCount Finset.univ f := by
    calc (N : Real) * (κ * (N : Real) ^ 3) = κ * (N : Real) ^ 4 := by ring
      _ ≤ _ := h3
  exact le_of_mul_le_mul_left this hNpos

/-- **A Freiman homomorphism from a separated family.** -/
theorem freiman_of_separated {N : Nat} [NeZero N] [Fact N.Prime] {Ω : Type*} [Fintype Ω]
    [Nonempty Ω] (f g : ZMod N → ZMod N) (Q : Finset (ZMod N × ZMod N × Ω))
    (hsep : ∀ x x' a ω, (x, a, ω) ∈ Q → (x', a, ω) ∈ Q → f (x + a) - g x = f (x' + a) - g x')
    {c : Real} (hc : 0 < c)
    (hQ : c * (N : Real) ^ 2 * Fintype.card Ω ≤ Q.card) :
    ∃ B : Finset (ZMod N), (2 : Real) ^ (-(1882 : Real)) * (c ^ 4) ^ 1164 * N ≤ B.card ∧
      FreimanHom 8 B f := by
  have hcardG : (Fintype.card (ZMod N) : Real) = N := by rw [ZMod.card]
  have hresp := respected_quadruples_of_separated f g Q hsep hc.le (by rw [hcardG]; exact hQ)
  rw [hcardG] at hresp
  have hadd := phiAdditiveCount_ge_of_respected (κ := c ^ 4) f (by
    refine le_trans hresp (le_of_eq ?_)
    congr 2; ext t; simp only [Finset.mem_filter])
  obtain ⟨B, -, hB, hF⟩ := corollary_7_6_holds N Finset.univ f 1 (c ^ 4) Fact.out one_pos
    (by positivity) (by rw [Finset.card_univ, ZMod.card]; ring)
    (by rw [one_mul]; exact hadd)
  exact ⟨B, by simpa [mul_one] using hB, hF⟩

/-- The transfer to `phiAdditiveCount V f` when all four sums lie in `V`. -/
theorem phiAdditiveCount_ge_of_respected_in {N : Nat} [NeZero N] (f : ZMod N → ZMod N)
    (V : Finset (ZMod N)) {κ : Real}
    (h : κ * (N : Real) ^ 4 ≤ ((Finset.univ : Finset (ZMod N × ZMod N × ZMod N × ZMod N)).filter
      fun t => f (t.1 + t.2.2.1) - f (t.2.1 + t.2.2.1) =
        f (t.1 + t.2.2.2) - f (t.2.1 + t.2.2.2) ∧
        t.1 + t.2.2.1 ∈ V ∧ t.2.1 + t.2.2.1 ∈ V ∧ t.1 + t.2.2.2 ∈ V ∧ t.2.1 + t.2.2.2 ∈ V).card) :
    κ * (N : Real) ^ 3 ≤ phiAdditiveCount V f := by
  let R := (Finset.univ : Finset (ZMod N × ZMod N × ZMod N × ZMod N)).filter fun t =>
    f (t.1 + t.2.2.1) - f (t.2.1 + t.2.2.1) = f (t.1 + t.2.2.2) - f (t.2.1 + t.2.2.2) ∧
    t.1 + t.2.2.1 ∈ V ∧ t.2.1 + t.2.2.1 ∈ V ∧ t.1 + t.2.2.2 ∈ V ∧ t.2.1 + t.2.2.2 ∈ V
  let φ : ZMod N × ZMod N × ZMod N × ZMod N → (Fin 4 → ZMod N) := fun t =>
    ![t.1 + t.2.2.1, t.2.1 + t.2.2.2, t.2.1 + t.2.2.1, t.1 + t.2.2.2]
  have himg : R.image φ ⊆ (Finset.univ : Finset (Fin 4 → ZMod N)).filter (IsPhiAdditive V f) := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨he, m1, m2, m3, m4⟩ := (Finset.mem_filter.mp ht).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [φ, m1, m2, m3, m4]
    · simp only [IsAdditiveQuadruple, φ, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      ring
    · simp only [φ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      linear_combination he
  have hfib : ∀ q ∈ R.image φ, (R.filter fun t => φ t = q).card ≤ N := by
    intro q _
    calc (R.filter fun t => φ t = q).card ≤ (Finset.univ : Finset (ZMod N)).card := by
          apply Finset.card_le_card_of_injOn (fun t => t.1)
          · intro _ _; exact Finset.mem_univ _
          · intro t ht t' ht' h
            have h : t.1 = t'.1 := h
            have e := (Finset.mem_filter.mp ht).2
            have e' := (Finset.mem_filter.mp ht').2
            rw [← e'] at e
            have e0 := congrFun e 0
            have e2 := congrFun e 2
            have e3 := congrFun e 3
            simp only [φ, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.cons_val_three,
              Matrix.head_cons, Matrix.tail_cons] at e0 e2 e3
            have ha : t.2.2.1 = t'.2.2.1 := by
              have := e0; rw [h] at this; exact add_left_cancel this
            have hb : t.2.2.2 = t'.2.2.2 := by
              have := e3; rw [h] at this; exact add_left_cancel this
            have hx' : t.2.1 = t'.2.1 := by
              have := e2; rw [ha] at this; exact add_right_cancel this
            exact Prod.ext h (Prod.ext hx' (Prod.ext ha hb))
      _ = N := by rw [Finset.card_univ, ZMod.card]
  have h1 := Finset.card_le_mul_card_image (f := φ) R N hfib
  have h2 : (R.image φ).card ≤ phiAdditiveCount V f := by
    unfold phiAdditiveCount countWhere
    exact (Finset.card_le_card himg).trans (le_of_eq (by congr 1))
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have h3 : κ * (N : Real) ^ 4 ≤ N * phiAdditiveCount V f := by
    calc κ * (N : Real) ^ 4 ≤ R.card := h
      _ ≤ N * (R.image φ).card := by exact_mod_cast h1
      _ ≤ N * phiAdditiveCount V f :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast h2) hNpos.le
  have : (N : Real) * (κ * (N : Real) ^ 3) ≤ N * phiAdditiveCount V f := by
    calc (N : Real) * (κ * (N : Real) ^ 3) = κ * (N : Real) ^ 4 := by ring
      _ ≤ _ := h3
  exact le_of_mul_le_mul_left this hNpos

/-- **A Freiman homomorphism on the values of a separated family.** The set
`B` lies among the values `x + a` of the family. -/
theorem freiman_on_values_of_separated {N : Nat} [NeZero N] [Fact N.Prime] {Ω : Type*}
    [Fintype Ω] [Nonempty Ω] (f g : ZMod N → ZMod N) (Q : Finset (ZMod N × ZMod N × Ω))
    (hsep : ∀ x x' a ω, (x, a, ω) ∈ Q → (x', a, ω) ∈ Q → f (x + a) - g x = f (x' + a) - g x')
    {c : Real} (hc : 0 < c)
    (hQ : c * (N : Real) ^ 2 * Fintype.card Ω ≤ Q.card) :
    ∃ B ⊆ Q.image (fun q => q.1 + q.2.1),
      (2 : Real) ^ (-(1882 : Real)) * (c ^ 4) ^ 1164 *
          (Q.image (fun q => q.1 + q.2.1)).card ≤ B.card ∧
      FreimanHom 8 B f := by
  set V := Q.image (fun q : ZMod N × ZMod N × Ω => q.1 + q.2.1) with hV
  have hcardG : (Fintype.card (ZMod N) : Real) = N := by rw [ZMod.card]
  have hresp := respected_quadruples_of_separated_in f g Q hsep hc.le (by rw [hcardG]; exact hQ)
  rw [hcardG] at hresp
  have hadd := phiAdditiveCount_ge_of_respected_in (κ := c ^ 4) f V (by
    refine le_trans hresp (le_of_eq ?_)
    congr 2; ext t; simp only [Finset.mem_filter, Finset.mem_image, V])
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hVN : (V.card : Real) ≤ N := by
    have : V.card ≤ N := by
      calc V.card ≤ (Finset.univ : Finset (ZMod N)).card := Finset.card_le_univ V
        _ = N := by rw [Finset.card_univ, ZMod.card]
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos V.card with hV0 | hVpos
  · refine ⟨∅, Finset.empty_subset _, by rw [hV0]; simp, ?_⟩
    unfold FreimanHom
    simpa using (isAddFreimanHom_empty (n := 8) (B := Set.univ) (f := f))
  have hα : (0 : Real) < V.card / N := by
    have : (0 : Real) < V.card := by exact_mod_cast hVpos
    positivity
  have hα1 : (V.card : Real) / N ≤ 1 := (div_le_one hNpos).mpr hVN
  obtain ⟨B, hBV, hB, hF⟩ := corollary_7_6_holds N V f (V.card / N) (c ^ 4) Fact.out hα
    (by positivity) (by field_simp) (by
      calc c ^ 4 * ((V.card : Real) / N * N) ^ 3 = c ^ 4 * (V.card : Real) ^ 3 := by
            field_simp
        _ ≤ c ^ 4 * (N : Real) ^ 3 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hVN 3) (by positivity)
        _ ≤ _ := hadd)
  refine ⟨B, hBV, ?_, hF⟩
  calc (2 : Real) ^ (-(1882 : Real)) * (c ^ 4) ^ 1164 * V.card
      = (2 : Real) ^ (-(1882 : Real)) * (c ^ 4) ^ 1164 * (V.card / N) * N := by field_simp
    _ ≤ (B.card : Real) := hB

end LeanProofs.GowersSzemeredi
