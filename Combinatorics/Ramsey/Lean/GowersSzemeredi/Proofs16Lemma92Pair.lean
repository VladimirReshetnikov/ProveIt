import GowersSzemeredi.Proofs16ShiftAgreement
import GowersSzemeredi.Proofs07BohrHom

/-! Milićević's Lemma 9.2 for one pair of maps, in `ℤ/N` with polynomial
bounds (arXiv:2601.01682, printed pp. 63–65).

Let a family `Q` of `c N²|Ω|` triples `(x, a, ω)` separate `f` and `g`:
`f(x + a) − g(x)` depends only on `(a, ω)`. Then
`lemma_9_2_pair` gives a set `B` of values `x + a` with
`|B| ≥ 2^(-1882)·c^4656·|V|` (`V` is the value set), and a map `ψ`, such
that:
* `f` is a Freiman 8-homomorphism on `B`
  (`freiman_on_values_of_separated`, Corollary 7.6);
* `ψ` is a Freiman 2-homomorphism on a Bohr set `bohr K ρ` with
  `|K| ≤ 16α′^(−2)` and `ρ = α′/(32π)`, where `α′ = |B|/N`, and
  `f y − f y′ = ψ(y − y′)` on `B` (Lemma 7.8, `lemma_7_8_holds`);
* `g` shares the linear part: `g x − g x′ = ψ(x − x′)` whenever
  `(x, a, ω), (x′, a, ω) ∈ Q`, `x + a, x′ + a ∈ B` and `x − x′` lies in
  the Bohr set (`shared_linear_part`).

Milićević's coset progressions and rank argument are replaced by Lemma
7.8's Bohr set and the shared linear part. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- **Lemma 9.2 for one pair.** -/
theorem lemma_9_2_pair {N : Nat} [NeZero N] [Fact N.Prime] {Ω : Type*} [Fintype Ω]
    [Nonempty Ω] (f g : ZMod N → ZMod N) (Q : Finset (ZMod N × ZMod N × Ω))
    (hsep : ∀ x x' a ω, (x, a, ω) ∈ Q → (x', a, ω) ∈ Q → f (x + a) - g x = f (x' + a) - g x')
    {c : Real} (hc : 0 < c)
    (hQ : c * (N : Real) ^ 2 * Fintype.card Ω ≤ Q.card) :
    ∃ B ⊆ Q.image (fun q => q.1 + q.2.1), ∃ ψ : ZMod N → ZMod N,
      (2 : Real) ^ (-(1882 : Real)) * (c ^ 4) ^ 1164 *
          (Q.image (fun q => q.1 + q.2.1)).card ≤ B.card ∧
      FreimanHom 8 B f ∧
      ((section7Spectrum B ((B.card : Real) / N)).card : Real) ≤
        16 * ((B.card : Real) / N) ^ (-(2 : Real)) ∧
      FreimanHom 2 (bohr (section7Spectrum B ((B.card : Real) / N))
        (((B.card : Real) / N) / (32 * Real.pi))) ψ ∧
      (∀ y ∈ B, ∀ y' ∈ B, y - y' ∈ bohr (section7Spectrum B ((B.card : Real) / N))
        (((B.card : Real) / N) / (32 * Real.pi)) → f y - f y' = ψ (y - y')) ∧
      ∀ x x' a ω, (x, a, ω) ∈ Q → (x', a, ω) ∈ Q → x + a ∈ B → x' + a ∈ B →
        x - x' ∈ bohr (section7Spectrum B ((B.card : Real) / N))
          (((B.card : Real) / N) / (32 * Real.pi)) →
        g x - g x' = ψ (x - x') := by
  obtain ⟨B, hBV, hBcard, hF⟩ := freiman_on_values_of_separated f g Q hsep hc hQ
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  -- `Q` is nonempty, so `V` and then `B` are nonempty
  have hQpos : (0 : Real) < Q.card :=
    (by positivity : (0 : Real) < c * (N : Real) ^ 2 * Fintype.card Ω).trans_le hQ
  have hVpos : (0 : Real) < (Q.image (fun q => q.1 + q.2.1)).card := by
    have hQne : Q.Nonempty := Finset.card_pos.mp (by exact_mod_cast hQpos)
    exact_mod_cast (hQne.image _).card_pos
  have hBpos : (0 : Real) < B.card := (by positivity :
    (0 : Real) < (2 : Real) ^ (-(1882 : Real)) * (c ^ 4) ^ 1164 *
      (Q.image (fun q => q.1 + q.2.1)).card).trans_le hBcard
  have hα : (0 : Real) < (B.card : Real) / N := by positivity
  obtain ⟨hK, ψ, hψ, hloc⟩ := lemma_7_8_holds N B f ((B.card : Real) / N) hα (by field_simp) hF
  refine ⟨B, hBV, ψ, hBcard, hF, hK, hψ, fun y hy y' hy' hd => hloc y hy y' hy' hd, ?_⟩
  intro x x' a ω hx hx' hxa hxa' hd
  exact shared_linear_part f g ψ B _ (fun y hy y' hy' hd => hloc y hy y' hy' hd)
    (hsep x x' a ω hx hx') hxa hxa' hd

end LeanProofs.GowersSzemeredi
