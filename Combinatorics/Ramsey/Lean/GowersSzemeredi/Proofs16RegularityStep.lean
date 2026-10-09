import GowersSzemeredi.Proofs16FreimanKernelBohr
import GowersSzemeredi.Proofs16RelationAveraging

/-! One step of the algebraic regularity iteration ([49] Theorem 33) in
prime `ℤ/N`, on a centred Bohr domain.

The maps `ψⱼ` are Freiman-linear on `B(Ψ;σ)`, and the current class is
`C ⊆ B(Ψ;σ/4)`. The relations satisfied identically on `C` form the
subspace `Λ = relationSubmodule C ψ`. Suppose some set `Bad ⊆ C` of
vertices each carry a witness `(μ, v)` from a finite list `R`: a
coefficient vector `μ ∉ Λ` with `μ·ψ(t) = v`. In Claim 34 this is a
bounded relation `Σνγ + μ·ψ(t) = 0` with `μ ∉ Λ`, where `v = −Σνγ`.

`regularity_step_vertex` produces:
* one witness `(μ, v) ∈ R`, by pigeonhole (`exists_popular_witness`), and
  a set `F′ ⊆ Bad` with `|Bad| ≤ |R|·|F′|` on which `μ·ψ ≡ v`;
* the Bohr set `B′ = B(Spec F′; 1/(8π))` with `|Spec| ≤ 16α⁻²`, where
  `α = |F′|/N`, on which `μ·ψ(x) = μ·ψ(0)`
  (`freiman_const_on_bohr_of_dense`);
* hence `μ ∈ relationSubmodule (C ∩ B′) ψ` while `μ ∉ relationSubmodule C ψ`.

So the relation subspace grows strictly when the class is cut down to
`C ∩ B′`. By `strict_chain_length_le` this happens at most `|κ|` times. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- **One step of the regularity iteration, single vertices.** -/
theorem regularity_step_vertex {N : Nat} [NeZero N] [Fact N.Prime] {κ : Type*} [Fintype κ]
    (Ψ : Finset (ZMod N)) {σ : Real} (hσ : 0 ≤ σ) (ψ : κ → ZMod N → ZMod N)
    (hψ : ∀ j, IsFreimanLinearOn (bohr Ψ σ) (ψ j)) (C : Finset (ZMod N))
    (hC : C ⊆ bohr Ψ (σ / 4)) (R : Finset ((κ → ZMod N) × ZMod N)) (hR : R.Nonempty)
    (Bad : Finset (ZMod N)) (hBad : Bad ⊆ C) (hBad0 : Bad.Nonempty)
    (hwit : ∀ t ∈ Bad, ∃ p ∈ R, p.1 ∉ relationSubmodule C ψ ∧ ∑ j, p.1 j * ψ j t = p.2) :
    ∃ p ∈ R, p.1 ∉ relationSubmodule C ψ ∧
      ∃ F' : Finset (ZMod N), F' ⊆ Bad ∧ (Bad.card : Real) ≤ R.card * F'.card ∧
        (∀ t ∈ F', ∑ j, p.1 j * ψ j t = p.2) ∧
        ((section7Spectrum F' (F'.card / N)).card : Real) ≤
          16 * ((F'.card : Real) / N) ^ (-(2 : Real)) ∧
        p.1 ∈ relationSubmodule
          (C ∩ bohr (section7Spectrum F' (F'.card / N)) (1 / (8 * Real.pi))) ψ := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  -- pigeonhole onto one witness
  obtain ⟨p, hpR, hpop⟩ := exists_popular_witness Bad R
    (fun t p => p.1 ∉ relationSubmodule C ψ ∧ ∑ j, p.1 j * ψ j t = p.2) hR hwit
  set F' := Bad.filter fun t => p.1 ∉ relationSubmodule C ψ ∧ ∑ j, p.1 j * ψ j t = p.2
    with hF'
  have hF'sub : F' ⊆ Bad := Finset.filter_subset _ _
  have hF'pos : 0 < F'.card := by
    by_contra h0
    push Not at h0
    have : F'.card = 0 := by omega
    rw [this, Nat.cast_zero, mul_zero] at hpop
    have := hBad0.card_pos
    have : (0 : Real) < Bad.card := by exact_mod_cast this
    linarith
  obtain ⟨t₀, ht₀⟩ := Finset.card_pos.mp hF'pos
  have hpnot : p.1 ∉ relationSubmodule C ψ := (Finset.mem_filter.mp ht₀).2.1
  -- the combination is Freiman-linear and constant on `F′`
  set f : ZMod N → ZMod N := fun y => ∑ j, p.1 j * ψ j y with hf
  have hflin : IsFreimanLinearOn (bohr Ψ σ) f := IsFreimanLinearOn.linear_combination hψ p.1
  have hconst : ∀ z ∈ F', f z = p.2 := fun z hz => (Finset.mem_filter.mp hz).2.2
  have hα : (0 : Real) < F'.card / N := by
    have : (0 : Real) < F'.card := by exact_mod_cast hF'pos
    positivity
  have hcard : (F'.card : Real) = (F'.card / N) * N := by field_simp
  obtain ⟨hspec, hker⟩ := freiman_const_on_bohr_of_dense Ψ hσ hflin F'
    (fun z hz => hC (hBad (hF'sub hz))) hconst hα hcard
  refine ⟨p, hpR, hpnot, F', hF'sub, hpop, hconst, hspec, ?_⟩
  -- `μ ∈ relationSubmodule (C ∩ B′) ψ`
  rw [mem_relationSubmodule]
  intro y hy
  have h := (hker y (Finset.mem_inter.mp hy).2).2
  simp only [hf] at h
  rw [← sub_eq_zero] at h
  have hsum : ∑ j, p.1 j * (ψ j y - ψ j 0) = ∑ j, p.1 j * ψ j y - ∑ j, p.1 j * ψ j 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  exact h

end LeanProofs.GowersSzemeredi
