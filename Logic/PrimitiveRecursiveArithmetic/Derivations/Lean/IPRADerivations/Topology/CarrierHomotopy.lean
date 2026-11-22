import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Abel

/-!
# The explicit simplex-carrier homotopy and carrier degree one

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/05_algebraic.tex`, Theorem
`thm:simplex-carrier` (A20), and `07_spheres.tex`, Lemma `lem:carrier-degree-one` (S03):

* the source chains are the free group `S →₀ ℤ` on the simplices `S` of `K` (the empty simplex included, which
  is the augmentation `C_{-1}`), with a boundary `bd σ` supported on simplices of smaller rank and `∂² = 0`; the
  target `B` has a boundary `∂` with `∂² = 0`; `F, G` are chain maps (commuting with the augmented boundaries, so
  they "preserve augmentation in degree zero");
* each simplex `σ` has a carrier subgroup `Car σ` (the chains on `C(σ)`), monotone along faces, containing
  `F(σ)` and `G(σ)`, with a contracting cone `c_σ` (`c_a` for the least vertex `a` of `C(σ)`):
  `∂ c_σ + c_σ ∂ = 1` on `Car σ` ("Hence `∂c_a + c_a∂ = 1`, including degree zero", the cone identity of
  `Topology/SimplicialCone`);
* `homotopy`: "`z_σ = G(σ) − F(σ) − H(∂σ)`, `H(σ) = c_{a_σ} z_σ`", by well-founded recursion on the rank;
* `homotopy_spec` (A20): `H(σ) ∈ Car σ` and `∂H(σ) + H(∂σ) = G(σ) − F(σ)` ("`∂z_σ = (G − F)(∂σ) −
  ∂H(∂σ) = 0`"), and `homotopy_identity`: `∂H + H∂ = G − F` on all chains;
* `degree_one` (S03): a cycle `z` (`∂z = 0`) on which `H` vanishes (in the top degree, "`C_n` has no
  `(n+1)`-chains") has `G z = F z`, so `u_# s^r(z_n) = z_n`.
-/

namespace LeanProofs.IPRA.Topology.CarrierHomotopy

open Finsupp

variable {S B : Type*} [AddCommGroup B]

/-- The boundary of the free source complex. -/
noncomputable def bdA (bd : S → S →₀ ℤ) : (S →₀ ℤ) →ₗ[ℤ] (S →₀ ℤ) := linearCombination ℤ bd

/-- The carrier homotopy on a simplex: `H(σ) = c_σ (G(σ) − F(σ) − H(∂σ))`. -/
noncomputable def homotopy (r : S → ℕ) (bd : S → S →₀ ℤ) (hbd : ∀ σ, ∀ ρ ∈ (bd σ).support, r ρ < r σ)
    (F G : (S →₀ ℤ) →ₗ[ℤ] B) (c : S → B →ₗ[ℤ] B) (σ : S) : B :=
  c σ (G (single σ 1) - F (single σ 1) -
    (bd σ).support.attach.sum fun ρ => bd σ ρ.1 • homotopy r bd hbd F G c ρ.1)
termination_by r σ
decreasing_by all_goals (try simp_wf); exact hbd σ ρ.1 ρ.2

/-- The homotopy on all chains. -/
noncomputable def H (r : S → ℕ) (bd : S → S →₀ ℤ) (hbd : ∀ σ, ∀ ρ ∈ (bd σ).support, r ρ < r σ)
    (F G : (S →₀ ℤ) →ₗ[ℤ] B) (c : S → B →ₗ[ℤ] B) : (S →₀ ℤ) →ₗ[ℤ] B :=
  linearCombination ℤ (homotopy r bd hbd F G c)

variable {r : S → ℕ} {bd : S → S →₀ ℤ} {hbd : ∀ σ, ∀ ρ ∈ (bd σ).support, r ρ < r σ}
  {F G : (S →₀ ℤ) →ₗ[ℤ] B} {c : S → B →ₗ[ℤ] B}

theorem homotopy_eq (σ : S) :
    homotopy r bd hbd F G c σ = c σ (G (single σ 1) - F (single σ 1) - H r bd hbd F G c (bd σ)) := by
  rw [homotopy, H, linearCombination_apply, Finsupp.sum]
  exact congrArg (fun t => c σ (G (single σ 1) - F (single σ 1) - t))
    (Finset.sum_attach (bd σ).support fun ρ => bd σ ρ • homotopy r bd hbd F G c ρ)

/-- A linear map vanishing on the basis elements of the support of `x` vanishes at `x`. -/
theorem vanish_of_support {M : Type*} [AddCommGroup M] (D : (S →₀ ℤ) →ₗ[ℤ] M) (x : S →₀ ℤ)
    (h : ∀ ρ ∈ x.support, D (single ρ 1) = 0) : D x = 0 := by
  conv_lhs => rw [← Finsupp.sum_single x]
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun ρ hρ => ?_
  rw [← smul_single_one, map_zsmul, h ρ hρ, smul_zero]

variable {d : B →ₗ[ℤ] B}

/-- A20: `H(σ)` lies in the carrier of `σ` and `∂H(σ) + H(∂σ) = G(σ) − F(σ)`. -/
theorem homotopy_spec (hdd : ∀ y, d (d y) = 0) (hbdd : ∀ σ, bdA bd (bd σ) = 0)
    (hF : ∀ x, d (F x) = F (bdA bd x)) (hG : ∀ x, d (G x) = G (bdA bd x))
    (Car : S → AddSubgroup B) (hFc : ∀ σ, F (single σ 1) ∈ Car σ) (hGc : ∀ σ, G (single σ 1) ∈ Car σ)
    (hface : ∀ σ, ∀ ρ ∈ (bd σ).support, Car ρ ≤ Car σ) (hcc : ∀ σ, ∀ y ∈ Car σ, c σ y ∈ Car σ)
    (hcone : ∀ σ, ∀ y ∈ Car σ, d (c σ y) + c σ (d y) = y) :
    ∀ m σ, r σ = m → homotopy r bd hbd F G c σ ∈ Car σ ∧
      d (homotopy r bd hbd F G c σ) + H r bd hbd F G c (bd σ) = G (single σ 1) - F (single σ 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro σ hσ
  have IH : ∀ ρ ∈ (bd σ).support, homotopy r bd hbd F G c ρ ∈ Car ρ ∧
      d (homotopy r bd hbd F G c ρ) + H r bd hbd F G c (bd ρ) = G (single ρ 1) - F (single ρ 1) :=
    fun ρ hρ => ih (r ρ) (by rw [← hσ]; exact hbd σ ρ hρ) ρ rfl
  -- `H(∂σ) ∈ Car σ`
  have hHbd : H r bd hbd F G c (bd σ) ∈ Car σ := by
    rw [H, linearCombination_apply, Finsupp.sum]
    exact sum_mem fun ρ hρ => zsmul_mem (hface σ ρ hρ (IH ρ hρ).1) _
  set z := G (single σ 1) - F (single σ 1) - H r bd hbd F G c (bd σ) with hz
  have hzc : z ∈ Car σ := AddSubgroup.sub_mem _ (AddSubgroup.sub_mem _ (hGc σ) (hFc σ)) hHbd
  -- `∂ H(∂σ) = (G − F)(∂σ)`, from the faces
  have hD : (d ∘ₗ H r bd hbd F G c + H r bd hbd F G c ∘ₗ bdA bd - (G - F)) (bd σ) = 0 :=
    vanish_of_support _ _ fun ρ hρ => by
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply]
      rw [H, bdA, linearCombination_single, linearCombination_single, one_smul, one_smul, ← H]
      rw [(IH ρ hρ).2]
      simp
  have hdH : d (H r bd hbd F G c (bd σ)) = G (bd σ) - F (bd σ) := by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, hbdd, map_zero,
      add_zero] at hD
    exact sub_eq_zero.mp hD
  -- `∂z = 0`
  have hdz : d z = 0 := by
    have e₁ : bdA bd (single σ 1) = bd σ := by rw [bdA, linearCombination_single, one_smul]
    rw [hz, map_sub, map_sub, hG, hF, e₁, hdH]
    abel
  refine ⟨?_, ?_⟩
  · rw [homotopy_eq]; exact hcc σ z hzc
  · rw [homotopy_eq]
    have := hcone σ z hzc
    rw [hdz, map_zero, add_zero] at this
    rw [← hz, this, hz]
    abel

/-- A20 on all chains: `∂H + H∂ = G − F`. -/
theorem homotopy_identity (hdd : ∀ y, d (d y) = 0) (hbdd : ∀ σ, bdA bd (bd σ) = 0)
    (hF : ∀ x, d (F x) = F (bdA bd x)) (hG : ∀ x, d (G x) = G (bdA bd x))
    (Car : S → AddSubgroup B) (hFc : ∀ σ, F (single σ 1) ∈ Car σ) (hGc : ∀ σ, G (single σ 1) ∈ Car σ)
    (hface : ∀ σ, ∀ ρ ∈ (bd σ).support, Car ρ ≤ Car σ) (hcc : ∀ σ, ∀ y ∈ Car σ, c σ y ∈ Car σ)
    (hcone : ∀ σ, ∀ y ∈ Car σ, d (c σ y) + c σ (d y) = y) (x : S →₀ ℤ) :
    d (H r bd hbd F G c x) + H r bd hbd F G c (bdA bd x) = G x - F x := by
  have hD : (d ∘ₗ H r bd hbd F G c + H r bd hbd F G c ∘ₗ bdA bd - (G - F)) x = 0 :=
    vanish_of_support _ _ fun σ _ => by
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply]
      rw [H, bdA, linearCombination_single, linearCombination_single, one_smul, one_smul, ← H]
      rw [(homotopy_spec hdd hbdd hF hG Car hFc hGc hface hcc hcone (r σ) σ rfl).2]
      simp
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply] at hD
  exact sub_eq_zero.mp hD

/-- S03: on a cycle `z` where the homotopy vanishes, `G z = F z`. -/
theorem degree_one (hdd : ∀ y, d (d y) = 0) (hbdd : ∀ σ, bdA bd (bd σ) = 0)
    (hF : ∀ x, d (F x) = F (bdA bd x)) (hG : ∀ x, d (G x) = G (bdA bd x))
    (Car : S → AddSubgroup B) (hFc : ∀ σ, F (single σ 1) ∈ Car σ) (hGc : ∀ σ, G (single σ 1) ∈ Car σ)
    (hface : ∀ σ, ∀ ρ ∈ (bd σ).support, Car ρ ≤ Car σ) (hcc : ∀ σ, ∀ y ∈ Car σ, c σ y ∈ Car σ)
    (hcone : ∀ σ, ∀ y ∈ Car σ, d (c σ y) + c σ (d y) = y) {z : S →₀ ℤ} (hz : bdA bd z = 0)
    (htop : H r bd hbd F G c z = 0) : G z = F z := by
  have := homotopy_identity (r := r) (hbd := hbd) hdd hbdd hF hG Car hFc hGc hface hcc hcone z
  rw [htop, hz, map_zero, map_zero, add_zero] at this
  exact (sub_eq_zero.mp this.symm)

end LeanProofs.IPRA.Topology.CarrierHomotopy
