import IPRADerivations.Topology.PrismIdentity
import IPRADerivations.Topology.SphereCycle

/-!
# The finite identity–antipodal obstruction

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/07_spheres.tex`, Theorem S04
(`thm:antipodal-finite`), assembled from the prism identity A19 (`Topology/PrismIdentity`), the cross-polytope
cycle S01 (`Topology/SphereCycle`) and the carrier degree S03 (as the hypothesis `hdeg1`; it is the conclusion
of `Topology/CarrierHomotopy.degree_one`). The same statement is the chain argument of Theorem
`thm:obstruction` of `topology/hairy_ball_ipra` for one pair of consecutive layers.

Chains are finite families of ordered tuples `σ i : ℕ → V` with integer coefficients `a i`, evaluated by a
functional `φ` on tuples (the coefficient of the positive facet, as an alternating functional):

* `prism_cycle`: "`∂P(c) = c_top − c_bottom`, since `∂c = 0`. Push this identity forward … Every
  `(n+1)`-simplex maps degenerately to the `n`-dimensional target, so its chain image is zero": if `c` is a
  cycle and every prism tuple of `f, g` on `c` has vanishing `φ`-boundary, then `g_# c = f_# c` under `φ`;
* `ext`: a facet `Fin (n+1) → Vtx (n+1)` as a sequence;
* `antipodal_obstruction`: for even `n` there is no cycle `c` with `u_# c = z_n` (carrier degree one) whose
  prism tuples for `u` and `A ∘ u` are degenerate: "this is `−z_n = z_n`. The coefficient of the positive
  facet says `−1 = 1` in `ℤ`, a contradiction."
* `layers_constant`, `finite_obstruction`: the same along `T` time layers with degenerate prisms between
  consecutive layers (`thm:obstruction` of the hairy ball packet: "consecutive layers have exactly the same
  top image chain. Repeating this equality gives `Z = c_# S^r(Z) = (A ∘ c)_# S^r(Z) = (−1)^d Z`").
-/

namespace LeanProofs.IPRA.Topology.AntipodalObstruction

open Finset
open LeanProofs.IPRA.Topology.PrismIdentity (face prism prism_identity)
open LeanProofs.IPRA.Topology.SphereCycle (Vtx facet coef anti antipodal top_coef)

variable {V W M ι : Type*} [AddCommGroup M]

/-- The prism identity on a cycle whose prism tuples have vanishing boundary under `φ`: `g_# c = f_# c`. -/
theorem prism_cycle (k : ℕ) (s : Finset ι) (a : ι → ℤ) (σ : ι → ℕ → V) (f g : V → W) (φ : (ℕ → W) → M)
    (hφ : ∀ ρ τ : ℕ → W, (∀ m < k + 1, ρ m = τ m) → φ ρ = φ τ)
    (hcyc : ∀ ψ : (ℕ → V) → M, ∑ i ∈ s, a i • ∑ l ∈ range (k + 1), ((-1 : ℤ) ^ l) • ψ (face l (σ i)) = 0)
    (hdegen : ∀ i ∈ s, ∀ m ∈ range (k + 1),
      ∑ j ∈ range (k + 2), ((-1 : ℤ) ^ j) • φ (face j (prism f g m (σ i))) = 0) :
    ∑ i ∈ s, a i • φ (g ∘ σ i) = ∑ i ∈ s, a i • φ (f ∘ σ i) := by
  have hA : ∀ i ∈ s, ∑ m ∈ range (k + 1), ∑ j ∈ range (k + 2),
      ((-1 : ℤ) ^ (m + j)) • φ (face j (prism f g m (σ i))) = 0 := by
    intro i hi
    refine sum_eq_zero fun m hm => ?_
    have h := hdegen i hi m hm
    calc ∑ j ∈ range (k + 2), ((-1 : ℤ) ^ (m + j)) • φ (face j (prism f g m (σ i)))
        = ((-1 : ℤ) ^ m) • ∑ j ∈ range (k + 2), ((-1 : ℤ) ^ j) • φ (face j (prism f g m (σ i))) := by
          rw [smul_sum]
          exact sum_congr rfl fun j _ => by rw [pow_add, mul_smul]
      _ = 0 := by rw [h, smul_zero]
  have hB : ∑ i ∈ s, a i • ∑ l ∈ range (k + 1), ∑ m ∈ range k,
      ((-1 : ℤ) ^ (l + m)) • φ (prism f g m (face l (σ i))) = 0 := by
    have e : ∀ i ∈ s, a i • ∑ l ∈ range (k + 1), ∑ m ∈ range k,
        ((-1 : ℤ) ^ (l + m)) • φ (prism f g m (face l (σ i))) =
        ∑ m ∈ range k, ((-1 : ℤ) ^ m) •
          (a i • ∑ l ∈ range (k + 1), ((-1 : ℤ) ^ l) • φ (prism f g m (face l (σ i)))) := by
      intro i _
      rw [sum_comm, smul_sum]
      refine sum_congr rfl fun m _ => ?_
      rw [smul_comm]
      congr 1
      rw [smul_sum]
      exact sum_congr rfl fun l _ => by rw [← mul_smul, ← pow_add, _root_.add_comm]
    rw [sum_congr rfl e, sum_comm]
    refine sum_eq_zero fun m _ => ?_
    have h := hcyc fun ρ => φ (prism f g m ρ)
    beta_reduce at h
    rw [← smul_sum, h, smul_zero]
  have hid : ∀ i ∈ s, a i • (φ (g ∘ σ i) - φ (f ∘ σ i)) =
      a i • (∑ m ∈ range (k + 1), ∑ j ∈ range (k + 2),
        ((-1 : ℤ) ^ (m + j)) • φ (face j (prism f g m (σ i)))) +
      a i • ∑ l ∈ range (k + 1), ∑ m ∈ range k, ((-1 : ℤ) ^ (l + m)) • φ (prism f g m (face l (σ i))) := by
    intro i _
    rw [← smul_add, prism_identity f g k φ hφ (σ i)]
  have hsum : ∑ i ∈ s, a i • (φ (g ∘ σ i) - φ (f ∘ σ i)) = 0 := by
    rw [sum_congr rfl hid, sum_add_distrib, hB, _root_.add_zero]
    exact sum_eq_zero fun i hi => by rw [hA i hi, smul_zero]
  rw [← sub_eq_zero, ← sum_sub_distrib]
  simpa only [smul_sub] using hsum

/-- A facet as a sequence (constant beyond its entries). -/
def ext {n : ℕ} (τ : Fin (n + 1) → Vtx (n + 1)) : ℕ → Vtx (n + 1) :=
  fun m => if h : m < n + 1 then τ ⟨m, h⟩ else (true, 0)

theorem anti_ext {n : ℕ} (τ : Fin (n + 1) → Vtx (n + 1)) (m : ℕ) (hm : m < n + 1) :
    (anti ∘ ext τ) m = ext (anti ∘ τ) m := by
  simp [ext, hm]

/-- Along a sequence of layers with degenerate prisms between consecutive ones, the image of the cycle under
`φ` is the same at every layer. -/
theorem layers_constant (k : ℕ) (s : Finset ι) (a : ι → ℤ) (σ : ι → ℕ → V) (ℓ : ℕ → V → W) (φ : (ℕ → W) → M)
    (hφ : ∀ ρ τ : ℕ → W, (∀ m < k + 1, ρ m = τ m) → φ ρ = φ τ)
    (hcyc : ∀ ψ : (ℕ → V) → M, ∑ i ∈ s, a i • ∑ l ∈ range (k + 1), ((-1 : ℤ) ^ l) • ψ (face l (σ i)) = 0)
    (T : ℕ)
    (hdegen : ∀ t < T, ∀ i ∈ s, ∀ m ∈ range (k + 1),
      ∑ j ∈ range (k + 2), ((-1 : ℤ) ^ j) • φ (face j (prism (ℓ t) (ℓ (t + 1)) m (σ i))) = 0) :
    ∑ i ∈ s, a i • φ (ℓ T ∘ σ i) = ∑ i ∈ s, a i • φ (ℓ 0 ∘ σ i) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [prism_cycle k s a σ (ℓ T) (ℓ (T + 1)) φ hφ hcyc (hdegen T (Nat.lt_succ_self T))]
    exact ih fun t ht => hdegen t (Nat.lt_succ_of_lt ht)

/-- The sign clash: for even `n`, a cycle with `u_# c = z_n` cannot satisfy `(A ∘ u)_# c = u_# c` under the
coefficient functional of the positive facet. -/
theorem sign_clash {n : ℕ} (hn : Even n) (s : Finset ι) (a : ι → ℤ) (σ : ι → ℕ → V)
    (u : V → Vtx (n + 1)) (φ : (ℕ → Vtx (n + 1)) → ℤ)
    (hφ : ∀ ρ τ : ℕ → Vtx (n + 1), (∀ m < n + 1, ρ m = τ m) → φ ρ = φ τ)
    (hfacet : ∀ ε : Fin (n + 1) → Bool,
      φ (ext (facet ε)) = if facet ε = facet (fun _ => true) then 1 else 0)
    (hdeg1 : ∀ χ : (ℕ → Vtx (n + 1)) → ℤ,
      (∀ ρ τ : ℕ → Vtx (n + 1), (∀ m < n + 1, ρ m = τ m) → χ ρ = χ τ) →
      ∑ i ∈ s, a i • χ (u ∘ σ i) = ∑ ε : Fin (n + 1) → Bool, coef ε • χ (ext (facet ε)))
    (h1 : ∑ i ∈ s, a i • φ ((anti ∘ u) ∘ σ i) = ∑ i ∈ s, a i • φ (u ∘ σ i)) : False := by
  have e4 : ∑ ε : Fin (n + 1) → Bool, coef ε • φ (ext (facet ε)) = 1 := by
    simp only [hfacet, smul_eq_mul, mul_ite, _root_.mul_one, MulZeroClass.mul_zero]
    exact top_coef
  have hR : ∑ i ∈ s, a i • φ (u ∘ σ i) = 1 := by
    rw [hdeg1 φ hφ, e4]
  have hφ' : ∀ ρ τ : ℕ → Vtx (n + 1), (∀ m < n + 1, ρ m = τ m) → φ (anti ∘ ρ) = φ (anti ∘ τ) :=
    fun ρ τ h => hφ _ _ fun m hm => by simp only [Function.comp_apply, h m hm]
  have e : ∑ i ∈ s, a i • φ ((anti ∘ u) ∘ σ i) =
      ∑ ε : Fin (n + 1) → Bool, coef ε • φ (anti ∘ ext (facet ε)) :=
    hdeg1 (fun ρ => φ (anti ∘ ρ)) hφ'
  have e2 : ∀ ε : Fin (n + 1) → Bool, φ (anti ∘ ext (facet ε)) = φ (ext (anti ∘ facet ε)) :=
    fun ε => hφ _ _ fun m hm => anti_ext (facet ε) m hm
  have e3 : ∑ ε : Fin (n + 1) → Bool, coef ε • φ (ext (anti ∘ facet ε)) =
      ((-1 : ℤ) ^ (n + 1)) • ∑ ε : Fin (n + 1) → Bool, coef ε • φ (ext (facet ε)) :=
    antipodal (M := ℤ) fun τ => φ (ext τ)
  have e2' : ∑ ε : Fin (n + 1) → Bool, coef ε • φ (anti ∘ ext (facet ε)) =
      ∑ ε : Fin (n + 1) → Bool, coef ε • φ (ext (anti ∘ facet ε)) :=
    sum_congr rfl fun ε _ => by rw [e2 ε]
  have hL : ∑ i ∈ s, a i • φ ((anti ∘ u) ∘ σ i) = -1 := by
    rw [e, e2', e3, e4, pow_succ, hn.neg_one_pow]
    norm_num
  rw [hL, hR] at h1
  norm_num at h1

/-- S04: for even `n`, no cycle carried with degree one has degenerate prisms between `u` and `A ∘ u`. -/
theorem antipodal_obstruction {n : ℕ} (hn : Even n) (s : Finset ι) (a : ι → ℤ) (σ : ι → ℕ → V)
    (u : V → Vtx (n + 1)) (φ : (ℕ → Vtx (n + 1)) → ℤ)
    (hφ : ∀ ρ τ : ℕ → Vtx (n + 1), (∀ m < n + 1, ρ m = τ m) → φ ρ = φ τ)
    (hfacet : ∀ ε : Fin (n + 1) → Bool,
      φ (ext (facet ε)) = if facet ε = facet (fun _ => true) then 1 else 0)
    (hcyc : ∀ ψ : (ℕ → V) → ℤ, ∑ i ∈ s, a i • ∑ l ∈ range (n + 1), ((-1 : ℤ) ^ l) • ψ (face l (σ i)) = 0)
    (hdeg1 : ∀ χ : (ℕ → Vtx (n + 1)) → ℤ,
      (∀ ρ τ : ℕ → Vtx (n + 1), (∀ m < n + 1, ρ m = τ m) → χ ρ = χ τ) →
      ∑ i ∈ s, a i • χ (u ∘ σ i) = ∑ ε : Fin (n + 1) → Bool, coef ε • χ (ext (facet ε)))
    (hdegen : ∀ i ∈ s, ∀ m ∈ range (n + 1),
      ∑ j ∈ range (n + 2), ((-1 : ℤ) ^ j) • φ (face j (prism u (anti ∘ u) m (σ i))) = 0) : False :=
  sign_clash hn s a σ u φ hφ hfacet hdeg1 (prism_cycle n s a σ u (anti ∘ u) φ hφ hcyc hdegen)

/-- The finite obstruction with `T` time layers (`thm:obstruction` of the hairy ball packet, in chain form):
for even `n`, labels `ℓ_0, …, ℓ_T` with `ℓ_0` of carrier degree one and `ℓ_T = A ∘ ℓ_0` cannot have degenerate
prisms between all consecutive layers, so some fine simplex and some `t < T` carry opposite labels. -/
theorem finite_obstruction {n : ℕ} (hn : Even n) (s : Finset ι) (a : ι → ℤ) (σ : ι → ℕ → V)
    (ℓ : ℕ → V → Vtx (n + 1)) (T : ℕ) (hT : ℓ T = anti ∘ ℓ 0) (φ : (ℕ → Vtx (n + 1)) → ℤ)
    (hφ : ∀ ρ τ : ℕ → Vtx (n + 1), (∀ m < n + 1, ρ m = τ m) → φ ρ = φ τ)
    (hfacet : ∀ ε : Fin (n + 1) → Bool,
      φ (ext (facet ε)) = if facet ε = facet (fun _ => true) then 1 else 0)
    (hcyc : ∀ ψ : (ℕ → V) → ℤ, ∑ i ∈ s, a i • ∑ l ∈ range (n + 1), ((-1 : ℤ) ^ l) • ψ (face l (σ i)) = 0)
    (hdeg1 : ∀ χ : (ℕ → Vtx (n + 1)) → ℤ,
      (∀ ρ τ : ℕ → Vtx (n + 1), (∀ m < n + 1, ρ m = τ m) → χ ρ = χ τ) →
      ∑ i ∈ s, a i • χ (ℓ 0 ∘ σ i) = ∑ ε : Fin (n + 1) → Bool, coef ε • χ (ext (facet ε)))
    (hdegen : ∀ t < T, ∀ i ∈ s, ∀ m ∈ range (n + 1),
      ∑ j ∈ range (n + 2), ((-1 : ℤ) ^ j) • φ (face j (prism (ℓ t) (ℓ (t + 1)) m (σ i))) = 0) : False := by
  have h := layers_constant n s a σ ℓ φ hφ hcyc T hdegen
  rw [hT] at h
  exact sign_clash hn s a σ (ℓ 0) φ hφ hfacet hdeg1 h

end LeanProofs.IPRA.Topology.AntipodalObstruction
