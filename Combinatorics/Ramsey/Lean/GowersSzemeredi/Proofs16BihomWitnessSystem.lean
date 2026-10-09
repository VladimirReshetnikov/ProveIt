import GowersSzemeredi.Proofs16ColumnRepSystem
import GowersSzemeredi.Proofs16ManyExactColumnQuadruples

/-! A column witness system for every Freiman bihomomorphism: Milićević's
Proposition 5.1 (i)–(ii) assembled in prime `ℤ/N`, in the interface
`IsColumnWitnessSystem` consumed by `many_exact_column_quadruples` (J.97).

For a Freiman bihomomorphism `φ` on `A ⊆ ℤ/N × ℤ/N` (`IsEBihomomorphism A φ {0}`)
and `α > 0`, let `X` be the columns with at least `αN` points. For every
`x ∈ X`:
* `column_freiman_bohr` gives `B_x` in the column with `|B_x| ≥ κN`,
  where `κ = 2⁻¹⁸⁸²(α⁴)¹¹⁶⁴`, on which `φ(x, ·)` is a Freiman
  8-homomorphism;
* `T x = commonLargeSpectrum B_x B_x (√β_x³/4)`, `L x = repMap B_x φ(x, ·)`,
  `W x = columnWitnesses B_x (T x)` and `ρ = 1/(4π)`.

`bihom_column_witness_system` proves:
* the witness-system property: every witness lies in the column, lands
  in the Bohr set, and represents `L x` exactly;
* `|T x| ≤ 16/κ²`;
* `L x` is Freiman-linear on `B(T x; ρ)` with `L x 0 = 0`;
* `|W x| ≥ κ⁴N⁴/(4·13^{|T x|})`.

All bounds are polynomial in `α`, except the witness density, which is
exponential in the spectrum size `|T x| ≤ 16/κ²`. That exponential is
the Bohr-set density at radius `1/(4π)`, the same loss as in the
source. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The column of `A` above `x`. -/
def bihomColumnSet {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N)) (x : ZMod N) :
    Finset (ZMod N) :=
  Finset.univ.filter fun y => (x, y) ∈ A

/-- The columns with at least `αN` points. -/
def denseColumns {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N)) (α : Real) :
    Finset (ZMod N) :=
  Finset.univ.filter fun x => α * N ≤ (bihomColumnSet A x).card

/-- A Freiman bihomomorphism is a Freiman 2-homomorphism on each column. -/
theorem column_freimanHom2 {N : Nat} [NeZero N] {A : Finset (ZMod N × ZMod N)}
    {φ : ZMod N × ZMod N → ZMod N} (hφ : IsEBihomomorphism A φ {0}) (x : ZMod N) :
    FreimanHom 2 (bihomColumnSet A x) (fun y => φ (x, y)) := by
  rw [FreimanHom, isAddFreimanHom_two]
  refine ⟨Set.mapsTo_univ _ _, ?_⟩
  intro a ha b hb c hc d hd habcd
  simp only [bihomColumnSet, Finset.coe_filter, Finset.mem_univ, true_and,
    Set.mem_setOf_eq] at ha hb hc hd
  have h := Set.mem_singleton_iff.mp (hφ.2 x a b c d habcd ha hb hc hd)
  linear_combination h

/-- **A dense column has a large Freiman 8-homomorphism core.** -/
theorem exists_column_core {N : Nat} [NeZero N] [Fact N.Prime] {A : Finset (ZMod N × ZMod N)}
    {φ : ZMod N × ZMod N → ZMod N} (hφ : IsEBihomomorphism A φ {0}) {α : Real} (hα : 0 < α)
    {x : ZMod N} (hx : x ∈ denseColumns A α) :
    ∃ B ⊆ bihomColumnSet A x,
      (2 : Real) ^ (-(1882 : Real)) * (α ^ 4) ^ 1164 * N ≤ B.card ∧
      FreimanHom 8 B (fun y => φ (x, y)) := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  obtain ⟨β, hβ⟩ : ∃ β : Real, β = (bihomColumnSet A x).card / N := ⟨_, rfl⟩
  have hcol : α * N ≤ (bihomColumnSet A x).card := (Finset.mem_filter.mp hx).2
  have hβα : α ≤ β := by rw [hβ, le_div_iff₀ hNR]; exact hcol
  have hβpos : 0 < β := lt_of_lt_of_le hα hβα
  have hβcard : ((bihomColumnSet A x).card : Real) = β * N := by
    rw [hβ]; exact (div_mul_cancel₀ _ hNR.ne').symm
  obtain ⟨B, hsub, hcard, h8, -⟩ := column_freiman_bohr (bihomColumnSet A x)
    (fun y => φ (x, y)) (column_freimanHom2 hφ x) hβpos hβcard
  refine ⟨B, hsub, le_trans ?_ hcard, h8⟩
  have h4 : (α ^ 4) ^ 1164 ≤ (β ^ 4) ^ 1164 :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hα.le hβα 4) 1164
  have h2 : (0 : Real) ≤ (2 : Real) ^ (-(1882 : Real)) := by positivity
  have := mul_le_mul_of_nonneg_left h4 h2
  nlinarith

/-- The chosen 8-homomorphism core of a dense column (empty otherwise). -/
def columnCore {N : Nat} [NeZero N] [Fact N.Prime] (A : Finset (ZMod N × ZMod N))
    (φ : ZMod N × ZMod N → ZMod N) (hφ : IsEBihomomorphism A φ {0}) {α : Real}
    (hα : 0 < α) (x : ZMod N) : Finset (ZMod N) :=
  if hx : x ∈ denseColumns A α then (exists_column_core hφ hα hx).choose else ∅

theorem columnCore_spec {N : Nat} [NeZero N] [Fact N.Prime] (A : Finset (ZMod N × ZMod N))
    (φ : ZMod N × ZMod N → ZMod N) (hφ : IsEBihomomorphism A φ {0}) {α : Real}
    (hα : 0 < α) {x : ZMod N} (hx : x ∈ denseColumns A α) :
    columnCore A φ hφ hα x ⊆ bihomColumnSet A x ∧
      (2 : Real) ^ (-(1882 : Real)) * (α ^ 4) ^ 1164 * N ≤ (columnCore A φ hφ hα x).card ∧
      FreimanHom 8 (columnCore A φ hφ hα x) (fun y => φ (x, y)) := by
  unfold columnCore
  rw [dif_pos hx]
  exact (exists_column_core hφ hα hx).choose_spec

/-- The spectrum of a column core. -/
def columnSpectrum {N : Nat} [NeZero N] (B : Finset (ZMod N)) : Finset (ZMod N) :=
  commonLargeSpectrum B B (Real.sqrt (((B.card : Real) / N) ^ 3) / 4)

/-- **The column witness system of a Freiman bihomomorphism.** -/
theorem bihom_column_witness_system {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (φ : ZMod N × ZMod N → ZMod N)
    (hφ : IsEBihomomorphism A φ {0}) {α : Real} (hα : 0 < α) :
    let κ : Real := (2 : Real) ^ (-(1882 : Real)) * (α ^ 4) ^ 1164
    let X := denseColumns A α
    let B := columnCore A φ hφ hα
    let T := fun x => columnSpectrum (B x)
    let L := fun x => repMap (B x) (fun y => φ (x, y))
    let W := fun x => columnWitnesses (B x) (T x)
    IsColumnWitnessSystem A φ X T L W (1 / (4 * Real.pi)) ∧
      (∀ x ∈ X, ((T x).card : Real) ≤ 16 / κ ^ 2) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) (1 / (4 * Real.pi))) (L x)) ∧
      (∀ x ∈ X, L x 0 = 0) ∧
      (∀ x ∈ X, κ ^ 4 * (N : Real) ^ 4 / 4 ≤ (13 : Real) ^ (T x).card * (W x).card) := by
  intro κ X B T L W
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hκ : 0 < κ := by positivity
  -- per-column facts
  have hcol : ∀ x ∈ X, B x ⊆ bihomColumnSet A x ∧ κ * N ≤ (B x).card ∧
      FreimanHom 8 (B x) (fun y => φ (x, y)) := fun x hx => columnCore_spec A φ hφ hα hx
  have hne : ∀ x ∈ X, (B x).Nonempty := by
    intro x hx
    have h := (hcol x hx).2.1
    have : (0 : Real) < (B x).card := lt_of_lt_of_le (by positivity) h
    exact Finset.card_pos.mp (by exact_mod_cast this)
  have hrep : ∀ x ∈ X, _ := fun x hx => column_rep_system (B x) (fun y => φ (x, y))
    (hcol x hx).2.2 (hne x hx)
  have hβ : ∀ x ∈ X, κ ≤ ((B x).card : Real) / N := by
    intro x hx; rw [le_div_iff₀ hNR]; exact (hcol x hx).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the witness system
    intro x hx z hz
    simp only [W, columnWitnesses, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    refine ⟨fun j => ?_, hz.2, ?_⟩
    · have := (hcol x hx).1 (hz.1 j)
      simpa [bihomColumnSet] using this
    · exact repMap_spec (hcol x hx).2.2 hz.1
  · -- spectrum size
    intro x hx
    obtain ⟨hS, -, -⟩ := hrep x hx
    refine hS.trans ?_
    have hb := hβ x hx
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact pow_le_pow_left₀ hκ.le hb 2
  · -- linearity
    intro x hx
    exact (hrep x hx).2.1
  · -- normalization
    intro x hx
    obtain ⟨a, ha⟩ := hne x hx
    have h := repMap_spec (hcol x hx).2.2 (q := fun _ => a) (fun _ => ha)
    simp only [fourSum, repFourValue] at h
    simpa using h
  · -- witness density
    intro x hx
    obtain ⟨-, -, hcount⟩ := hrep x hx
    have hw := column_witness_card_ge (B x) (T x) hcount (by positivity)
    have hb := hβ x hx
    have h4 : κ ^ 4 ≤ (((B x).card : Real) / N) ^ 4 := pow_le_pow_left₀ hκ.le hb 4
    calc κ ^ 4 * (N : Real) ^ 4 / 4 ≤ (((B x).card : Real) / N) ^ 4 * (N : Real) ^ 3 / 4 * N := by
          have : (0 : Real) ≤ (N : Real) ^ 4 / 4 := by positivity
          nlinarith
      _ ≤ _ := hw

/-- **Many dense columns.** If `|A| ≥ δN²`, at least `(δ/2)N` columns have
`(δ/2)N` points. -/
theorem denseColumns_card_ge {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N)) {δ : Real}
    (hδ : 0 ≤ δ) (hA : δ * (N : Real) ^ 2 ≤ A.card) :
    δ / 2 * N ≤ (denseColumns A (δ / 2)).card := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hsum : (A.card : Real) = ∑ x : ZMod N, ((bihomColumnSet A x).card : Real) := by
    have : A.card = ∑ x : ZMod N, (bihomColumnSet A x).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.card_bij (fun p _ => p.2)
      · intro p hp
        obtain ⟨hpA, hpx⟩ := Finset.mem_filter.mp hp
        simp only [bihomColumnSet, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hpx]; exact hpA
      · intro p hp p' hp' h
        have h1 := (Finset.mem_filter.mp hp).2
        have h2 := (Finset.mem_filter.mp hp').2
        exact Prod.ext (h1.trans h2.symm) h
      · intro y hy
        simp only [bihomColumnSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact ⟨(x, y), Finset.mem_filter.mpr ⟨hy, rfl⟩, rfl⟩
    exact_mod_cast this
  have hcolN : ∀ x, ((bihomColumnSet A x).card : Real) ≤ N := fun x => by
    exact_mod_cast (show (bihomColumnSet A x).card ≤ N by
      simpa using Finset.card_le_univ (bihomColumnSet A x))
  rw [Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun x => δ / 2 * N ≤ ((bihomColumnSet A x).card : Real))
    (fun x => ((bihomColumnSet A x).card : Real)) |>.symm] at hsum
  have hdense : ∑ x ∈ Finset.univ.filter (fun x => δ / 2 * N ≤ ((bihomColumnSet A x).card : Real)),
      ((bihomColumnSet A x).card : Real) ≤ (denseColumns A (δ / 2)).card * N := by
    calc _ ≤ ∑ _x ∈ Finset.univ.filter
          (fun x => δ / 2 * N ≤ ((bihomColumnSet A x).card : Real)), (N : Real) :=
          Finset.sum_le_sum fun x _ => hcolN x
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; rfl
  have hsparse : ∑ x ∈ Finset.univ.filter
      (fun x => ¬ δ / 2 * N ≤ ((bihomColumnSet A x).card : Real)),
      ((bihomColumnSet A x).card : Real) ≤ δ / 2 * (N : Real) ^ 2 := by
    calc _ ≤ ∑ _x ∈ Finset.univ.filter
          (fun x => ¬ δ / 2 * N ≤ ((bihomColumnSet A x).card : Real)), δ / 2 * (N : Real) :=
          Finset.sum_le_sum fun x hx => le_of_lt (not_le.mp (Finset.mem_filter.mp hx).2)
      _ ≤ ∑ _x : ZMod N, δ / 2 * (N : Real) := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring
  have hX : δ / 2 * (N : Real) * N ≤ (denseColumns A (δ / 2)).card * N := by nlinarith
  exact le_of_mul_le_mul_right hX hNR

/-- **Milićević's Proposition 5.1 with exact identities, prime `ℤ/N`.** A
Freiman bihomomorphism of density `δ` has `(δ/2)N` dense columns, each
carrying a Freiman-linear map on a Bohr set, and at least `θN³` additive
quadruples of these columns whose maps satisfy
`L x₀ + L x₁ = L x₂ + L x₃` exactly on one uniform Bohr restriction. -/
theorem bihom_many_exact_column_quadruples {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (φ : ZMod N × ZMod N → ZMod N)
    (hφ : IsEBihomomorphism A φ {0}) {δ : Real} (hδ : 0 < δ)
    (hA : δ * (N : Real) ^ 2 ≤ A.card) :
    let α : Real := δ / 2
    let κ : Real := (2 : Real) ^ (-(1882 : Real)) * (α ^ 4) ^ 1164
    let d : Nat := ⌊16 / κ ^ 2⌋₊
    let c : Real := κ ^ 4 / (4 * (13 : Real) ^ d)
    let ρ : Real := 1 / (4 * Real.pi)
    let θ : Real := c ^ 4 * α ^ 4 / 2
    let B := columnCore A φ hφ (half_pos hδ)
    sharedWitnessImageCap d ρ θ < N →
      0 < sharedWitnessKernelRadius d ρ θ ∧
        θ * (N : Real) ^ 3 ≤ ((exactColumnQuadruples (denseColumns A α)
          (fun x => columnSpectrum (B x)) (fun x => repMap (B x) (fun y => φ (x, y)))
          (sharedWitnessKernelRadius d ρ θ)).card : Real) := by
  intro α κ d c ρ θ B hN
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hα : 0 < α := half_pos hδ
  have hκ : 0 < κ := by positivity
  obtain ⟨hsys, hTκ, hlin, hzero, hWdens⟩ := bihom_column_witness_system A φ hφ hα
  have hT : ∀ x ∈ denseColumns A α, (columnSpectrum (B x)).card ≤ d := by
    intro x hx
    exact Nat.le_floor (hTκ x hx)
  have hW : ∀ x ∈ denseColumns A α,
      c * (N : Real) ^ 4 ≤ (columnWitnesses (B x) (columnSpectrum (B x))).card := by
    intro x hx
    have h := hWdens x hx
    have h13 : (13 : Real) ^ (columnSpectrum (B x)).card ≤ (13 : Real) ^ d :=
      pow_le_pow_right₀ (by norm_num) (hT x hx)
    have hpos : (0 : Real) < 4 * (13 : Real) ^ d := by positivity
    have hW0 : (0 : Real) ≤ (columnWitnesses (B x) (columnSpectrum (B x))).card :=
      Nat.cast_nonneg _
    rw [show c * (N : Real) ^ 4 = κ ^ 4 * (N : Real) ^ 4 / 4 / (13 : Real) ^ d by
      simp only [c]; field_simp]
    rw [div_le_iff₀ (by positivity)]
    calc κ ^ 4 * (N : Real) ^ 4 / 4 ≤ (13 : Real) ^ (columnSpectrum (B x)).card *
          (columnWitnesses (B x) (columnSpectrum (B x))).card := h
      _ ≤ (13 : Real) ^ d * (columnWitnesses (B x) (columnSpectrum (B x))).card :=
          mul_le_mul_of_nonneg_right h13 hW0
      _ = _ := by ring
  have hX : α * N ≤ (denseColumns A α).card := denseColumns_card_ge A hδ.le hA
  exact many_exact_column_quadruples A φ (denseColumns A α) (fun x => columnSpectrum (B x))
    (fun x => repMap (B x) (fun y => φ (x, y)))
    (fun x => columnWitnesses (B x) (columnSpectrum (B x)))
    (by positivity : (0 : Real) < ρ) (by positivity : (0 : Real) < c) hα hφ hsys hT hlin hzero
    hW hX hN

end LeanProofs.GowersSzemeredi
