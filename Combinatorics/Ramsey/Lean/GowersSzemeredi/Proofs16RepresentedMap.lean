import GowersSzemeredi.Proofs16LineFreimanUnconditional

/-! The map induced by a Freiman 8-homomorphism on `2B − 2B`.

If `f` is a Freiman 8-homomorphism on `B ⊆ ℤ/N`, then
`ψ(a + e − b − c) = f a + f e − f b − f c` is well defined on the
represented points (`repMap_spec`). It is Freiman-linear on every set of
represented points (`repMap_freimanLinear`).

The corpus already uses this construction privately inside Gowers's
Lemma 7.8 (`Proofs07BohrHom`). It is re-proved here in public form so that
every four-tuple of `B` is a witness for the induced map. That is the
form Milićević's Proposition 5.1 (ii)–(iii) needs, and editing the
foundational module would force a large rebuild. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- Sums of eight points under a Freiman 8-homomorphism. -/
theorem freimanHom8_fin_sum {N : Nat} {B : Finset (ZMod N)} {f : ZMod N → ZMod N}
    (hf : FreimanHom 8 B f) (x y : Fin 8 → ZMod N) (hx : ∀ i, x i ∈ B) (hy : ∀ i, y i ∈ B)
    (hsum : ∑ i, x i = ∑ i, y i) : ∑ i, f (x i) = ∑ i, f (y i) := by
  let sx : Multiset (ZMod N) := Multiset.map x (Finset.univ : Finset (Fin 8)).val
  let sy : Multiset (ZMod N) := Multiset.map y (Finset.univ : Finset (Fin 8)).val
  have hsA : ∀ ⦃z⦄, z ∈ sx → z ∈ (B : Set (ZMod N)) := by
    intro z hz
    simp only [sx, Multiset.mem_map] at hz
    obtain ⟨i, _, rfl⟩ := hz
    exact hx i
  have htA : ∀ ⦃z⦄, z ∈ sy → z ∈ (B : Set (ZMod N)) := by
    intro z hz
    simp only [sy, Multiset.mem_map] at hz
    obtain ⟨i, _, rfl⟩ := hz
    exact hy i
  have hsCard : sx.card = 8 := by simp [sx]
  have htCard : sy.card = 8 := by simp [sy]
  have hsEq : sx.sum = sy.sum := by simpa [sx, sy, Fin.sum_univ_succ] using hsum
  have hmap := hf.map_sum_eq_map_sum hsA htA hsCard htCard hsEq
  simpa [sx, sy, Fin.sum_univ_succ] using hmap

/-- The point represented by a four-tuple. -/
def fourSum {N : Nat} (q : Fin 4 → ZMod N) : ZMod N := q 0 + q 1 - q 2 - q 3

/-- The value of `f` along a four-tuple. -/
def repFourValue {N : Nat} (f : ZMod N → ZMod N) (q : Fin 4 → ZMod N) : ZMod N :=
  f (q 0) + f (q 1) - f (q 2) - f (q 3)

/-- `d` is represented as `a + e − b − c` with all four points in `B`. -/
def IsRepresented {N : Nat} (B : Finset (ZMod N)) (d : ZMod N) : Prop :=
  ∃ q : Fin 4 → ZMod N, (∀ i, q i ∈ B) ∧ fourSum q = d

/-- The map induced on represented points. -/
def repMap {N : Nat} (B : Finset (ZMod N)) (f : ZMod N → ZMod N) (d : ZMod N) : ZMod N :=
  if h : IsRepresented B d then repFourValue f h.choose else 0

/-- Two representations of the same point give the same value. -/
theorem repFourValue_eq_of_fourSum_eq {N : Nat} {B : Finset (ZMod N)} {f : ZMod N → ZMod N}
    (hf : FreimanHom 8 B f) {q q' : Fin 4 → ZMod N} (hq : ∀ i, q i ∈ B)
    (hq' : ∀ i, q' i ∈ B) (h : fourSum q = fourSum q') : repFourValue f q = repFourValue f q' := by
  let x : Fin 8 → ZMod N := ![q 0, q 1, q' 2, q' 3, q 0, q 0, q 0, q 0]
  let y : Fin 8 → ZMod N := ![q' 0, q' 1, q 2, q 3, q 0, q 0, q 0, q 0]
  have hx : ∀ i, x i ∈ B := by intro i; fin_cases i <;> simp [x, hq, hq']
  have hy : ∀ i, y i ∈ B := by intro i; fin_cases i <;> simp [y, hq, hq']
  have hsum : ∑ i, x i = ∑ i, y i := by
    simp only [x, y, Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp only [fourSum] at h
    simp
    linear_combination h
  have himage := freimanHom8_fin_sum hf x y hx hy hsum
  simp only [x, y, Fin.sum_univ_succ, Fin.sum_univ_zero] at himage
  simp at himage
  unfold repFourValue
  linear_combination himage

/-- **The induced map agrees with every representation.** -/
theorem repMap_spec {N : Nat} {B : Finset (ZMod N)} {f : ZMod N → ZMod N}
    (hf : FreimanHom 8 B f) {q : Fin 4 → ZMod N} (hq : ∀ i, q i ∈ B) :
    repMap B f (fourSum q) = repFourValue f q := by
  have hrep : IsRepresented B (fourSum q) := ⟨q, hq, rfl⟩
  unfold repMap
  rw [dif_pos hrep]
  exact repFourValue_eq_of_fourSum_eq hf hrep.choose_spec.1 hq hrep.choose_spec.2

/-- **The induced map is Freiman-linear on represented points.** -/
theorem repMap_freimanLinear {N : Nat} {B : Finset (ZMod N)} {f : ZMod N → ZMod N}
    (hf : FreimanHom 8 B f) (D : Finset (ZMod N)) (hD : ∀ d ∈ D, IsRepresented B d) :
    IsFreimanLinearOn D (repMap B f) := by
  intro d₁ d₂ d₃ d₄ h₁ h₂ h₃ h₄ h
  obtain ⟨q₁, hq₁, rfl⟩ := hD d₁ h₁
  obtain ⟨q₂, hq₂, rfl⟩ := hD d₂ h₂
  obtain ⟨q₃, hq₃, rfl⟩ := hD d₃ h₃
  obtain ⟨q₄, hq₄, rfl⟩ := hD d₄ h₄
  rw [repMap_spec hf hq₁, repMap_spec hf hq₂, repMap_spec hf hq₃, repMap_spec hf hq₄]
  let x : Fin 8 → ZMod N := ![q₁ 0, q₁ 1, q₂ 0, q₂ 1, q₃ 2, q₃ 3, q₄ 2, q₄ 3]
  let y : Fin 8 → ZMod N := ![q₃ 0, q₃ 1, q₄ 0, q₄ 1, q₁ 2, q₁ 3, q₂ 2, q₂ 3]
  have hx : ∀ i, x i ∈ B := by intro i; fin_cases i <;> simp [x, hq₁, hq₂, hq₃, hq₄]
  have hy : ∀ i, y i ∈ B := by intro i; fin_cases i <;> simp [y, hq₁, hq₂, hq₃, hq₄]
  have hsum : ∑ i, x i = ∑ i, y i := by
    simp only [x, y, Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp only [fourSum] at h
    simp
    linear_combination h
  have himage := freimanHom8_fin_sum hf x y hx hy hsum
  simp only [x, y, Fin.sum_univ_succ, Fin.sum_univ_zero] at himage
  simp at himage
  unfold repFourValue
  linear_combination himage

end LeanProofs.GowersSzemeredi
