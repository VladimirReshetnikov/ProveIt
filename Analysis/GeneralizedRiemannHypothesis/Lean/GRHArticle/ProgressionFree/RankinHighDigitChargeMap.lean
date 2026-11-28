import GRHArticle.ProgressionFree.RankinDigitCharges

/-!
# Charging bad high digits to missing greedy vectors

The unused member of a greedy predecessor pair has a reciprocal weight
that can be charged by a binary ternary mask. Each charged point can be
recovered from the missing vector, the mask, and the choice of predecessor.
-/

namespace GRHArticle.ProgressionFree

/-- Coordinatewise Rankin exponents. -/
def rankinExponentVectors (ι : Type*) : Set (ι → ℕ) :=
  {v | ∀ i, v i ∈ greedyExponents}

/-- A greedy mask containing at least one nonzero digit above its cut. -/
def rankinHighDigitMasks {ι : Type*} (k : ι → ℕ) : Set (ι → ℕ) :=
  {v | v ∈ rankinExponentVectors ι ∧ ∃ i, 0 < v i/3^(k i)}

/-- The admitted vectors with at least one forbidden high digit. -/
def rankinBadHighVectors {ι : Type*} (k : ι → ℕ) (F : Set (ι → ℕ)) : Set (ι → ℕ) :=
  {v | v ∈ F ∧ ∃ i, v i / 3^(k i) ∉ greedyExponents}

/-- A bad high digit forces a missing greedy vector at one or two mask steps. -/
theorem exists_missing_rankinVector_of_badHigh {ι : Type*} (k : ι → ℕ)
    {F : Set (ι → ℕ)} (hF : ThreeAPFree F) {v : ι → ℕ} (hv : v ∈ rankinBadHighVectors k F) :
    ∃ (a : ↥(rankinExponentVectors ι \ F)) (e : Fin 2) (d : ↥(rankinHighDigitMasks k)),
      ∀ i, v i = a.val i + (e.val+1)*d.val i := by
  classical
  have h (i : ι) := exists_greedy_digitCharge (v i)
  let a (i : ι) := (h i).choose
  let d (i : ι) := (h i).choose_spec.choose
  have hD (i : ι) := (h i).choose_spec.choose_spec
  have he (j : ι) : a j+2*d j = v j := (hD j).1
  have ha : a ∈ rankinExponentVectors ι := fun i ↦ (hD i).2.1
  have hb : a+d ∈ rankinExponentVectors ι := fun i ↦ (hD i).2.2.1
  obtain ⟨i,hi⟩ := hv.2
  have hDi : 0 < d i/3^(k i) := ((hD i).2.2.2.2 (k i)).mp hi
  have hd : d ∈ rankinHighDigitMasks k := ⟨fun j ↦ (hD j).2.2.2.1,i,hDi⟩
  by_cases hA : a ∈ F
  · have hB : a+d ∉ F := by
      intro hB
      have hMid : a+v = (a+d)+(a+d) := by
        funext j
        change a j + v j = (a j+d j)+(a j+d j)
        rw [← he j]
        omega
      have he' := congrFun (hF hA hB hv.1 hMid) i
      change a i = a i+d i at he'
      have he₀ : d i = 0 := by omega
      rw [he₀,Nat.zero_div] at hDi
      omega
    refine ⟨⟨a+d,hb,hB⟩,0,⟨d,hd⟩,fun j ↦ ?_⟩
    change v j = (a j+d j)+(0+1)*d j
    have := he j
    omega
  · exact ⟨⟨a,ha,hA⟩,1,⟨d,hd⟩,fun j ↦ (he j).symm⟩

/-- The charge map is injective because the recorded data recover the
charged exponent vector. -/
noncomputable def rankinHighDigitChargeEmbedding {ι : Type*} (k : ι → ℕ)
    {F : Set (ι → ℕ)} (hF : ThreeAPFree F) :
    ↥(rankinBadHighVectors k F) ↪ ↥(rankinExponentVectors ι \ F) × Fin 2 × ↥(rankinHighDigitMasks k) where
  toFun v :=
    let h := exists_missing_rankinVector_of_badHigh k hF v.property
    (h.choose,h.choose_spec.choose,h.choose_spec.choose_spec.choose)
  inj' v w he := by
    let hv := exists_missing_rankinVector_of_badHigh k hF v.property
    let hw := exists_missing_rankinVector_of_badHigh k hF w.property
    apply Subtype.ext
    funext i
    have h₁ := hv.choose_spec.choose_spec.choose_spec i
    have h₂ := hw.choose_spec.choose_spec.choose_spec i
    rw [h₁,h₂]
    exact congrArg (fun a : ↥(rankinExponentVectors ι \ F) × Fin 2 × ↥(rankinHighDigitMasks k) ↦
      a.1.val i+(a.2.1.val+1)*a.2.2.val i) he

/-- Recover the charged vector coordinatewise from its recorded data. -/
theorem rankinHighDigitChargeEmbedding_apply {ι : Type*} (k : ι → ℕ)
    {F : Set (ι → ℕ)} (hF : ThreeAPFree F) (v : ↥(rankinBadHighVectors k F)) (i : ι) :
    let p := rankinHighDigitChargeEmbedding k hF v
    v.val i = p.1.val i + (p.2.1.val+1)*p.2.2.val i :=
  (exists_missing_rankinVector_of_badHigh k hF v.property).choose_spec.choose_spec.choose_spec i

end GRHArticle.ProgressionFree
