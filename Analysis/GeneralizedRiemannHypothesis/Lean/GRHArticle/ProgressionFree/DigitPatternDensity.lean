import GRHArticle.ProgressionFree.IndexedDensity
import GRHArticle.ProgressionFree.RankinTruncation
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Natural densities of truncated one-digit rules

At affected primes the exponent is uniquely encoded as `3 * h + c`. The
finite valuation-pattern density factors into the cap mass, the common
higher-digit weights, and the weights at the remaining tracked primes.
-/

open scoped BigOperators

namespace GRHArticle.ProgressionFree

private abbrev Digits (ι : Type*) := ZMod 3 × (ι → ZMod 3)

def digitVectorOf {ι : Type*} (e : Option ι → ℕ) : Digits ι :=
  (e none, fun i => e (some i))

private def digitAt {ι : Type*} (v : Digits ι) : Option ι → ZMod 3 :=
  fun o => o.elim v.1 v.2

private theorem digitAt_digitVectorOf {ι : Type*} (e : Option ι → ℕ) (o : Option ι) :
    digitAt (digitVectorOf e) o = (e o : ZMod 3) := by
  cases o <;> rfl

private theorem div_encoded_digit (h : ℕ) (c : ZMod 3) :
    (3 * h + c.val) / 3 = h := by
  have hc := ZMod.val_lt c
  omega

private theorem cast_encoded_digit (h : ℕ) (c : ZMod 3) :
    ((3 * h + c.val : ℕ) : ZMod 3) = c := by
  apply ZMod.val_injective 3
  rw [ZMod.val_natCast]
  have hc := ZMod.val_lt c
  omega

private abbrev PatternData (ι ρ : Type*) := Digits ι × ((Option ι → ℕ) × (ρ → ℕ))

private def encodePattern {ι ρ : Type*} (v : PatternData ι ρ) : Option ι ⊕ ρ → ℕ :=
  Sum.elim (fun o => 3 * v.2.1 o + (digitAt v.1 o).val) v.2.2

private theorem encodePattern_injective {ι ρ : Type*} :
    Function.Injective (encodePattern (ι := ι) (ρ := ρ)) := by
  intro a b hab
  have hi (o : Option ι) :
      3 * a.2.1 o + (digitAt a.1 o).val = 3 * b.2.1 o + (digitAt b.1 o).val :=
    congrFun hab (.inl o)
  have hc (o : Option ι) : digitAt a.1 o = digitAt b.1 o := by
    have h := congrArg (fun n : ℕ => (n : ZMod 3)) (hi o)
    simpa only [cast_encoded_digit] using h
  have hh (o : Option ι) : a.2.1 o = b.2.1 o := by
    have h := congrArg (fun n : ℕ => n / 3) (hi o)
    simpa only [div_encoded_digit] using h
  exact Prod.ext (Prod.ext (hc none) (funext fun i => hc (some i)))
    (Prod.ext (funext hh) (funext fun j => congrFun hab (.inr j)))

/-- Finite-prime truncation of a cap rule. At affected primes, the high part
of each exponent is less than `L`. Other tracked exponents are less than `3L`. -/
def finiteDigitRuleSet {ι ρ : Type*} (affected : Option ι → ℕ) (rough : ρ → ℕ)
    (C : Set (Digits ι)) (L : ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧ digitVectorOf (fun o => n.factorization (affected o)) ∈ C ∧
    (∀ o, n.factorization (affected o) / 3 ∈ greedyExponentsBelow L) ∧
    ∀ q, n.factorization (rough q) ∈ greedyExponentsBelow (3 * L)}

/-- The two products in the finite density that are independent of the cap. -/
noncomputable def digitRuleCommonWeight {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (affected : Option ι → ℕ) (rough : ρ → ℕ) (L : ℕ) : ℝ :=
  (∏ o, (1 - 1 / (affected o : ℝ)) *
    ∑ h ∈ greedyExponentsBelow L, (1 / (affected o : ℝ)) ^ (3 * h)) *
  (∏ q, (1 - 1 / (rough q : ℝ)) *
    ∑ e ∈ greedyExponentsBelow (3 * L), (1 / (rough q : ℝ)) ^ e)

/-- Exact density of a finite one-digit rule with disjoint affected and rough
prime coordinates. -/
theorem hasNaturalDensity_finiteDigitRuleSet {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (affected : Option ι → ℕ) (rough : ρ → ℕ) (C : Set (Digits ι)) (L : ℕ)
    (hinj : Function.Injective (Sum.elim affected rough))
    (hpa : ∀ o, (affected o).Prime) (hpr : ∀ q, (rough q).Prime) :
    HasNaturalDensity (finiteDigitRuleSet affected rough C L)
      (digitCapMass (1 / (affected none : ℝ)) (fun i => 1 / (affected (some i) : ℝ)) C *
        digitRuleCommonWeight affected rough L) := by
  classical
  let p : Option ι ⊕ ρ → ℕ := Sum.elim affected rough
  let D := Finset.univ.filter (· ∈ C)
  let H := Fintype.piFinset fun _ : Option ι => greedyExponentsBelow L
  let G := Fintype.piFinset fun _ : ρ => greedyExponentsBelow (3 * L)
  let enc : PatternData ι ρ ↪ ((Option ι ⊕ ρ) → ℕ) :=
    ⟨encodePattern, encodePattern_injective⟩
  let P := (D ×ˢ (H ×ˢ G)).map enc
  have hset : {n | n ≠ 0 ∧ (fun j => n.factorization (p j)) ∈ P} =
      finiteDigitRuleSet affected rough C L := by
    ext n
    constructor
    · rintro ⟨hn, hP⟩
      obtain ⟨⟨c, h, g⟩, hmem, he⟩ := Finset.mem_map.mp hP
      obtain ⟨hcD, hhg⟩ := Finset.mem_product.mp hmem
      obtain ⟨hhH, hgG⟩ := Finset.mem_product.mp hhg
      have ha (o : Option ι) :
          n.factorization (affected o) = 3 * h o + (digitAt c o).val :=
        (congrFun he (.inl o)).symm
      have hb (q : ρ) : n.factorization (rough q) = g q := (congrFun he (.inr q)).symm
      have hc (o : Option ι) : (n.factorization (affected o) : ZMod 3) = digitAt c o := by
        rw [ha, cast_encoded_digit]
      have hC : digitVectorOf (fun o => n.factorization (affected o)) = c :=
        Prod.ext (hc none) (funext fun i => hc (some i))
      refine ⟨hn, hC.symm ▸ (Finset.mem_filter.mp hcD).2, ?_, ?_⟩
      · intro o
        rw [ha, div_encoded_digit]
        exact Fintype.mem_piFinset.mp hhH o
      · intro q
        rw [hb]
        exact Fintype.mem_piFinset.mp hgG q
    · rintro ⟨hn, hc, hh, hg⟩
      let c := digitVectorOf (fun o => n.factorization (affected o))
      let h (o : Option ι) := n.factorization (affected o) / 3
      let g (q : ρ) := n.factorization (rough q)
      refine ⟨hn, Finset.mem_map.mpr ⟨(c, h, g), Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, Finset.mem_product.mpr
          ⟨Fintype.mem_piFinset.mpr hh, Fintype.mem_piFinset.mpr hg⟩⟩, ?_⟩⟩
      funext j
      cases j with
      | inl o =>
        change 3 * h o + (digitAt c o).val = n.factorization (affected o)
        simp only [c, h, digitAt_digitVectorOf, ZMod.val_natCast]
        omega
      | inr q => rfl
  have hprime (j : Option ι ⊕ ρ) : (p j).Prime := by
    cases j with
    | inl o => exact hpa o
    | inr q => exact hpr q
  have hD := hasNaturalDensity_indexedValuationPatterns p hinj hprime P
  rw [hset] at hD
  let Wd (c : Digits ι) := digitWeight (1 / (affected none : ℝ))
    (fun i => 1 / (affected (some i) : ℝ)) c
  let Wa (h : Option ι → ℕ) :=
    ∏ o, (1 - 1 / (affected o : ℝ)) * (1 / (affected o : ℝ)) ^ (3 * h o)
  let Wg (g : ρ → ℕ) := ∏ q, (1 - 1 / (rough q : ℝ)) * (1 / (rough q : ℝ)) ^ g q
  have hdigit (c : Digits ι) :
      Wd c = ∏ o : Option ι, (1 / (affected o : ℝ)) ^ (digitAt c o).val := by
    rw [Fintype.prod_option]
    rfl
  have hsplit (c : Digits ι) (h : Option ι → ℕ) :
      (∏ o, (1 - 1 / (affected o : ℝ)) *
        (1 / (affected o : ℝ)) ^ (3 * h o + (digitAt c o).val)) = Wd c * Wa h := by
    simp only [hdigit, Wa, ← Finset.prod_mul_distrib]
    exact Fintype.prod_congr _ _ fun o => by rw [pow_add]; ac_rfl
  have hweight (v : PatternData ι ρ) :
      (∏ j, (1 - 1 / (p j : ℝ)) * (1 / (p j : ℝ)) ^ enc v j) =
        Wd v.1 * (Wa v.2.1 * Wg v.2.2) := by
    rw [Fintype.prod_sum_type]
    change (∏ o : Option ι, (1 - 1 / (affected o : ℝ)) *
      (1 / (affected o : ℝ)) ^ (3 * v.2.1 o + (digitAt v.1 o).val)) * Wg v.2.2 = _
    rw [hsplit, mul_assoc]
  have ha_sum : (∑ h ∈ H, Wa h) = ∏ o, (1 - 1 / (affected o : ℝ)) *
      ∑ h ∈ greedyExponentsBelow L, (1 / (affected o : ℝ)) ^ (3 * h) := by
    dsimp only [H, Wa]
    rw [← Finset.prod_univ_sum (fun _ : Option ι => greedyExponentsBelow L)
      (fun o h => (1 - 1 / (affected o : ℝ)) * (1 / (affected o : ℝ)) ^ (3 * h))]
    simp only [Finset.mul_sum]
  have hg_sum : (∑ g ∈ G, Wg g) = ∏ q, (1 - 1 / (rough q : ℝ)) *
      ∑ e ∈ greedyExponentsBelow (3 * L), (1 / (rough q : ℝ)) ^ e := by
    dsimp only [G, Wg]
    rw [← Finset.prod_univ_sum (fun _ : ρ => greedyExponentsBelow (3 * L))
      (fun q e => (1 - 1 / (rough q : ℝ)) * (1 / (rough q : ℝ)) ^ e)]
    simp only [Finset.mul_sum]
  have hmass :
      (∑ e ∈ P, ∏ j, (1 - 1 / (p j : ℝ)) * (1 / (p j : ℝ)) ^ e j) =
        (∑ c ∈ D, Wd c) * ((∑ h ∈ H, Wa h) * (∑ g ∈ G, Wg g)) := by
    unfold P
    rw [Finset.sum_map]
    simp_rw [Finset.sum_product, hweight, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hmass, ha_sum, hg_sum] at hD
  exact hD

end GRHArticle.ProgressionFree
