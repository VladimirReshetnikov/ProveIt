import OAI.Combinatorics.Progressions.Lattices.StablePrimeUpperComparison

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateCell_lcm_nonempty {ι σ : Type*} [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (q : ι → ℕ) (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base) :
    Nonempty (IntegerResidueBox lo (fun j => lo j + N j)
      (fun _ => (M.lcm (∏ i ∈ K, q i) : ℤ)) (fun j => (u.val j).val)) :=
  ⟨residuePrimeCoordinateCell_lcmEquiv lo N M a q hpair K base u u⟩

theorem selectedCombined_coprime_outside {ι : Type*} [DecidableEq ι]
    (q : ι → ℕ) (hpair : Pairwise (fun i j => (q i).Coprime (q j))) (M : ℕ) (K : Finset ι)
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (j : ι) (hj : j ∉ K) :
    (M.lcm (∏ i ∈ K, q i)).Coprime (q j) := by
  have hK : (∏ i ∈ K, q i).Coprime (q j) := by
    apply Nat.coprime_prod_left_iff.mpr
    intro i hi
    exact hpair (fun heq => hj (heq ▸ hi))
  exact Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul M _)
    (Nat.coprime_mul_iff_left.mpr ⟨hcop j hj, hK⟩)

theorem PrimeRefinementUpperBound.outside {ι σ : Type*} [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ}
    {M : ℕ} {q : ι → ℕ} {r : ℕ} {level ε δ : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    (hupper : PrimeRefinementUpperBound h g lo N M a q r level ε δ K base)
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (S : Finset {i // i ∉ K}) (hS : S.card ≤ r)
    (x : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))
    (hne : Nonempty (ResiduePrimeCoordinateCell lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) (fun i : {i // i ∉ K} => q i.val) S x)) :
    (residuePrimeCoordinateMean h lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) (fun i : {i // i ∉ K} => q i.val) S x).re ≤
      level * (residuePrimeCoordinateMean g lo N M a q K base).re + ε + level * δ := by
  classical
  let y := CoordinateDecisionTree.outsideAssignment K base x
  have hy : ∀ i ∈ K, y i = base i := by
    intro i hi
    simp only [y, CoordinateDecisionTree.outsideAssignment, hi, dite_true]
  have hout : (fun i : {i // i ∉ K} => y i.val) = x := by
    funext i
    simp only [y, CoordinateDecisionTree.outsideAssignment, i.property, dite_false]
  have hdis : Disjoint K (S.image Subtype.val) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨j, _, heq⟩ := Finset.mem_image.mp hj
    exact j.property (heq ▸ hi)
  have hcard : (S.image Subtype.val).card ≤ r := Finset.card_image_le.trans hS
  have hne' : Nonempty (ResiduePrimeCoordinateCell lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) (fun i : {i // i ∉ K} => q i.val) S (fun i => y i.val)) := by
    rw [hout]
    exact hne
  obtain ⟨v⟩ := hne'
  have hneOriginal : Nonempty (ResiduePrimeCoordinateCell lo N M a q (K ∪ S.image Subtype.val) y) :=
    ⟨(residuePrimeCoordinateOutsideEquiv lo N M a q hpair K base u S y hy).symm v⟩
  have hu := hupper (S.image Subtype.val) hdis hcard y hy hneOriginal
  rw [residuePrimeCoordinateMean_outside h lo N M a q hpair K base u S y hy, hout] at hu
  exact hu

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem ResiduePrimeCoordinateStable.outside_mean_close {ι σ : Type*} [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] {g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ}
    {M : ℕ} {q : ι → ℕ} {r : ℕ} {δ : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    (hstable : ResiduePrimeCoordinateStable g lo N M a q r δ K base)
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (S : Finset {i // i ∉ K}) (hS : S.card ≤ r)
    (x : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))
    (hne : Nonempty (ResiduePrimeCoordinateCell lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) (fun i : {i // i ∉ K} => q i.val) S x)) :
    ‖residuePrimeCoordinateMean g lo N M a q K base -
      residuePrimeCoordinateMean g lo N (M.lcm (∏ i ∈ K, q i))
        (fun j => (u.val j).val) (fun i : {i // i ∉ K} => q i.val) S x‖ ≤ δ := by
  classical
  let y := CoordinateDecisionTree.outsideAssignment K base x
  have hy : ∀ i ∈ K, y i = base i := by
    intro i hi
    simp only [y, CoordinateDecisionTree.outsideAssignment, hi, dite_true]
  have hout : (fun i : {i // i ∉ K} => y i.val) = x := by
    funext i
    simp only [y, CoordinateDecisionTree.outsideAssignment, i.property, dite_false]
  have hdis : Disjoint K (S.image Subtype.val) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨j, _, heq⟩ := Finset.mem_image.mp hj
    exact j.property (heq ▸ hi)
  have hcard : (S.image Subtype.val).card ≤ r := Finset.card_image_le.trans hS
  have hne' : Nonempty (ResiduePrimeCoordinateCell lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) (fun i : {i // i ∉ K} => q i.val) S (fun i => y i.val)) := by
    rw [hout]
    exact hne
  obtain ⟨v⟩ := hne'
  have hneOriginal : Nonempty (ResiduePrimeCoordinateCell lo N M a q (K ∪ S.image Subtype.val) y) :=
    ⟨(residuePrimeCoordinateOutsideEquiv lo N M a q hpair K base u S y hy).symm v⟩
  have hs := hstable (S.image Subtype.val) hdis hcard y hy hneOriginal
  rw [residuePrimeCoordinateMean_outside g lo N M a q hpair K base u S y hy, hout] at hs
  exact hs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem ResiduePrimeCoordinateStable.reference_density_close {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {r : ℕ} {δ : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    (hstable : ResiduePrimeCoordinateStable g lo N M a q r δ K base)
    (hM : 0 < M) (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (hcop : ∀ i ∉ K, M.Coprime (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ z ∈ translatedIntegerBox lo N, |(g z).re| ≤ C)
    (S : Finset {i // i ∉ K}) (hS : S.card ≤ r)
    (x : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))
    (hsmall : (∑ j, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) (M.lcm (∏ i ∈ K, q i)) ((u.val j).val)) < 1 / 2) :
    |productConditionalMean (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)) S
      (residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun j => (u.val j).val)
        (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
        (fun i : {i // i ∉ K} => q i.val) (fun z => (g z).re)) x -
          (residuePrimeCoordinateMean g lo N M a q K base).re| ≤
      δ + (2 * ∑ j, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo j) (lo j + N j) (M.lcm (∏ i ∈ K, q i)) ((u.val j).val)) * C := by
  have hQ : 0 < M.lcm (∏ i ∈ K, q i) :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero hM.ne'
      (Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (q i)))).ne')
  have hQcop : ∀ i : {i // i ∉ K}, (M.lcm (∏ k ∈ K, q k)).Coprime (q i.val) :=
    fun i => selectedCombined_coprime_outside q hpair M K hcop i.val i.property
  have hpair' : Pairwise (fun i j : {i // i ∉ K} => (q i.val).Coprime (q j.val)) :=
    fun i j hij => hpair (fun heq => hij (Subtype.ext heq))
  have hbase := residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u
  have hne := residuePrimeCoordinateCell_nonempty_of_small lo N (M.lcm (∏ i ∈ K, q i))
    (fun j => (u.val j).val) hbase (fun i : {i // i ∉ K} => q i.val) hQ hQcop hpair' S x hsmall
  have hs := hstable.outside_mean_close hpair u S hS x hne
  have hsre := (Complex.abs_re_le_norm _).trans hs
  rw [Complex.sub_re, abs_sub_comm] at hsre
  have he := residuePrimeCoordinateDensity_conditional_error lo N (M.lcm (∏ i ∈ K, q i))
    (fun j => (u.val j).val) hbase (fun i : {i // i ∉ K} => q i.val) hQ hQcop hpair'
    (fun z => (g z).re) C hC hg S x hsmall.le
  rw [← residuePrimeCoordinateMean_re] at he
  let v := (residuePrimeCoordinateMean g lo N M a q K base).re
  let G := (residuePrimeCoordinateMean g lo N (M.lcm (∏ i ∈ K, q i))
    (fun j => (u.val j).val) (fun i : {i // i ∉ K} => q i.val) S x).re
  let R := productConditionalMean
    (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)) S
    (residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun j => (u.val j).val)
      hbase (fun i : {i // i ∉ K} => q i.val) (fun z => (g z).re)) x
  change |G - v| ≤ δ at hsre
  change |R - G| ≤ _ at he
  change |R - v| ≤ _
  calc
    |R - v| = |(R - G) + (G - v)| := by congr 1; ring
    _ ≤ |R - G| + |G - v| := abs_add_le _ _
    _ ≤ _ := by linarith

end Erdos3

end

end OAI
