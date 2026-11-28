import GRHArticle.SingularModuli.ConjugateDisks

/-!
# Full minimum support from factorial valuation sums across the degree

The interval test in `smd:lem:criterion` applies to integral elements over
arbitrary coefficient fields admitting the indicated p-adic embeddings.
-/

namespace GRHArticle.SingularModuli

variable {p : ℕ} [hp : Fact p.Prime] {b : ℚ}

/-- Factorial weights telescope over consecutive integers, including the
empty interval. -/
theorem factorialWeight_add_sub_eq_intervalSum (u d : ℕ) :
    factorialWeight p b (u+d) - factorialWeight p b u =
      b*d - ∑ j ∈ Finset.range d, (padicValNat p (u+j+1) : ℚ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ]
    simp only [factorialWeight] at ih ⊢
    rw [Nat.add_succ, Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _)]
    push_cast at ih ⊢
    linarith only [ih]

/-- The root cutoff takes its smallest possible value exactly when every
interval crossing the degree has valuation sum below depth times length. -/
theorem sparseDiskRootBound_eq_pred_iff_intervals {h : ℕ} (hh : 0 < h)
    (hb : 1 / ((p:ℚ)-1) < b) :
    sparseDiskRootBound p h b hh hb = h-1 ↔
      ∀ u d : ℕ, u < h → h ≤ u+d →
        (∑ j ∈ Finset.range d, (padicValNat p (u+j+1) : ℚ)) < b*d := by
  let B := sparseDiskRootBound p h b hh hb
  have hB := isGreatest_sparseDiskRootBound (p := p) hh hb
  have hlo : h-1 ≤ B := hB.2 ⟨⟨h-1, by omega⟩,le_rfl⟩
  constructor
  · intro he u d hu hd
    have hlt : B < u+d := by dsimp [B]; omega
    have hw := factorialWeight_lt_of_gt_greatest hB hlt ⟨u,hu⟩
    change factorialWeight p b u < factorialWeight p b (u+d) at hw
    linarith only [hw, factorialWeight_add_sub_eq_intervalSum (p := p) (b := b) u d]
  · intro hint
    change B = h-1
    apply le_antisymm _ hlo
    by_contra! hn
    obtain ⟨i,hi⟩ := hB.1
    change factorialWeight p b B ≤ factorialWeight p b i at hi
    have hcut : h ≤ B := by omega
    have hi' := i.isLt
    have he : i.val + (B-i.val) = B := by omega
    have hv := hint i.val (B-i.val) hi' (by omega)
    have hw := factorialWeight_add_sub_eq_intervalSum (p := p) (b := b) i.val (B-i.val)
    rw [he] at hw
    linarith only [hi,hw,hv]

/-- It suffices to check the intervals ending at the degree and the
intervals beginning right after it. -/
theorem factorialWeight_crossing_of_oneSided {h : ℕ}
    (hleft : ∀ u < h, (∑ j ∈ Finset.range (h-u), (padicValNat p (u+j+1) : ℚ)) < b*(h-u:ℕ))
    (hright : ∀ d : ℕ, 0 < d → (∑ j ∈ Finset.range d, (padicValNat p (h+j+1) : ℚ)) < b*d)
    (u d : ℕ) (hu : u < h) (hd : h ≤ u+d) :
    (∑ j ∈ Finset.range d, (padicValNat p (u+j+1) : ℚ)) < b*d := by
  have h₁ := factorialWeight_add_sub_eq_intervalSum (p := p) (b := b) u (h-u)
  rw [Nat.add_sub_of_le hu.le] at h₁
  have h₂ : factorialWeight p b h ≤ factorialWeight p b (u+d) := by
    rcases hd.eq_or_lt with he | hlt
    · rw [he]
    · have h₃ := factorialWeight_add_sub_eq_intervalSum (p := p) (b := b) h (u+d-h)
      rw [Nat.add_sub_of_le hd] at h₃
      linarith only [h₃, hright (u+d-h) (by omega)]
  linarith only [h₁,h₂, hleft u hu, factorialWeight_add_sub_eq_intervalSum (p := p) (b := b) u d]

/-- A verified crossing condition and a full disk of distinct conjugates
force maximal minimum support, with no degree bound on the annihilator. -/
theorem minimumSupport_eq_degree_add_one_of_intervalSums
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra K ℂ_[p]]
    {x : L} (hx : IsIntegral K x) (hb : 1 / ((p:ℚ)-1) < b)
    (a : ℂ_[p]) (ha : a ≠ 0) (σ : Fin (minpoly K x).natDegree → L →ₐ[K] ℂ_[p])
    (hinj : Function.Injective fun i ↦ σ i x)
    (hdisk : ∀ i, ‖σ i x/a-1‖ ≤ (p:ℝ)^(-(b:ℝ)))
    (hcross : ∀ u d : ℕ, u < (minpoly K x).natDegree → (minpoly K x).natDegree ≤ u+d →
      (∑ j ∈ Finset.range d, (padicValNat p (u+j+1) : ℚ)) < b*d) :
    minimumSupport hx = (minpoly K x).natDegree+1 := by
  have hh := minpoly.natDegree_pos hx
  have he := (sparseDiskRootBound_eq_pred_iff_intervals hh hb).mpr hcross
  have hn := not_hasSparseAnnihilator_of_padic_conjugates hh hb x a ha σ hinj hdisk (by omega)
  have hlow := mt (minimumSupport_le_iff hx _).mp hn
  exact le_antisymm (minimumSupport_le_natDegree_add_one hx) (by omega)

end GRHArticle.SingularModuli
