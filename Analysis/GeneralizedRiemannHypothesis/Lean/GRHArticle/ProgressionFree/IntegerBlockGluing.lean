import GRHArticle.ProgressionFree.IntegerDensityExtrema
import GRHArticle.ProgressionFree.DensityBounds

/-!
# Gluing separated integer windows

Taking only the upper portion of each selected prefix keeps the asymptotic
proportion. Fast-growing cutoffs prevent triples involving several windows.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical

/-- The union of the pieces of `A j` in the selected windows `(L j,N j]`. -/
def integerBlockUnion (L N : ℕ → ℕ) (A : ℕ → Set ℕ) : Set ℕ :=
  {n | ∃ j, n ∈ A j ∧ L j < n ∧ n ≤ N j}

theorem zero_not_mem_integerBlockUnion (L N : ℕ → ℕ) (A : ℕ → Set ℕ) :
    0 ∉ integerBlockUnion L N A := by
  rintro ⟨j, _, hj, _⟩
  omega

/-- The two degree-two separation inequalities prevent triples spanning
multiple integer windows, for either ratio convention. -/
theorem integerBlockUnion_admissible {integral : Bool} {L N : ℕ → ℕ}
    {A : ℕ → Set ℕ} (hA : ∀ j, IntegerPrefixAdmissible integral (A j))
    (hsep : ∀ ⦃i j⦄, i < j → (N i)^2 ≤ L j ∧ N i * N j ≤ (L j)^2) :
    IntegerPrefixAdmissible integral (integerBlockUnion L N A) := by
  intro a b c ha hb hc hab hbc he hd
  obtain ⟨i, ha, hai, haN⟩ := ha
  obtain ⟨j, hb, hbj, hbN⟩ := hb
  obtain ⟨k, hc, hck, hcN⟩ := hc
  have horder {u v r s : ℕ} (hu : L r < u) (hv : v ≤ N s) (huv : u < v) : r ≤ s := by
    by_contra! h
    have hs := (hsep h).1
    have hsq : N s ≤ (N s)^2 := by
      by_cases hz : N s = 0
      · simp [hz]
      · rw [pow_two]
        calc
          N s = 1 * N s := (one_mul _).symm
          _ ≤ N s * N s := Nat.mul_le_mul_right (N s) (Nat.pos_of_ne_zero hz)
    omega
  have hij := horder hai hbN hab
  have hjk := horder hbj hcN hbc
  have hjk' : j = k := by
    by_contra hne
    have hlt := lt_of_le_of_ne hjk hne
    have hs : b*b ≤ (N j)^2 := by rw [pow_two]; exact Nat.mul_le_mul hbN hbN
    have hca : c ≤ a*c := by
      calc
        c = 1*c := (one_mul _).symm
        _ ≤ a*c := Nat.mul_le_mul_right c (Nat.succ_le_of_lt (Nat.zero_lt_of_lt hai))
    rw [he] at hca
    exact hck.not_ge (hca.trans (hs.trans (hsep hlt).1))
  subst k
  have hij' : i = j := by
    by_contra hne
    have hlt := lt_of_le_of_ne hij hne
    have hlt' : (L j)^2 < b*b := by
      rw [pow_two]
      exact (Nat.mul_le_mul_left (L j) hbj.le).trans_lt
        (Nat.mul_lt_mul_of_pos_right hbj (Nat.zero_lt_of_lt hbj))
    have hle := (Nat.mul_le_mul haN hcN).trans (hsep hlt).2
    rw [he] at hle
    exact hlt'.not_ge hle
  subst j
  exact hA i ha hb hc hab hbc he hd

private theorem integerBlock_separation {p N D : ℕ} (hD : 0 < D)
    (hN : 2*D^2*(p+1)^2 ≤ N) : p^2 ≤ N/D ∧ p*N ≤ (N/D)^2 := by
  let L := N/D
  have hlo : 2*D*(p+1)^2 ≤ L := by
    apply (Nat.le_div_iff_mul_le hD).mpr
    calc
      _ = 2*D^2*(p+1)^2 := by ring
      _ ≤ _ := hN
  have hD2 : 1 ≤ 2*D := by omega
  have hpp : p^2 ≤ (p+1)^2 := by
    rw [pow_two, pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hpp' : p+1 ≤ (p+1)^2 := by
    rw [pow_two]
    simpa only [one_mul] using Nat.mul_le_mul_right (p+1) (show 1 ≤ p+1 by omega)
  have hLpos : 0 < L := Nat.zero_lt_of_lt (by
    have hOne : 1 ≤ (p+1)^2 := (Nat.succ_le_succ (Nat.zero_le p)).trans hpp'
    exact lt_of_lt_of_le (by omega : 0 < 1) (hOne.trans
      ((by simpa only [one_mul] using Nat.mul_le_mul_right ((p+1)^2) hD2 : _ ≤ 2*D*(p+1)^2).trans hlo)))
  have hprod : 2*D*p ≤ L :=
    (Nat.mul_le_mul_left (2*D) ((Nat.le_succ p).trans hpp')).trans hlo
  have hN' : N ≤ 2*L*D := by
    have hcap : N < (L+1)*D := (Nat.div_lt_iff_lt_mul hD).mp (Nat.lt_succ_self L)
    exact hcap.le.trans (Nat.mul_le_mul_right D (by omega))
  refine ⟨hpp.trans ((by simpa only [one_mul] using Nat.mul_le_mul_right ((p+1)^2) hD2 :
    (p+1)^2 ≤ 2*D*(p+1)^2).trans hlo), ?_⟩
  calc
    p*N ≤ p*(2*L*D) := Nat.mul_le_mul_left p hN'
    _ = (2*D*p)*L := by ring
    _ ≤ L^2 := by rw [pow_two]; exact Nat.mul_le_mul_right L hprod

private theorem densityUpTo_le_prefix (N L : ℕ) :
    densityUpTo {n | n ≤ L} N ≤ (L : ℝ) / N := by
  have hc : countUpTo {n | n ≤ L} N ≤ L := by
    calc
      _ ≤ (Icc 1 L).card := by
        unfold countUpTo
        apply card_le_card
        intro n hn
        simp only [mem_filter, mem_Icc, Set.mem_setOf_eq] at hn ⊢
        exact ⟨hn.1.1, hn.2⟩
      _ = L := by rw [Nat.card_Icc, add_tsub_cancel_right]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg N)

/-- Arbitrarily large admissible prefixes at density approaching `d` can be
glued to one admissible set with upper density at least `d`. -/
theorem exists_integerBlockUnion_limsup_ge_of_arbitrarily_large_prefix
    (integral : Bool) (d : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ, ∃ N ≥ N₀, ∃ A : Set ℕ,
      IntegerPrefixAdmissible integral A ∧ d - ε ≤ densityUpTo A N) :
    ∃ A : Set ℕ, 0 ∉ A ∧ IntegerPrefixAdmissible integral A ∧
      d ≤ integerUpperDensity A := by
  let err (j : ℕ) := ((j : ℝ)+2)⁻¹
  have herr (j : ℕ) : 0 < err j := by dsimp [err]; positivity
  choose pick hpick sets hAdm hProp using fun j m : ℕ ↦ h (err j) (herr j) m
  let B : ℕ → ℕ := Nat.rec 1 (fun j m ↦
    2*(j+3)^2*(pick j m+1)^2 + pick j m+1)
  let N (j : ℕ) := pick j (B j)
  let A (j : ℕ) := sets j (B j)
  let L (j : ℕ) := N j/(j+2)
  have h₀ : 1 ≤ N 0 := hpick 0 1
  have hstep (j : ℕ) : 2*(j+3)^2*(N j+1)^2 + N j+1 ≤ N (j+1) := hpick (j+1) (B (j+1))
  have hNat : StrictMono N := strictMono_nat_of_lt_succ (fun j ↦ by have := hstep j; omega)
  have hNpos (j : ℕ) : 0 < N j := h₀.trans (hNat.monotone (Nat.zero_le j))
  have hsep ⦃i j : ℕ⦄ (hij : i < j) : (N i)^2 ≤ L j ∧ N i*N j ≤ (L j)^2 := by
    cases j with
    | zero => omega
    | succ j =>
      have hprev : N i ≤ N j := hNat.monotone (Nat.le_of_lt_succ hij)
      have hs := hstep j
      have hlarge : 2*(j+3)^2*(N j+1)^2 ≤ N (j+1) := by omega
      have ⟨h₁,h₂⟩ := integerBlock_separation (show 0 < j+3 by omega) hlarge
      change (N i)^2 ≤ N (j+1)/(j+3) ∧ N i*N (j+1) ≤ (N (j+1)/(j+3))^2
      exact ⟨(by rw [pow_two,pow_two]; exact Nat.mul_le_mul hprev hprev : (N i)^2 ≤ (N j)^2) |>.trans h₁,
        (Nat.mul_le_mul_right _ hprev).trans h₂⟩
  let U := integerBlockUnion L N A
  refine ⟨U, zero_not_mem_integerBlockUnion _ _ _, integerBlockUnion_admissible
    (fun j ↦ hAdm j (B j)) (fun ⦃_ _⦄ h ↦ hsep h), ?_⟩
  have hsample (j : ℕ) : d - err j - err j ≤ densityUpTo U (N j) := by
    have hsub : densityUpTo (A j) (N j) ≤ densityUpTo (U ∪ {n | n ≤ L j}) (N j) := by
      apply densityUpTo_le_of_subset_on_cutoff (N j)
      intro n hn ha
      by_cases hL : L j < n
      · exact Or.inl ⟨j, ha, hL, (mem_Icc.mp hn).2⟩
      · exact Or.inr (Nat.le_of_not_gt hL)
    have hlow : (L j : ℝ)/(N j : ℝ) ≤ err j := by
      have hd : (0:ℝ) < (j:ℝ)+2 := by positivity
      have hn : 0 < (N j : ℝ) := by exact_mod_cast hNpos j
      dsimp only [err]
      rw [← one_div, div_le_div_iff₀ hn hd, one_mul]
      exact_mod_cast Nat.div_mul_le_self (N j) (j+2)
    linarith only [hProp j (B j), hsub.trans (densityUpTo_union_le U {n | n ≤ L j} (N j)),
      (densityUpTo_le_prefix (N j) (L j)).trans hlow]
  have hlimErr : Tendsto err atTop (𝓝 0) := by
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun n : ℕ ↦ 1/((↑(n+1):ℝ)+1)) atTop (𝓝 0) at ht
    simpa only [err, Nat.cast_add, Nat.cast_one, add_assoc, one_div,
      show (1:ℝ)+1 = 2 by norm_num] using ht
  have hlim : Tendsto (fun j ↦ d - err j - err j) atTop (𝓝 d) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hlimErr).sub hlimErr
  exact le_integerUpperDensity_of_tendsto_le hNat.tendsto_atTop hlim
    (Eventually.of_forall hsample)

/-- A sequence of local admissible prefix counts gives a lower bound for the
extremum over actual infinite sets. -/
theorem le_integerUpperDensitySupremum_of_arbitrarily_large_prefix
    (integral : Bool) (d : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ, ∃ N ≥ N₀, ∃ A : Set ℕ,
      IntegerPrefixAdmissible integral A ∧ d - ε ≤ densityUpTo A N) :
    d ≤ integerUpperDensitySupremum integral := by
  obtain ⟨A, h0, hA, hd⟩ := exists_integerBlockUnion_limsup_ge_of_arbitrarily_large_prefix integral d h
  exact hd.trans (le_integerUpperDensitySupremum h0 hA)

end GRHArticle.ProgressionFree
