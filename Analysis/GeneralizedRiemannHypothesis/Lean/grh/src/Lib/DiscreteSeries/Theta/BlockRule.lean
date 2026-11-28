import Lib.DiscreteSeries.Theta.FockDualPair

/-!
# The block rule for corresponding parameters

The block rule compares two discrete series parameters at one place through their shifted entries.
This file proves that it is equivalent to matching for the oscillator pair, that it is kept by a
swap, a negation and a shift, and gives its form for a pair with one character. In the code all
entries are doubled, so that they are integers.

Notions from other files:
* `HCParam s`: an integer vector l = 2λ indexed by the domain of the signs s; `toHCParam s l` is l
  read as such a vector.
* `HasGap h`: the entries of l are distinct, of the parity of n − 1 for n entries, and those of
  opposite signs differ by at least 2h.
* `FockDualPair.std t s γ δ`: the oscillator pair with rows for the signs t, columns for the signs
  s, row shift γ and column shift δ + n' for n' rows (the constants added on the diagonal).
* `IsMatch`: both parameters have gap 500(n+n')³ and each row and each column is either matched,
  with a sign condition, or lies in the central range left by the difference of the ranks.
* `centredParam`: the entry of a row less twice the row shift, plus the number of columns; `swap`
  exchanges rows and columns.
* `IsMatchedPair`: the centred entries of a row and a column are opposite, and their signs times the
  centred row entry exceed the absolute difference of the ranks.

## Relation to the literature

Known result: the shape of the theta correspondence of discrete series parameters. Only statements
about the parameters, as integer vectors, are proved here. Sources: J.-S. Li, Theta lifting for
unitary representations with nonzero cohomology, Duke Math. J. 61 (1990); A. Paul, First occurrence
for the dual pairs (U(p,q), U(r,s)), Canad. J. Math. 51 (1999), 636–657.
-/

noncomputable section

namespace New

open Fintype Finset

/-- The block [d] = ((d−1)/2, (d−3)/2, …, (1−d)/2), with its entries doubled. -/
def doubledBlock (d : ℕ) : Finset ℤ :=
  (range d).image fun b : ℕ ↦ (d : ℤ) - 1 - 2 * b

/-- The block e + [d] of length d and centre e, with its entries doubled. -/
def centredBlock (e : ℤ) (d : ℕ) : Finset ℤ :=
  (doubledBlock d).image fun x : ℤ ↦ 2 * e + x

/-- Twice the entries of a parameter λ, l = 2λ, shifted by minus the weight of the other space's
character: for m the rank of the other space and γ = wt χ + m/2 this is l − 2γ + m. -/
def shiftedEntry {ι : Type} (γ : ℤ) (m : ℕ) (l : ι → ℤ) (i : ι) : ℤ :=
  l i - 2 * γ + m

/-- The block rule at one place, for spaces S, T of ranks n, n' with signs s, t, parameters
l = 2λ, l' = 2λ', and γ = wt χ_S + n/2, γ' = wt χ_T + n'/2. It compares the entries of λ shifted
by −wt χ_T with those of λ' shifted by −wt χ_S. -/
structure IsBlockRule {n n' : Type} [Fintype n] [Fintype n'] {s : n → ℤˣ} {t : n' → ℤˣ}
    (γ γ' : ℤ) (l : HCParam s) (l' : HCParam t) : Prop where
  /-- λ has distinct entries in (n−1)/2 + ℤ, and those of opposite signs differ by at least
  500(n+n')³. -/
  hasGap_left : l.HasGap (500 * (card n + card n') ^ 3)
  /-- λ' has distinct entries in (n'−1)/2 + ℤ, and those of opposite signs differ by at least
  500(n+n')³. -/
  hasGap_right : l'.HasGap (500 * (card n + card n') ^ 3)
  /-- If n ≤ n', the shifted entries for T are those for S together with the block [n'−n]. -/
  entries_of_le : card n ≤ card n' →
    univ.image (shiftedEntry γ (card n) l') =
      univ.image (shiftedEntry γ' (card n') l) ∪ doubledBlock (card n' - card n)
  /-- If n' ≤ n, the shifted entries for S are those for T together with the block [n−n']. -/
  entries_of_ge : card n' ≤ card n →
    univ.image (shiftedEntry γ' (card n') l) =
      univ.image (shiftedEntry γ (card n) l') ∪ doubledBlock (card n - card n')
  /-- A positive shifted entry that occurs on both spaces has the same sign on S and T. -/
  sign_of_pos : ∀ (c : n) (r : n'), shiftedEntry γ' (card n') l c = shiftedEntry γ (card n) l' r →
    0 < shiftedEntry γ' (card n') l c → s c = t r
  /-- A negative shifted entry that occurs on both spaces has opposite signs on S and T. -/
  sign_of_neg : ∀ (c : n) (r : n'), shiftedEntry γ' (card n') l c = shiftedEntry γ (card n) l' r →
    shiftedEntry γ' (card n') l c < 0 → s c = -t r

/-- The points of (d−1)/2 + ℤ of modulus below d/2 form [d]; here all is doubled. -/
lemma mem_doubledBlock {d : ℕ} {x : ℤ} :
    x ∈ doubledBlock d ↔ |x| < d ∧ Even (x + d - 1) := by
  simp only [doubledBlock, Finset.mem_image, Finset.mem_range, abs_lt, Int.even_iff]
  refine ⟨?_, fun hx ↦ ⟨(((d : ℤ) - 1 - x) / 2).toNat, by omega, by omega⟩⟩
  rintro ⟨b, hb, rfl⟩
  omega

lemma mem_centredBlock {e y : ℤ} {d : ℕ} :
    y ∈ centredBlock e d ↔ ∃ b : ℕ, b < d ∧ y = 2 * e + d - 1 - 2 * b := by
  simp only [centredBlock, doubledBlock, Finset.image_image, Finset.mem_image, Finset.mem_range,
    Function.comp_apply]
  exact exists_congr fun b ↦ and_congr_right fun _ ↦ by omega

lemma card_doubledBlock (d : ℕ) : (doubledBlock d).card = d := by
  rw [doubledBlock, card_image_of_injective _ fun a b hab ↦ by simpa using hab, card_range]

lemma card_centredBlock (e : ℤ) (d : ℕ) : (centredBlock e d).card = d := by
  rw [centredBlock, Finset.card_image_of_injective _ (add_right_injective _), card_doubledBlock]

/-- Negation sends the block e + [d] to the block −e + [d]. -/
lemma image_neg_centredBlock (e : ℤ) (d : ℕ) :
    (centredBlock e d).image Neg.neg = centredBlock (-e) d := by
  ext y
  simp only [Finset.mem_image, mem_centredBlock]
  constructor
  · rintro ⟨x, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨d - 1 - b, by omega, by omega⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨2 * e + d - 1 - 2 * (d - 1 - b : ℕ), ⟨d - 1 - b, by omega, rfl⟩, by omega⟩

/-- For a natural number d, signs u, v and an integer y: u v y > d says that |y| > d and that
u v is the sign of y. -/
lemma lt_sign_mul_iff {d : ℕ} {u v : ℤˣ} {y : ℤ} :
    (d : ℤ) < (u * v : ℤˣ) * y ↔
      (d : ℤ) < |y| ∧ (0 < y → v = u) ∧ (y < 0 → v = -u) := by
  -- In each of the four cases u v y is y or −y.
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
    simp [lt_abs] <;> omega

/-- From the block rule to matching, for vectors a on C and b on R with distinct entries, where R
has d more elements than C. Suppose three things: the entries of b have the parity of d − 1; they
are those of a together with those of `doubledBlock d` = {d−1, d−3, …, 1−d} (the block [d],
doubled); and whenever a_c = b_r, s_c = t_r if this entry is positive and s_c = −t_r if it is
negative. Then each b_r either equals some a_c with t_r s_c b_r > d or has |b_r| < d, and each a_c
equals some b_r with t_r s_c b_r > d. -/
lemma exists_matched_of_entries_eq {C R : Type} [Fintype C] [Fintype R] {s : C → ℤˣ}
    {t : R → ℤˣ} {a : C → ℤ} {b : R → ℤ} {d : ℕ} (hcard : card R = card C + d)
    (ha : a.Injective) (hb : b.Injective) (hparity : ∀ r : R, Even (b r + d - 1))
    (hentries : univ.image b = univ.image a ∪ doubledBlock d)
    (hpos : ∀ (c : C) (r : R), a c = b r → 0 < a c → s c = t r)
    (hneg : ∀ (c : C) (r : R), a c = b r → a c < 0 → s c = -t r) :
    (∀ r : R, (∃ c : C, b r = a c ∧ (d : ℤ) < (t r * s c : ℤˣ) * b r) ∨ |b r| < d) ∧
      ∀ c : C, ∃ r : R, b r = a c ∧ (d : ℤ) < (t r * s c : ℤˣ) * b r := by
  have hdisjoint : Disjoint (univ.image a) (doubledBlock d) := by
    rw [← card_union_eq_card_add_card, ← hentries]
    simp [card_image_of_injective, ha, hb, card_doubledBlock, hcard]
  have hmatched (c : C) (r : R) (heq : a c = b r) :
      b r = a c ∧ (d : ℤ) < (t r * s c : ℤˣ) * b r := by
    have hnot : b r ∉ doubledBlock d := by
      rw [← heq]
      exact Finset.disjoint_left.1 hdisjoint (Finset.mem_image_of_mem a (mem_univ c))
    -- The modulus has the parity of d − 1 and is not below d, so it exceeds d.
    have houtside : (d : ℤ) < |b r| := by
      grind [mem_doubledBlock, hparity r, lt_abs, abs_lt]
    exact ⟨heq.symm, lt_sign_mul_iff.2 ⟨houtside, fun h ↦ hpos c r heq (h.trans_eq heq.symm),
      fun h ↦ hneg c r heq (heq.trans_lt h)⟩⟩
  refine ⟨fun r ↦ ?_, fun c ↦ ?_⟩
  · have hr : b r ∈ univ.image a ∪ doubledBlock d :=
      hentries.subset (Finset.mem_image_of_mem b (mem_univ r))
    simp only [mem_union, Finset.mem_image, mem_univ, true_and, mem_doubledBlock] at hr
    exact hr.imp (fun ⟨c, hc⟩ ↦ ⟨c, hmatched c r hc⟩) And.left
  · obtain ⟨r, -, hr⟩ := Finset.mem_image.1
      (hentries.superset (Finset.mem_union_left _ (Finset.mem_image_of_mem a (mem_univ c))))
    exact ⟨r, hmatched c r hr.symm⟩

/-- From matching to the block rule, for vectors a on C and b on R, where R has d more elements
than C and b has distinct entries of the parity of d − 1. Suppose that each entry of b is equal to
one of a with t s b > d or has modulus below d, and each entry of a is equal to one of b with
t s b > d. Then the entries of b are those of a together with the block [d], and a common entry
has equal signs if it is positive, opposite ones if it is negative. -/
lemma entries_eq_of_exists_matched {C R : Type} [Fintype C] [Fintype R] {s : C → ℤˣ}
    {t : R → ℤˣ} {a : C → ℤ} {b : R → ℤ} {d : ℕ} (hcard : card R = card C + d)
    (hb : b.Injective) (hparity : ∀ r : R, Even (b r + d - 1))
    (hrows : ∀ r : R, (∃ c : C, b r = a c ∧ (d : ℤ) < (t r * s c : ℤˣ) * b r) ∨ |b r| < d)
    (hcols : ∀ c : C, ∃ r : R, b r = a c ∧ (d : ℤ) < (t r * s c : ℤˣ) * b r) :
    univ.image b = univ.image a ∪ doubledBlock d ∧
      (∀ (c : C) (r : R), a c = b r → 0 < a c → s c = t r) ∧
      ∀ (c : C) (r : R), a c = b r → a c < 0 → s c = -t r := by
  have hsub : univ.image b ⊆ univ.image a ∪ doubledBlock d := fun x hx ↦ by
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hx
    grind [mem_doubledBlock, hparity r, hrows r]
  have hcount : (univ.image a ∪ doubledBlock d).card ≤ (univ.image b).card := by
    grw [card_union_le, card_image_le]
    simp [card_image_of_injective, hb, card_doubledBlock, hcard]
  have hsign (c : C) (r : R) (heq : a c = b r) :
      (0 < b r → s c = t r) ∧ (b r < 0 → s c = -t r) := by
    obtain ⟨r', hr', hlt⟩ := hcols c
    obtain rfl : r' = r := hb (hr'.trans heq)
    exact (lt_sign_mul_iff.1 hlt).2
  exact ⟨Finset.eq_of_subset_of_card_le hsub hcount,
    fun c r heq h ↦ (hsign c r heq).1 (h.trans_eq heq),
    fun c r heq h ↦ (hsign c r heq).2 (heq.symm.trans_lt h)⟩

section BlockRule
variable {n n' : Type} [Fintype n] [Fintype n'] {s : n → ℤˣ} {t : n' → ℤˣ}
  {γ γ' : ℤ} {l : HCParam s} {l' : HCParam t}

/-- The shifted entries of a parameter with a gap are distinct. -/
lemma shiftedEntry_injective {g : ℕ} (hl : l.HasGap g) (m : ℕ) :
    (shiftedEntry γ' m l).Injective :=
  fun x y hxy ↦ hl.injective (by simpa [shiftedEntry] using hxy)

/-- If the space of λ has rank n = m + d, then its entries shifted for a space of rank m lie in
(d−1)/2 + ℤ, that is, the doubled entries have the parity of d − 1. -/
lemma even_shiftedEntry_add_sub_one {g : ℕ} (hl : l.HasGap g) {m d : ℕ} (hd : card n = m + d)
    (c : n) : Even (shiftedEntry γ' m l c + d - 1) := by
  grind [shiftedEntry, hl.parity c]

omit [Fintype n] in
/-- The centred column parameter of −λ for the oscillator pair is minus the shifted entry. -/
lemma centredParam_swap_std (c : n) :
    (FockDualPair.std t s γ (-γ')).swap.centredParam (-l) c =
      -shiftedEntry γ' (card n') l c := by
  simp only [shiftedEntry, FockDualPair.centredParam, Pi.neg_apply]
  ring

/-- For the oscillator pair with rows for T and columns for S, a row r of λ' and a column c of −λ
are matched if and only if the doubled shifted entries agree and t_r s_c times them exceeds
|n'−n|. -/
lemma isMatchedPair_std_iff (r : n') (c : n) :
    IsMatchedPair (.std t s γ (-γ')) l' (-l) r c ↔
      shiftedEntry γ (card n) l' r = shiftedEntry γ' (card n') l c ∧
        |(card n' : ℤ) - card n| < (t r * s c : ℤˣ) * shiftedEntry γ (card n) l' r := by
  rw [IsMatchedPair, centredParam_swap_std, neg_neg]
  simp [FockDualPair.centredParam, pairSign, shiftedEntry]

/-- λ' and −λ match for the oscillator pair (`IsMatch`) if and only if both have gap 500(n+n')³,
each doubled shifted entry of λ' is matched with one of λ or has modulus below n'−n, and each
doubled shifted entry of λ is matched with one of λ' or has modulus below n−n'. -/
lemma isMatch_std_iff :
    IsMatch (.std t s γ (-γ')) l' (-l) ↔
      l.HasGap (500 * (card n + card n') ^ 3) ∧
      l'.HasGap (500 * (card n + card n') ^ 3) ∧
      (∀ r : n', (∃ c : n, shiftedEntry γ (card n) l' r = shiftedEntry γ' (card n') l c ∧
          |(card n' : ℤ) - card n| < (t r * s c : ℤˣ) * shiftedEntry γ (card n) l' r) ∨
        |shiftedEntry γ (card n) l' r| < (card n' : ℤ) - card n) ∧
      ∀ c : n, (∃ r : n', shiftedEntry γ (card n) l' r = shiftedEntry γ' (card n') l c ∧
          |(card n' : ℤ) - card n| < (t r * s c : ℤˣ) * shiftedEntry γ (card n) l' r) ∨
        |shiftedEntry γ' (card n') l c| < (card n : ℤ) - card n' := by
  have hrow (r : n') : FockDualPair.centredParam (.std t s γ (-γ')) l' r =
      shiftedEntry γ (card n) l' r := rfl
  constructor
  · intro h
    exact ⟨by simpa [neg_neg, add_comm] using h.hasGap_column.neg,
      by simpa [add_comm] using h.hasGap_row,
      fun r ↦ by simpa only [isMatchedPair_std_iff, hrow] using h.left r,
      fun c ↦ by simpa only [isMatchedPair_std_iff, centredParam_swap_std, abs_neg] using h.right c⟩
  · intro ⟨hgap, hgap', hrows, hcols⟩
    exact ⟨by simpa [add_comm] using hgap', by simpa [add_comm] using hgap.neg,
      fun r ↦ by simpa only [isMatchedPair_std_iff, hrow] using hrows r,
      fun c ↦ by simpa only [isMatchedPair_std_iff, centredParam_swap_std, abs_neg] using hcols c⟩

/-- If λ', −λ match for the oscillator pair of (T, S), then λ, −λ' match for that of (S, T). -/
lemma IsMatch.std_symm (h : IsMatch (.std t s γ (-γ')) l' (-l)) :
    IsMatch (.std s t γ' (-γ)) l (-l') := by
  obtain ⟨hgap, hgap', hrows, hcols⟩ := isMatch_std_iff.1 h
  refine isMatch_std_iff.2 ⟨by simpa [add_comm] using hgap', by simpa [add_comm] using hgap,
    fun c ↦ (hcols c).imp_left ?_, fun r ↦ (hrows r).imp_left ?_⟩
  · rintro ⟨r, heq, hlt⟩
    exact ⟨r, heq.symm, by rwa [abs_sub_comm, mul_comm (s c), ← heq]⟩
  · rintro ⟨c, heq, hlt⟩
    exact ⟨c, heq.symm, by rwa [abs_sub_comm, mul_comm (s c), ← heq]⟩

/-- The block rule is symmetric: for spaces S, T of ranks n, n' with signs s, t, parameters l = 2λ,
l' = 2λ', and γ = wt χ_S + n/2, γ' = wt χ_T + n'/2, if `IsBlockRule γ γ' l l'` holds then so does
`IsBlockRule γ' γ l' l`, with the roles of the two spaces exchanged. -/
theorem IsBlockRule.symm (h : IsBlockRule γ γ' l l') : IsBlockRule γ' γ l' l where
  hasGap_left := by simpa [add_comm] using h.hasGap_right
  hasGap_right := by simpa [add_comm] using h.hasGap_left
  entries_of_le := h.entries_of_ge
  entries_of_ge := h.entries_of_le
  sign_of_pos r c heq hr := (h.sign_of_pos c r heq.symm (hr.trans_eq heq)).symm
  sign_of_neg r c heq hr := by rw [h.sign_of_neg c r heq.symm (heq.symm.trans_lt hr), neg_neg]

/-- If n ≤ n' and λ', −λ match for the oscillator pair, then each column c is matched with a row r:
the doubled shifted entries agree, and t_r s_c times them exceeds n'−n. -/
lemma IsMatch.exists_row_of_le (h : IsMatch (.std t s γ (-γ')) l' (-l)) (hle : card n ≤ card n')
    (c : n) :
    ∃ r : n', shiftedEntry γ (card n) l' r = shiftedEntry γ' (card n') l c ∧
      |(card n' : ℤ) - card n| < (t r * s c : ℤˣ) * shiftedEntry γ (card n) l' r := by
  obtain ⟨-, -, -, hcols⟩ := isMatch_std_iff.1 h
  have hdiff : (card n : ℤ) - card n' ≤ 0 := by omega
  exact (hcols c).resolve_right (hdiff.trans (abs_nonneg _)).not_gt

/-- The case n ≤ n' of `isBlockRule_iff_isMatch`: the block rule holds if and only if λ' and −λ
match for the oscillator pair with rows for T and columns for S. -/
lemma isBlockRule_iff_isMatch_of_le (hle : card n ≤ card n') :
    IsBlockRule γ γ' l l' ↔ IsMatch (.std t s γ (-γ')) l' (-l) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  have hdiff : (card n' : ℤ) - card n = d := by omega
  constructor
  · intro h
    have hentries : univ.image (shiftedEntry γ (card n) l') =
        univ.image (shiftedEntry γ' (card n') l) ∪ doubledBlock d := by
      simpa [hd] using h.entries_of_le hle
    obtain ⟨hrows, hcols⟩ :=
      exists_matched_of_entries_eq hd (shiftedEntry_injective h.hasGap_left _)
        (shiftedEntry_injective h.hasGap_right _) (even_shiftedEntry_add_sub_one h.hasGap_right hd)
        hentries h.sign_of_pos h.sign_of_neg
    exact isMatch_std_iff.2 ⟨h.hasGap_left, h.hasGap_right, fun r ↦ by simpa [hdiff] using hrows r,
      fun c ↦ Or.inl (by simpa [hdiff] using hcols c)⟩
  · intro h
    obtain ⟨hgap, hgap', hrows, -⟩ := isMatch_std_iff.1 h
    obtain ⟨hentries, hpos, hneg⟩ :=
      entries_eq_of_exists_matched hd (shiftedEntry_injective hgap' _)
        (even_shiftedEntry_add_sub_one hgap' hd) (fun r ↦ by simpa [hdiff] using hrows r)
        (fun c ↦ by simpa [hdiff] using h.exists_row_of_le hle c)
    refine ⟨hgap, hgap', fun _ ↦ by simpa [hd] using hentries, fun hge ↦ ?_, hpos, hneg⟩
    -- For equal ranks the block is empty.
    have hzero : d = 0 := by omega
    simpa [hzero, Nat.sub_eq_zero_of_le hle, doubledBlock] using hentries.symm

/-- Parameters λ, λ' on (S, T) satisfy the block rule for γ, γ' if and only if λ', −λ match for the
oscillator pair with rows for T and columns for S. -/
theorem isBlockRule_iff_isMatch :
    IsBlockRule γ γ' l l' ↔ IsMatch (.std t s γ (-γ')) l' (-l) := by
  -- Both sides are symmetric in the two spaces.
  rcases le_total (card n) (card n') with hle | hge
  · exact isBlockRule_iff_isMatch_of_le hle
  · exact ⟨fun h ↦ ((isBlockRule_iff_isMatch_of_le hge).1 h.symm).std_symm,
      fun h ↦ ((isBlockRule_iff_isMatch_of_le hge).2 h.std_symm).symm⟩

/-- The block rule `IsBlockRule γ γ' l l'` is stated for spaces S, T of ranks n, n' with signs s, t,
doubled parameters l = 2λ, l' = 2λ', and γ = wt χ_S + n/2, γ' = wt χ_T + n'/2. It compares the
entries of λ shifted by −wt χ_T with those of λ' shifted by −wt χ_S. If it holds, then −λ, −λ'
satisfy it on (S⁻, T) for n − γ, n' − γ', that is, for the inverse characters: shifted entries and
the signs of S are negated. Here S⁻ is S with all signs negated, and `toHCParam s l` is l read as a
parameter for the signs s. -/
theorem IsBlockRule.neg (h : IsBlockRule γ γ' l l') :
    IsBlockRule (card n - γ) (card n' - γ') (toHCParam (-s) (-l)) (toHCParam t (-l')) := by
  have hneg {ι : Type} (δ : ℤ) (m : ℕ) (f : ι → ℤ) :
      shiftedEntry ((m : ℤ) - δ) m (-f) = Neg.neg ∘ shiftedEntry δ m f := by
    funext i
    grind [shiftedEntry, Pi.neg_apply]
  have hblock (d : ℕ) : (doubledBlock d).image Neg.neg = doubledBlock d := by
    simpa [centredBlock] using image_neg_centredBlock 0 d
  have hgap : (toHCParam (-s) (-l)).HasGap (500 * (card n + card n') ^ 3) :=
    { h.hasGap_left.neg with gap := fun i j hij ↦ h.hasGap_left.neg.gap i j fun hs ↦ hij (congrArg
      Neg.neg hs) }
  refine ⟨hgap, h.hasGap_right.neg, ?_, ?_, ?_, ?_⟩
  all_goals simp only [toHCParam, hneg]
  · intro hle
    rw [← image_image, ← image_image, h.entries_of_le hle, image_union, hblock]
  · intro hle
    rw [← image_image, ← image_image, h.entries_of_ge hle, image_union, hblock]
  · intro c r heq hc
    simp [h.sign_of_neg c r (by simpa using heq) (by simpa using hc)]
  · intro c r heq hc
    simp [h.sign_of_pos c r (by simpa using heq) (by simpa using hc)]

/-- The block rule is unchanged when all signs are reversed. Here `l` and `l'` are doubled
Harish-Chandra parameters (l = 2λ, l' = 2λ') for the signs `s` and `t`. The block rule
`IsBlockRule γ γ'` compares the entries of λ shifted by −wt χ_T with those of λ' shifted by −wt χ_S,
where γ = wt χ_S + n/2 and γ' = wt χ_T + n'/2. The claim: if `l`, `l'` satisfy the block rule, then
the same integer vectors, regarded via `toHCParam` as parameters for the signs `-s` and `-t`,
satisfy it for the same `γ`, `γ'`. -/
theorem IsBlockRule.neg_signs (h : IsBlockRule γ γ' l l') :
    IsBlockRule γ γ' (toHCParam (-s) l) (toHCParam (-t) l') := by
  simpa only [toHCParam, sub_sub_cancel, neg_neg] using h.neg.symm.neg.symm

/-- If γ and γ' are raised by integers u and u', then λ + u' and λ' + u still satisfy the block
rule: the shifted entries do not change. -/
theorem IsBlockRule.shift (h : IsBlockRule γ γ' l l') (u u' : ℤ) :
    IsBlockRule (γ + u) (γ' + u') (toHCParam s fun c : n ↦ l c + 2 * u')
      (toHCParam t fun r : n' ↦ l' r + 2 * u) := by
  have hshift {ι : Type} (δ v : ℤ) (m : ℕ) (f : ι → ℤ) :
      shiftedEntry (δ + v) m (fun i : ι ↦ f i + 2 * v) = shiftedEntry δ m f := by
    funext i
    grind [shiftedEntry]
  have hgap {ι : Type} [Fintype ι] {ε : ι → ℤˣ} {f : HCParam ε} {g : ℕ} (hf : f.HasGap g) (v : ℤ) :
      (toHCParam ε fun i : ι ↦ f i + 2 * v).HasGap g :=
    { injective := fun i j hij ↦ hf.injective (by simpa using hij)
      parity := fun i ↦ by grind [hf.parity i]
      gap := fun i j hij ↦ by simpa using hf.gap i j hij }
  refine ⟨hgap h.hasGap_left u', hgap h.hasGap_right u, ?_, ?_, ?_, ?_⟩
  all_goals simp only [toHCParam, hshift]
  exacts [h.entries_of_le, h.entries_of_ge, h.sign_of_pos, h.sign_of_neg]

/-- If the block rule holds with n ≤ n', no shifted entry of λ is zero: it is matched with one of
λ', and a matched entry is nonzero. -/
lemma IsBlockRule.shiftedEntry_ne_zero (h : IsBlockRule γ γ' l l') (hle : card n ≤ card n')
    (c : n) : shiftedEntry γ' (card n') l c ≠ 0 := by
  intro hzero
  obtain ⟨r, hr, hlt⟩ := (isBlockRule_iff_isMatch.1 h).exists_row_of_le hle c
  rw [hr, hzero, mul_zero] at hlt
  exact (abs_nonneg _).not_gt hlt

/-- The block rule for n ≤ n', recentred at an integer e, with offsets p = n − 2γ + 2e and
p' = n' − 2γ' + 2e: both parameters have gap 500(n+n')³, the entries l' + p are the l + p'
together with the doubled entries of the block e + [n'−n], and where an l c + p' equals an
l' r + p, the signs of c and r differ exactly if this number is below 2e. -/
theorem isBlockRule_iff_of_offsets {e p p' : ℤ} (hle : card n ≤ card n')
    (hp : (card n : ℤ) - 2 * γ = p - 2 * e) (hp' : (card n' : ℤ) - 2 * γ' = p' - 2 * e) :
    IsBlockRule γ γ' l l' ↔
      l.HasGap (500 * (card n + card n') ^ 3) ∧
      l'.HasGap (500 * (card n + card n') ^ 3) ∧
      univ.image (fun r : n' ↦ l' r + p) =
        univ.image (fun c : n ↦ l c + p') ∪
          centredBlock e (card n' - card n) ∧
      ∀ (c : n) (r : n'), l c + p' = l' r + p → (s c ≠ t r ↔ l c + p' < 2 * e) := by
  have hrow (r : n') : l' r + p = 2 * e + shiftedEntry γ (card n) l' r := by grind [shiftedEntry]
  have hcol (c : n) : l c + p' = 2 * e + shiftedEntry γ' (card n') l c := by grind [shiftedEntry]
  have himage {ι : Type} [Fintype ι] (f : ι → ℤ) :
      univ.image (fun i : ι ↦ 2 * e + f i) = (univ.image f).image (fun x : ℤ ↦ 2 * e + x) :=
    Finset.image_image.symm
  -- After a translation by 2e these are the conditions on the shifted entries.
  simp only [hrow, hcol, himage, centredBlock, ← Finset.image_union, add_right_inj,
    add_lt_iff_neg_left, (Finset.image_injective (add_right_injective (2 * e))).eq_iff]
  constructor
  · intro h
    refine ⟨h.hasGap_left, h.hasGap_right, h.entries_of_le hle, fun c r heq ↦
      ⟨fun hne ↦ ?_, fun hlt ↦ Int.units_ne_iff_eq_neg.2 (h.sign_of_neg c r heq hlt)⟩⟩
    by_contra hnot
    exact hne (h.sign_of_pos c r heq ((not_lt.1 hnot).lt_of_ne' (h.shiftedEntry_ne_zero hle c)))
  · intro ⟨hgap, hgap', hentries, hsign⟩
    refine ⟨hgap, hgap', fun _ ↦ hentries, fun hge ↦ ?_,
      fun c r heq hc ↦ not_not.1 fun hne ↦ hc.not_gt ((hsign c r heq).1 hne),
      fun c r heq hc ↦ Int.units_ne_iff_eq_neg.1 ((hsign c r heq).2 hc)⟩
    simpa [le_antisymm hle hge, doubledBlock] using hentries.symm

/-- The block rule (`IsBlockRule`) for n ≤ n' when γ = e + ⌊n/2⌋ and γ' = e + ⌊n'/2⌋, as for
characters whose weights for spaces of ranks n, n' are e less the fractional parts of n/2, n'/2. It
holds iff four conditions hold. The doubled parameters l = 2λ, l' = 2λ' have gap 500(n+n')³
(distinct entries ≡ card − 1 mod 2, |λ i − λ j| ≥ gap when signs differ). The entries l' + (n mod 2)
are the l + (n' mod 2) together with `centredBlock e (n'−n)`, the doubled entries of the block of
length n'−n centred at e. A column c and a row r with a common entry have s c ≠ t r exactly if it is
below 2e. -/
theorem isBlockRule_iff_of_character {e : ℤ} (hle : card n ≤ card n')
    (hγ : γ = e + (card n : ℤ) / 2) (hγ' : γ' = e + (card n' : ℤ) / 2) :
    IsBlockRule γ γ' l l' ↔
      l.HasGap (500 * (card n + card n') ^ 3) ∧
      l'.HasGap (500 * (card n + card n') ^ 3) ∧
      univ.image (fun r : n' ↦ l' r + (card n : ℤ) % 2) =
        univ.image (fun c : n ↦ l c + (card n' : ℤ) % 2) ∪
          centredBlock e (card n' - card n) ∧
      ∀ (c : n) (r : n'), l c + (card n' : ℤ) % 2 = l' r + (card n : ℤ) % 2 →
        (s c ≠ t r ↔ l c + (card n' : ℤ) % 2 < 2 * e) :=
  isBlockRule_iff_of_offsets hle (by omega) (by omega)

/-- The block rule for n ≤ n' when γ = e + ⌈n/2⌉ and γ' = e + ⌈n'/2⌉, as for characters whose
weights for spaces of ranks n, n' are e plus the fractional parts of n/2, n'/2. It holds iff three
conditions hold. First, both parameters have gap 500(n+n')³. Second, the entries of l' − (n mod 2)
are those of l − (n' mod 2) together with those of `centredBlock e (n'−n)` = {2e + d−1, 2e + d−3, …,
2e + 1−d} for d = n'−n (the block e + [d], doubled). Third, whenever l_c − (n' mod 2) = l'_r − (n
mod 2), s_c ≠ t_r exactly if this common entry is below 2e. -/
theorem isBlockRule_iff_of_character_conj {e : ℤ} (hle : card n ≤ card n')
    (hγ : γ = e + ((card n : ℤ) + 1) / 2) (hγ' : γ' = e + ((card n' : ℤ) + 1) / 2) :
    IsBlockRule γ γ' l l' ↔
      l.HasGap (500 * (card n + card n') ^ 3) ∧
      l'.HasGap (500 * (card n + card n') ^ 3) ∧
      univ.image (fun r : n' ↦ l' r - (card n : ℤ) % 2) =
        univ.image (fun c : n ↦ l c - (card n' : ℤ) % 2) ∪
          centredBlock e (card n' - card n) ∧
      ∀ (c : n) (r : n'), l c - (card n' : ℤ) % 2 = l' r - (card n : ℤ) % 2 →
        (s c ≠ t r ↔ l c - (card n' : ℤ) % 2 < 2 * e) := by
  have hp : (card n : ℤ) - 2 * γ = -((card n : ℤ) % 2) - 2 * e := by omega
  have hp' : (card n' : ℤ) - 2 * γ' = -((card n' : ℤ) % 2) - 2 * e := by omega
  simpa only [sub_eq_add_neg] using isBlockRule_iff_of_offsets (l := l) (l' := l') hle hp hp'

end BlockRule

end New

end
