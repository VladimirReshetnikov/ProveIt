import Lib.DiscreteSeries.Theta.BlockRule

/-!
# Inserting a block into a parameter

The parameters of all chains and grids of spaces are built in one way. There are a stem and a finite
set C of centres, each with a length and a kind, down or up. For B ⊆ C the vector λ⁺_B consists of
the stem and the blocks c + [l_c], c ∈ B, and the sign of an entry is −1 to the power of the number
of centres outside B that are down and above it or up and below it. The parameter λ_B is λ⁺_B
lowered by ½ or by 0, as the parity of the rank requires. Everything is at one infinite place, and
entries are doubled.

* `New.CentreSystem`, `New.CentreSystem.IsSeparated`, `New.CentreSystem.IsParam`: the data, the
  conditions on parities and distances, and the parameter λ_B on a space with these signs, up to a
  common sign σ.
* `New.CentreSystem.IsParam.isBlockRule_insert_of_down`,
  `New.CentreSystem.IsParam.isBlockRule_neg_insert_of_up`: the parameters before and after the
  insertion of a block correspond (`New.IsBlockRule`): the parameters themselves for a down centre,
  their negatives for an up centre.

Notions from other files:
* `HCParam s`: integer vectors l = 2λ indexed by the coordinates of a space with signs s.
* `HCParam.HasGap l h`: the entries of λ are distinct and lie in (n − 1)/2 + ℤ, n the rank, and
  entries at coordinates of opposite signs are at least h apart.
* `centredBlock e d`: the doubled entries of e + [d], where [d] = ((d−1)/2, (d−3)/2, …, (1−d)/2).
* `IsBlockRule γ γ' l l'`, for spaces of ranks n, n': both parameters have a large gap; after
  shifting λ by n'/2 − γ' and λ' by n/2 − γ, the longer one is the shorter one together with a block
  centred at 0; and the two coordinates of a common shifted entry have equal signs if the entry is
  positive and opposite signs if it is negative.
-/

namespace New

open Fintype Finset

/-- A stem and a finite set of centres at one place. Each centre has a value, a length and a kind,
down or up. The entries of the stem are doubled; the values of the centres are not. -/
structure CentreSystem (ι : Type) where
  /-- The finite set C of centres. -/
  centres : Finset ι
  /-- The value of a centre. -/
  centre : ι → ℤ
  /-- The length of the block that belongs to a centre. -/
  length : ι → ℕ
  /-- The kind of a centre: `true` for up, `false` for down. -/
  isUp : ι → Bool
  /-- The doubled entries of the stem. -/
  stem : Finset ℤ

namespace CentreSystem

section Definitions

variable {ι : Type} [DecidableEq ι] (X : CentreSystem ι)

/-- The doubled entries of the block c + [l_c], centred at the value of c and of length l_c. -/
def block (c : ι) : Finset ℤ := centredBlock (X.centre c) (X.length c)

/-- The doubled entries of λ⁺_B: the stem and the blocks of the centres in B. -/
def entries (B : Finset ι) : Finset ℤ := X.stem ∪ B.biUnion X.block

/-- The rank n_B: the length of the stem plus the lengths of the blocks in B. -/
def rank (B : Finset ι) : ℕ := #X.stem + ∑ c ∈ B, X.length c

/-- The doubled difference of λ⁺_B and λ_B: it is 1 if the length of the stem and #B are odd, and
0 otherwise. -/
def lowering (B : Finset ι) : ℤ := if Odd #X.stem ∧ Odd #B then 1 else 0

/-- The centre c counts for the doubled entry y: it is down and above y/2, or up and below y/2. -/
def CountsFor (c : ι) (y : ℤ) : Prop :=
  if X.isUp c then 2 * X.centre c < y else y < 2 * X.centre c

instance (c : ι) (y : ℤ) : Decidable (X.CountsFor c y) := by
  unfold CountsFor
  infer_instance

/-- The sign of the doubled entry y of λ⁺_B: it is −1 exactly if an odd number of the centres
outside B count for y. -/
def sign (B : Finset ι) (y : ℤ) : ℤˣ := (-1) ^ #{c ∈ X.centres \ B | X.CountsFor c y}

/-- All lengths have one parity, the stem lies in ½ + ℤ or in ℤ as they are even or odd, and each
centre c is at a distance of at least (h + l_c)/2 from the stem and from the other blocks. -/
structure IsSeparated (h : ℕ) : Prop where
  /-- The blocks have lengths of the same parity as the stem. -/
  length_mod_two : ∀ c ∈ X.centres, X.length c % 2 = #X.stem % 2
  /-- The doubled entries of the stem are odd if its length is even, and even if it is odd. -/
  odd_add_card : ∀ y ∈ X.stem, Odd (y + #X.stem)
  /-- The centres are far from the stem. -/
  stem_far : ∀ c ∈ X.centres, ∀ y ∈ X.stem, (h + X.length c : ℤ) ≤ |y - 2 * X.centre c|
  /-- The centres are far from the blocks of the other centres. -/
  block_far : ∀ c ∈ X.centres, ∀ c' ∈ X.centres, c' ≠ c →
    ∀ y ∈ X.block c', (h + X.length c : ℤ) ≤ |y - 2 * X.centre c|

/-- The vector l lists 2λ_B on a space of rank n_B, whose signs are those of the entries of λ⁺_B
times the common sign σ. -/
structure IsParam (B : Finset ι) (σ : ℤˣ) {n : Type} [Fintype n] {s : n → ℤˣ} (l : HCParam s) :
    Prop where
  /-- The space has rank n_B. -/
  card_eq : card n = X.rank B
  /-- Before the lowering the entries are those of λ⁺_B. -/
  image_eq : univ.image (fun x : n ↦ l x + X.lowering B) = X.entries B
  /-- The sign of a coordinate is σ times the sign of its entry. -/
  sign_eq : ∀ x : n, s x = σ * X.sign B (l x + X.lowering B)

end Definitions

/-- Dropping centres keeps the separation: if `X` is separated with gap h, then so is the system
with the same data and a subset C of the centres. -/
lemma IsSeparated.subset {ι : Type} {X : CentreSystem ι} {h : ℕ} (hX : X.IsSeparated h)
    {C : Finset ι} (hC : C ⊆ X.centres) : IsSeparated { X with centres := C } h where
  length_mod_two c hc := hX.length_mod_two c (hC hc)
  odd_add_card := hX.odd_add_card
  stem_far c hc := hX.stem_far c (hC hc)
  block_far c hc c' hc' := hX.block_far c (hC hc) c' (hC hc')

variable {ι : Type} [DecidableEq ι] {X : CentreSystem ι} {h : ℕ} {B : Finset ι} {c : ι} {y : ℤ}

lemma entries_insert : X.entries (insert c B) = X.entries B ∪ X.block c := by
  rw [entries, entries, biUnion_insert, union_comm (X.block c), union_assoc]

lemma rank_insert (hcB : c ∉ B) : X.rank (insert c B) = X.rank B + X.length c := by
  rw [rank, rank, sum_insert hcB, add_comm (X.length c), add_assoc]

/-- Inserting the block of a centre c outside B changes the sign of the doubled entry y exactly if
c counts for y (it is down and above y/2, or up and below y/2). -/
lemma sign_eq_ite_sign_insert (hc : c ∈ X.centres) (hcB : c ∉ B) :
    X.sign B y = if X.CountsFor c y then -X.sign (insert c B) y else X.sign (insert c B) y := by
  have h_missing : X.centres \ B = insert c (X.centres \ insert c B) := by
    rw [sdiff_insert, insert_erase (mem_sdiff.2 ⟨hc, hcB⟩)]
  rw [sign, sign, h_missing, filter_insert]
  split_ifs
  · rw [card_insert_of_notMem (by simp), pow_succ, mul_neg_one]
  · rfl

omit [DecidableEq ι] in
/-- In a system with separation h, a centre c outside B is at a distance of at least (h + l_c)/2
from every entry y/2 of λ⁺_B (the stem and the blocks of the centres in B). -/
lemma IsSeparated.add_length_le_abs_sub_two_mul_centre (hX : X.IsSeparated h) (hB : B ⊆ X.centres)
    (hc : c ∈ X.centres) (hcB : c ∉ B) (hy : y ∈ X.entries B) :
    (h + X.length c : ℤ) ≤ |y - 2 * X.centre c| := by
  obtain hy_stem | hy_blocks := mem_union.1 hy
  · exact hX.stem_far c hc y hy_stem
  · obtain ⟨c', hc'B, hy_block⟩ := mem_biUnion.1 hy_blocks
    exact hX.block_far c hc c' (hB hc'B) (ne_of_mem_of_not_mem hc'B hcB) y hy_block

omit [DecidableEq ι] in
/-- In a separated system the block of a centre c outside B is disjoint from the entries of
λ⁺_B. -/
lemma IsSeparated.disjoint_entries_block (hX : X.IsSeparated h) (hB : B ⊆ X.centres)
    (hc : c ∈ X.centres) (hcB : c ∉ B) : Disjoint (X.entries B) (X.block c) := by
  refine disjoint_left.2 fun y hy_entries hy_block ↦ ?_
  have h_far : (h + X.length c : ℤ) ≤ |y - 2 * X.centre c| :=
    hX.add_length_le_abs_sub_two_mul_centre hB hc hcB hy_entries
  obtain ⟨b, hb, hy⟩ : ∃ b < X.length c, y = 2 * X.centre c + X.length c - 1 - 2 * b :=
    mem_centredBlock.1 hy_block
  grind

/-- In a separated system the stem and the blocks of the centres in B are pairwise disjoint, so the
number of entries of λ⁺_B is the rank n_B, the sum of the lengths of the stem and the blocks. -/
lemma IsSeparated.card_entries (hX : X.IsSeparated h) (hB : B ⊆ X.centres) :
    #(X.entries B) = X.rank B := by
  induction B using Finset.induction_on with
  | empty => simp [entries, rank]
  | insert c B hcB ih =>
    obtain ⟨hc, hB⟩ := insert_subset_iff.1 hB
    rw [entries_insert, card_union_of_disjoint (hX.disjoint_entries_block hB hc hcB), ih hB,
      rank_insert hcB, block, card_centredBlock]

omit [DecidableEq ι] in
/-- In a separated system every doubled entry y of λ⁺_B (the stem and the blocks of the centres
in B) has the parity opposite to that of the length of the stem. -/
lemma IsSeparated.odd_add_card_of_mem_entries (hX : X.IsSeparated h) (hB : B ⊆ X.centres)
    (hy : y ∈ X.entries B) : Odd (y + #X.stem) := by
  obtain hy_stem | hy_blocks : y ∈ X.stem ∨ y ∈ B.biUnion X.block := mem_union.1 hy
  · exact hX.odd_add_card y hy_stem
  · obtain ⟨c, hcB, hy_block⟩ : ∃ c ∈ B, y ∈ X.block c := mem_biUnion.1 hy_blocks
    obtain ⟨b, -, hy_eq⟩ : ∃ b < X.length c, y = 2 * X.centre c + X.length c - 1 - 2 * b :=
      mem_centredBlock.1 hy_block
    have h_length : X.length c % 2 = #X.stem % 2 := hX.length_mod_two c (hB hcB)
    grind

/-- In a separated system the residue mod 2 of the rank n_B is that of the length of the stem minus
the lowering (1 if the length of the stem and #B are odd, 0 otherwise). -/
lemma IsSeparated.rank_mod_two (hX : X.IsSeparated h) (hB : B ⊆ X.centres) :
    (X.rank B : ℤ) % 2 = #X.stem % 2 - X.lowering B := by
  induction B using Finset.induction_on with
  | empty => simp [rank, lowering]
  | insert c B hcB ih =>
    obtain ⟨hc, hB⟩ := insert_subset_iff.1 hB
    have h_length : X.length c % 2 = #X.stem % 2 := hX.length_mod_two c hc
    have h_rank : (X.rank B : ℤ) % 2 = #X.stem % 2 - X.lowering B := ih hB
    rw [rank_insert hcB]
    grind [lowering]

variable {n n' : Type} [Fintype n] [Fintype n'] {s : n → ℤˣ} {t : n' → ℤˣ}
  {l : HCParam s} {l' : HCParam t} {σ : ℤˣ}

/-- If l lists 2λ_B, each of its entries becomes an entry of 2λ⁺_B when the lowering is added. -/
lemma IsParam.add_lowering_mem (hl : X.IsParam B σ l) (x : n) :
    l x + X.lowering B ∈ X.entries B := by
  simp [← hl.image_eq]

/-- If l lists 2λ_B on the space with signs s and common sign σ, then it lists 2λ_B on the opposite
space, with signs −s and common sign −σ (`toHCParam (-s) l` is l, read for the signs −s). -/
lemma IsParam.neg_signs (hl : X.IsParam B σ l) : X.IsParam B (-σ) (toHCParam (-s) l) where
  card_eq := hl.card_eq
  image_eq := hl.image_eq
  sign_eq x := by rw [Pi.neg_apply, hl.sign_eq, neg_mul]

/-- If l lists 2λ_B and the coordinates x, x' have different signs, then some centre outside B
counts for exactly one of the two corresponding entries of 2λ⁺_B. -/
lemma IsParam.exists_not_countsFor_iff_of_sign_ne (hl : X.IsParam B σ l) {x x' : n}
    (h_sign_ne : s x ≠ s x') :
    ∃ c ∈ X.centres \ B,
      ¬(X.CountsFor c (l x + X.lowering B) ↔ X.CountsFor c (l x' + X.lowering B)) := by
  by_contra! h_same
  apply h_sign_ne
  rw [hl.sign_eq, hl.sign_eq, sign, sign, filter_congr h_same]

/-- Let X be a system with separation h and B a set of its centres. Let l list 2λ_B on a space of
rank n: λ_B consists of the stem and the blocks of the centres in B, lowered by ½ or 0, and the
sign of a coordinate is σ times −1 to the number of centres outside B that count for its entry.
Then l has gap h: its entries are distinct and congruent to n − 1 mod 2, and the entries of λ_B at
coordinates of opposite signs are at least h apart. -/
theorem IsParam.hasGap (hl : X.IsParam B σ l) (hX : X.IsSeparated h) (hB : B ⊆ X.centres) :
    l.HasGap h where
  injective := by
    have h_inj : Set.InjOn (fun x : n ↦ l x + X.lowering B) (univ : Finset n) := by
      rw [← card_image_iff, hl.image_eq, hX.card_entries hB, card_univ, hl.card_eq]
    exact fun x x' hx ↦ h_inj (mem_univ x) (mem_univ x') (by simp [hx])
  parity x := by
    have h_entry : Odd (l x + X.lowering B + #X.stem) :=
      hX.odd_add_card_of_mem_entries hB (hl.add_lowering_mem x)
    have h_rank : (X.rank B : ℤ) % 2 = #X.stem % 2 - X.lowering B := hX.rank_mod_two hB
    rw [hl.card_eq]
    grind
  gap x x' h_sign_ne := by
    obtain ⟨c, hc_mem, h_sep⟩ : ∃ c ∈ X.centres \ B,
        ¬(X.CountsFor c (l x + X.lowering B) ↔ X.CountsFor c (l x' + X.lowering B)) :=
      hl.exists_not_countsFor_iff_of_sign_ne h_sign_ne
    obtain ⟨hc, hcB⟩ := mem_sdiff.1 hc_mem
    have h_far (z : n) : (h + X.length c : ℤ) ≤ |l z + X.lowering B - 2 * X.centre c| :=
      hX.add_length_le_abs_sub_two_mul_centre hB hc hcB (hl.add_lowering_mem z)
    -- The two entries lie on opposite sides of c, and both are far from it.
    grind [CountsFor, h_far x, h_far x']

/-- In a separated system let c be a centre outside B, and B' = B ∪ {c}. The lowering of either set
is the rank of the other mod 2: that for B is n_B' mod 2, and that for B' is n_B mod 2. So raising
a parameter by ½ if the other space has odd rank undoes the lowering. -/
lemma IsSeparated.lowering_eq_rank_emod_two (hX : X.IsSeparated h) (hB : B ⊆ X.centres)
    (hc : c ∈ X.centres) (hcB : c ∉ B) :
    X.lowering B = (X.rank (insert c B) : ℤ) % 2 ∧
      X.lowering (insert c B) = (X.rank B : ℤ) % 2 := by
  have h_rank : (X.rank B : ℤ) % 2 = #X.stem % 2 - X.lowering B := hX.rank_mod_two hB
  have h_rank' : (X.rank (insert c B) : ℤ) % 2 = #X.stem % 2 - X.lowering (insert c B) :=
    hX.rank_mod_two (insert_subset hc hB)
  grind [lowering]

/-- If l lists 2λ_B and l' lists 2λ_B', for a centre c outside B and B' = B ∪ {c}, then the rank of
the space of l is at most that of the space of l'. -/
lemma IsParam.card_le_card_insert (hl : X.IsParam B σ l) (hl' : X.IsParam (insert c B) σ l')
    (hcB : c ∉ B) : card n ≤ card n' := by
  simp [hl.card_eq, hl'.card_eq, rank_insert hcB]

/-- Let l and l' list 2λ_B and 2λ_B' (`X.IsParam`, common sign `σ`) with coordinate signs `s` and
`t`. Here X is separated with bound h (`X.IsSeparated h`), and B' = B ∪ {c} for a centre
c ∈ `X.centres` outside B ⊆ `X.centres`. Raise each entry of l by `card n'` % 2 and each entry of l'
by `card n` % 2. Then the raised entries of l' are those of l together with
`centredBlock (X.centre c) (card n' - card n)`. Take coordinates x of l and r of l' with equal
raised entries. Then `s x ≠ t r` exactly if `X.CountsFor c` holds for that entry. -/
lemma IsParam.image_eq_union_and_sign_ne_iff (hl : X.IsParam B σ l)
    (hl' : X.IsParam (insert c B) σ l') (hX : X.IsSeparated h) (hB : B ⊆ X.centres)
    (hc : c ∈ X.centres) (hcB : c ∉ B) :
    univ.image (fun r : n' ↦ l' r + (card n : ℤ) % 2) =
        univ.image (fun x : n ↦ l x + (card n' : ℤ) % 2) ∪
          centredBlock (X.centre c) (card n' - card n) ∧
      ∀ (x : n) (r : n'), l x + (card n' : ℤ) % 2 = l' r + (card n : ℤ) % 2 →
        (s x ≠ t r ↔ X.CountsFor c (l x + (card n' : ℤ) % 2)) := by
  obtain ⟨h_low, h_low'⟩ : X.lowering B = (X.rank (insert c B) : ℤ) % 2 ∧
      X.lowering (insert c B) = (X.rank B : ℤ) % 2 := hX.lowering_eq_rank_emod_two hB hc hcB
  rw [hl.card_eq, hl'.card_eq, ← h_low, ← h_low']
  refine ⟨?_, fun x r h_eq ↦ ?_⟩
  · rw [hl.image_eq, hl'.image_eq, rank_insert hcB, Nat.add_sub_cancel_left, entries_insert, block]
  · rw [hl.sign_eq, hl'.sign_eq, ← h_eq, sign_eq_ite_sign_insert hc hcB]
    split_ifs with h_counts <;> simp [h_counts]

/-- Let X be separated with bound h (`IsSeparated h`), B ⊆ `X.centres`, c a centre outside B with
`X.isUp c = false`, B' = B ∪ {c}. Let l list 2λ_B and l' list 2λ_B' for one sign σ on spaces of
ranks `card n`, `card n'`. Here λ_B is the stem of X together with the blocks of the centres in B,
lowered by ½ or 0. If h ≥ 500(`card n` + `card n'`)³, then l and l' satisfy the block rule with
γ = `X.centre c` + ⌊`card n`/2⌋ and γ' = `X.centre c` + ⌊`card n'`/2⌋. -/
theorem IsParam.isBlockRule_insert_of_down {B' : Finset ι} (hl : X.IsParam B σ l)
    (hl' : X.IsParam B' σ l') (h_insert : B' = insert c B) (hX : X.IsSeparated h)
    (hB : B ⊆ X.centres) (hc : c ∈ X.centres) (hcB : c ∉ B)
    (h_gap : 500 * (card n + card n') ^ 3 ≤ h) (h_down : X.isUp c = false) :
    IsBlockRule (X.centre c + (card n : ℤ) / 2) (X.centre c + (card n' : ℤ) / 2) l l' := by
  subst h_insert
  obtain ⟨h_entries, h_signs⟩ := hl.image_eq_union_and_sign_ne_iff hl' hX hB hc hcB
  rw [isBlockRule_iff_of_character (hl.card_le_card_insert hl' hcB) rfl rfl]
  refine ⟨(hl.hasGap hX hB).mono h_gap, (hl'.hasGap hX (insert_subset hc hB)).mono h_gap,
    h_entries, fun x r h_eq ↦ ?_⟩
  -- For a down centre, c counts for the entries below it.
  simp [h_signs x r h_eq, CountsFor, h_down]

/-- Let X have separation h, let B be a set of its centres, c a centre outside B that is up, B' = B
∪ {c}. Let l list 2λ_B and l' list 2λ_B' for one sign σ on spaces of ranks n, n', where λ_B is the
stem with the blocks of B, lowered by ½ or 0. If h ≥ 500(n + n')³, then −l and −l' satisfy the block
rule with γ = −c + ⌈n/2⌉, γ' = −c + ⌈n'/2⌉: both have the gap 500(n + n')³, the shifted entries of
−l' are those of −l and a block centred at 0, and the coordinates of a common shifted entry have
equal signs if it is positive and opposite signs if it is negative. -/
theorem IsParam.isBlockRule_neg_insert_of_up {B' : Finset ι} (hl : X.IsParam B σ l)
    (hl' : X.IsParam B' σ l') (h_insert : B' = insert c B) (hX : X.IsSeparated h)
    (hB : B ⊆ X.centres) (hc : c ∈ X.centres) (hcB : c ∉ B)
    (h_gap : 500 * (card n + card n') ^ 3 ≤ h) (h_up : X.isUp c = true) :
    IsBlockRule (-X.centre c + ((card n : ℤ) + 1) / 2) (-X.centre c + ((card n' : ℤ) + 1) / 2)
      (-l) (-l') := by
  subst h_insert
  obtain ⟨h_entries, h_signs⟩ := hl.image_eq_union_and_sign_ne_iff hl' hX hB hc hcB
  rw [isBlockRule_iff_of_character_conj (hl.card_le_card_insert hl' hcB) rfl rfl]
  refine ⟨((hl.hasGap hX hB).mono h_gap).neg,
    ((hl'.hasGap hX (insert_subset hc hB)).mono h_gap).neg, ?_, fun x r h_eq ↦ ?_⟩
  · have h_neg : (univ.image fun r : n' ↦ l' r + (card n : ℤ) % 2).image Neg.neg =
        (univ.image fun x : n ↦ l x + (card n' : ℤ) % 2).image Neg.neg ∪
          centredBlock (-X.centre c) (card n' - card n) := by
      rw [h_entries, image_union, image_neg_centredBlock]
    simpa only [image_image, Function.comp_def, neg_add, sub_eq_add_neg, Pi.neg_apply,
      centredBlock] using h_neg
  · change -l x - (card n' : ℤ) % 2 = -l' r - (card n : ℤ) % 2 at h_eq
    change s x ≠ t r ↔ -l x - (card n' : ℤ) % 2 < 2 * -X.centre c
    -- For an up centre, c counts for the entries above it.
    simp only [h_signs x r (by omega), CountsFor, h_up, ite_eq_left]
    omega

end CentreSystem

end New
