import Diophantine.Paper1980.Weights90
import Diophantine.Paper1980.Isolation93b

/-!
# The coefficient layout of the 90-operation certificate

`Papers/1980/BINARY_PRODUCT_90_PROOF.md`, Sections 2–3 (from
`PRODUCT_BOUND_91_PROOF.md`, Sections 2–3).  A compiled circuit is a list of
*rows* (the quadratic polynomials `Layout.Row` of the 93-operation layout: a
row over `m` physical coordinates lists `s zᵢ²`, `2 s zᵢ z_k`, `2 s x zᵢ` and
`s x²`, with divided coefficients `s = ±1`).  A monomial is the multiset of its
physical factors, with the base-seven weight `W` of `Weights90.lean`.

Row `j` (of `s` rows) is tested at `t_j = (s + 2) d₀ + 8M + j d₀`,
`d₀ = 12 M + 8`; a divided coefficient `c` of the monomial `μ` of row `j` is the
term `c X^(t_j − W μ)` of the coefficient polynomial.  Every *negative* monomial
`μ` of row `j`, at the position `r = t_j − W μ`, receives the six positive
*helper complements* `X^(r − W π)`, `π` running over the pairs of the row's
helper group; the *tested starts* of row `j` are its target `t_j` and its
negative positions; every start `r` gets the *reset* `X^(r − 4)`; and the last
row gets the *padding* `Σ_{h ∈ P_X} X^(t_last − 1 − v_h)`.  Exponents of the
three kinds are `≡ 0, 4, 7 (mod 8)`.

This file defines the layout and proves the band-separation and residue facts.
-/

namespace Jones1980

namespace L90

open Polynomial
open Layout (Row)

noncomputable section

variable {m : ℕ}

/-! ### Monomials of a row -/

/-- The monomials of a row with their divided coefficients, as multisets of factors. -/
def terms (R : Row m) : List (Multiset (Fin m) × ℤ) :=
  (R.sq.map fun p => (({p.1, p.1} : Multiset (Fin m)), p.2)) ++
  (R.cross.map fun p => (({p.1, p.2.1} : Multiset (Fin m)), p.2.2)) ++
  (R.xz.map fun p => (({p.1} : Multiset (Fin m)), p.2)) ++ [((0 : Multiset (Fin m)), R.xx)]

theorem card_le_two_of_mem_terms {R : Row m} {q : Multiset (Fin m) × ℤ} (hq : q ∈ terms R) :
    Multiset.card q.1 ≤ 2 := by
  unfold terms at hq
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hq
  rcases hq with ((⟨p, _, rfl⟩ | ⟨p, _, rfl⟩) | ⟨p, _, rfl⟩) | rfl <;> simp

/-- The negative monomials of a row. -/
def negs (R : Row m) : List (Multiset (Fin m)) :=
  ((terms R).filter fun q => decide (q.2 < 0)).map Prod.fst

theorem mem_negs {R : Row m} {μ : Multiset (Fin m)} :
    μ ∈ negs R ↔ ∃ c, (μ, c) ∈ terms R ∧ c < 0 := by
  unfold negs
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨μ', c⟩, ⟨h1, h2⟩, rfl⟩; exact ⟨c, h1, h2⟩
  · rintro ⟨c, h1, h2⟩; exact ⟨(μ, c), ⟨h1, h2⟩, rfl⟩

/-- The six helper pairs of a group. -/
def pairs (P : Fin 3 → Fin m) : List (Multiset (Fin m)) :=
  [{P 0, P 0}, {P 1, P 1}, {P 2, P 2}, {P 0, P 1}, {P 0, P 2}, {P 1, P 2}]

theorem card_of_mem_pairs {P : Fin 3 → Fin m} {π : Multiset (Fin m)} (h : π ∈ pairs P) :
    Multiset.card π = 2 := by
  unfold pairs at h
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mem_of_mem_pairs {P : Fin 3 → Fin m} {π : Multiset (Fin m)} (hπ : π ∈ pairs P)
    {a : Fin m} (ha : a ∈ π) : ∃ b, a = P b := by
  unfold pairs at hπ
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hπ
  rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha <;>
    rcases ha with rfl | rfl <;> exact ⟨_, rfl⟩

theorem pairs_nodup {P : Fin 3 → Fin m} (hP : Function.Injective P) : (pairs P).Nodup := by
  have h01 : P 0 ≠ P 1 := fun h => by have := hP h; simp at this
  have h02 : P 0 ≠ P 2 := fun h => by have := hP h; simp at this
  have h12 : P 1 ≠ P 2 := fun h => by have := hP h; simp at this
  have hkey : (pairs P).map (fun μ => (μ.count (P 0), μ.count (P 1), μ.count (P 2))) =
      [(2, 0, 0), (0, 2, 0), (0, 0, 2), (1, 1, 0), (1, 0, 1), (0, 1, 1)] := by
    simp [pairs, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, h01, h02,
      h12, h01.symm, h02.symm, h12.symm]
  have : ((pairs P).map (fun μ => (μ.count (P 0), μ.count (P 1), μ.count (P 2)))).Nodup := by
    rw [hkey]; decide
  exact this.of_map _

/-! ### The layout constants -/

/-- The band spacing. -/
def d0 (m : ℕ) : ℕ := 12 * M m + 8

/-- The position of target `j` among `s` targets. -/
def t (m s j : ℕ) : ℕ := (s + 2) * d0 m + 8 * M m + j * d0 m

/-- The last target. -/
def tl (m s : ℕ) : ℕ := t m s (s - 1)

/-- The bound `K = t_last + 3` on the exponents of the layout. -/
def K (m s : ℕ) : ℕ := tl m s + 3

theorem eight_dvd_d0 (m : ℕ) : 8 ∣ d0 m := by
  unfold d0; exact dvd_add (Dvd.dvd.mul_left (eight_dvd_M m) 12) (dvd_refl 8)

theorem eight_dvd_t (m s j : ℕ) : 8 ∣ t m s j := by
  unfold t
  exact dvd_add (dvd_add (Dvd.dvd.mul_left (eight_dvd_d0 m) _) (Dvd.dvd.mul_left (eight_dvd_M m) 8))
    (Dvd.dvd.mul_left (eight_dvd_d0 m) _)

theorem d0_gt (m : ℕ) : 12 * M m + 7 < d0 m := by unfold d0; omega

theorem t_succ (m s j : ℕ) : t m s (j + 1) = t m s j + d0 m := by unfold t; ring

theorem t_add (m s j k : ℕ) : t m s (j + k) = t m s j + k * d0 m := by unfold t; ring

theorem t_sub_ge {m s j k : ℕ} (hjk : j < k) : t m s j + d0 m ≤ t m s k := by
  obtain ⟨i, rfl⟩ : ∃ i, k = j + 1 + i := ⟨k - (j + 1), by omega⟩
  rw [t_add, t_succ]; omega

theorem t_mono {m s j k : ℕ} (hjk : j ≤ k) : t m s j ≤ t m s k := by
  unfold t; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hjk) _

theorem t_inj {m s j k : ℕ} (h : t m s j = t m s k) : j = k := by
  by_contra hne
  have hd0 := d0_gt m
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := t_sub_ge (m := m) (s := s) hlt; omega
  · have := t_sub_ge (m := m) (s := s) hgt; omega

/-- The first target is far above `M`: `t_0 ≥ 32 M + 16`. -/
theorem t_zero_ge (m s : ℕ) : 32 * M m + 16 ≤ t m s 0 := by
  unfold t d0; nlinarith [M_pos m]

theorem t_ge (m s j : ℕ) : 32 * M m + 16 ≤ t m s j :=
  le_trans (t_zero_ge m s) (t_mono (Nat.zero_le j))

theorem t_le_tl {m s : ℕ} (j : Fin s) : t m s j ≤ tl m s := t_mono (by have := j.isLt; omega)

/-- Band separation: a position `p` within `[t_j − 4M − 6, t_j + 2]` is not within `2M`
above any exponent `e ∈ [t_k − 4M − 4, t_k]` of another band `k ≠ j`. -/
theorem band_unique {m s j k p e : ℕ} (hjk : k ≠ j)
    (hp1 : t m s j ≤ p + 4 * M m + 6) (hp2 : p ≤ t m s j + 2)
    (he1 : t m s k ≤ e + 4 * M m + 4) (he2 : e ≤ t m s k)
    (hpe : e ≤ p ∧ p ≤ e + 2 * M m) : False := by
  have hd0 := d0_gt m
  rcases Nat.lt_or_gt_of_ne hjk with hlt | hgt
  · have := t_sub_ge (m := m) (s := s) hlt; omega
  · have := t_sub_ge (m := m) (s := s) hgt; omega

/-- Dummy exclusion: a coordinate position `u ≥ t_0 − 2M` and an exponent
`e ≥ t_0 − 4M − 4` sum to more than `t_last + 2`. -/
theorem dummy_exclusion {m s u e : ℕ} (hs : 1 ≤ s) (hu : t m s 0 ≤ u + 2 * M m)
    (he : t m s 0 ≤ e + 4 * M m + 4) : tl m s + 2 < u + e := by
  unfold tl
  have h1 : t m s (s - 1) = t m s 0 + (s - 1) * d0 m := by
    have := t_add m s 0 (s - 1); rwa [zero_add] at this
  have h2 : t m s 0 = (s + 2) * d0 m + 8 * M m := by unfold t; ring
  have hd0 := d0_gt m
  have : (s - 1) * d0 m + 3 * d0 m = (s + 2) * d0 m := by
    rw [show s + 2 = (s - 1) + 3 by omega, add_mul]
  nlinarith

/-! ### Starts and the coefficient polynomial -/

variable (s : ℕ) (rows : Fin s → Row m)

/-- The tested starts of row `j`: its target and its negative positions. -/
def starts (j : Fin s) : Finset ℕ :=
  insert (t m s j) (((negs (rows j)).map fun μ => t m s j - W μ).toFinset)

/-- All tested starts. -/
def Rset : Finset ℕ := Finset.univ.biUnion (starts s rows)

theorem mem_starts {j : Fin s} {r : ℕ} :
    r ∈ starts s rows j ↔ r = t m s j ∨ ∃ μ ∈ negs (rows j), r = t m s j - W μ := by
  unfold starts
  simp only [Finset.mem_insert, List.mem_toFinset, List.mem_map]
  constructor
  · rintro (h | ⟨μ, hμ, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨μ, hμ, rfl⟩
  · rintro (h | ⟨μ, hμ, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨μ, hμ, rfl⟩

theorem mem_Rset {r : ℕ} : r ∈ Rset s rows ↔ ∃ j, r ∈ starts s rows j := by
  unfold Rset; simp

theorem t_mem_starts (j : Fin s) : t m s j ∈ starts s rows j := (mem_starts s rows).2 (Or.inl rfl)

theorem t_mem_Rset (j : Fin s) : t m s j ∈ Rset s rows := (mem_Rset s rows).2 ⟨j, t_mem_starts s rows j⟩

/-- The main terms of row `j`. -/
def rowPoly (j : ℕ) (R : Row m) : ℤ[X] :=
  ((terms R).map fun q => C q.2 * X ^ (t m s j - W q.1)).sum

/-- The helper complements of row `j` with helper group `P`. -/
def helpPoly (j : ℕ) (R : Row m) (P : Fin 3 → Fin m) : ℤ[X] :=
  ((negs R).map fun μ => ((pairs P).map fun π => (X : ℤ[X]) ^ (t m s j - W μ - W π)).sum).sum

/-- The resets. -/
def resetPoly : ℤ[X] := ∑ r ∈ Rset s rows, (X : ℤ[X]) ^ (r - 4)

/-- The padding of the last row with the group `P_X`. -/
def padPoly (PX : Finset (Fin m)) : ℤ[X] := ∑ h ∈ PX, (X : ℤ[X]) ^ (tl m s - 1 - v h)

/-- The coefficient polynomial. -/
def D (hel : Fin s → Fin 3 → Fin m) (PX : Finset (Fin m)) : ℤ[X] :=
  ∑ j : Fin s, rowPoly s j (rows j) + ∑ j : Fin s, helpPoly s j (rows j) (hel j) +
    resetPoly s rows + padPoly s PX

/-- The digit polynomial of the input and the true coordinates. -/
def Cmain (x : ℤ) (z : Fin m → ℤ) : ℤ[X] := C x + ∑ i : Fin m, C (z i) * X ^ (v i)

/-- The digit polynomial of the dummy coordinates at the window positions. -/
def Cdum (dum : ℕ → Fin 3 → ℤ) : ℤ[X] :=
  ∑ r ∈ Rset s rows, ∑ e : Fin 3, C (dum r e) * X ^ (r + (e : ℕ))

/-! ### Validity -/

/-- A valid row with helper group `P`: divided coefficients `±1` or `0`, distinct monomials,
genuine cross pairs, nonnegative `x zᵢ` and nonpositive `x²` coefficients, and a helper group
disjoint from every negative monomial. -/
structure RowOk (R : Row m) (P : Fin 3 → Fin m) : Prop where
  coeff : ∀ q ∈ terms R, |q.2| ≤ 1
  nodup : ((terms R).map Prod.fst).Nodup
  cross : ∀ q ∈ R.cross, q.1 ≠ q.2.1
  xz : ∀ q ∈ R.xz, 0 ≤ q.2
  xx : R.xx ≤ 0
  disj : ∀ μ ∈ negs R, ∀ a, P a ∉ μ
  inj : Function.Injective P
  seed : R.xx < 0 → R.sq = [] ∧ R.cross = [] ∧ R.xz = []

/-- A seed row (negative `x²`) has no other monomial. -/
theorem terms_of_seed {R : Row m} {P : Fin 3 → Fin m} (hR : RowOk R P) (hxx : R.xx < 0) :
    terms R = [((0 : Multiset (Fin m)), R.xx)] := by
  obtain ⟨h1, h2, h3⟩ := hR.seed hxx
  unfold terms; rw [h1, h2, h3]; rfl

theorem negs_of_seed {R : Row m} {P : Fin 3 → Fin m} (hR : RowOk R P) (hxx : R.xx < 0) :
    ∀ μ ∈ negs R, μ = 0 := by
  intro μ hμ
  obtain ⟨c, hc, _⟩ := (mem_negs).1 hμ
  rw [terms_of_seed hR hxx, List.mem_singleton, Prod.mk.injEq] at hc
  exact hc.1

/-- A valid layout: valid rows, and a last row without negative monomials. -/
structure LayoutOk (hel : Fin s → Fin 3 → Fin m) : Prop where
  three_le : 3 ≤ s
  rows_ok : ∀ j, RowOk (rows j) (hel j)
  last : ∀ j : Fin s, (j : ℕ) = s - 1 → negs (rows j) = [] ∧ (rows j).xx = 0

/-- A negative monomial has degree two, or is `x²` (degree zero). -/
theorem card_of_mem_negs {R : Row m} {P : Fin 3 → Fin m} (hR : RowOk R P) {μ : Multiset (Fin m)}
    (hμ : μ ∈ negs R) : Multiset.card μ = 2 ∨ μ = 0 := by
  obtain ⟨c, hc, hneg⟩ := (mem_negs).1 hμ
  unfold terms at hc
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hc
  rcases hc with ((⟨p, _, hp⟩ | ⟨p, _, hp⟩) | ⟨p, hp, hp'⟩) | hp
  · left; rw [Prod.mk.injEq] at hp; rw [← hp.1]; simp
  · left; rw [Prod.mk.injEq] at hp; rw [← hp.1]; simp
  · exfalso; rw [Prod.mk.injEq] at hp'; have := hR.xz p hp; omega
  · right; rw [Prod.mk.injEq] at hp; exact hp.1

theorem negs_nodup {R : Row m} {P : Fin 3 → Fin m} (hR : RowOk R P) : (negs R).Nodup := by
  unfold negs
  exact hR.nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist)

/-- A monomial occurs once in a valid row. -/
theorem terms_coeff_unique {R : Row m} {P : Fin 3 → Fin m} (hR : RowOk R P)
    {μ : Multiset (Fin m)} {c c' : ℤ} (hc : (μ, c) ∈ terms R) (hc' : (μ, c') ∈ terms R) :
    c = c' := by
  have hcc : (μ, c) = (μ, c') := List.inj_on_of_nodup_map hR.nodup hc hc' rfl
  rw [Prod.mk.injEq] at hcc
  exact hcc.2

/-- The coefficient of a negative monomial is `−1`. -/
theorem coeff_of_mem_negs {R : Row m} {P : Fin 3 → Fin m} (hR : RowOk R P)
    {μ : Multiset (Fin m)} {c : ℤ} (hc : (μ, c) ∈ terms R) (hμ : μ ∈ negs R) : c = -1 := by
  obtain ⟨c', hc', hneg⟩ := (mem_negs).1 hμ
  have hcc := terms_coeff_unique hR hc hc'
  have := hR.coeff _ hc'
  rw [hcc]; rw [abs_le] at this; omega

end

end L90

end Jones1980
