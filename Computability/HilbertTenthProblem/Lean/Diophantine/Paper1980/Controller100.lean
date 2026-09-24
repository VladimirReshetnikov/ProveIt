import Diophantine.Paper1980.Compiled100

/-!
# The compiled fixed controller

`EXPLORATION_FIXED_PROGRAM_ROUTING.md`, §1, as used by
`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §1.  A fixed program is first phase-split so that
its successor function has no fixed point, then its `n ≥ 2` states are numbered from zero
and given the *Sidon exponents* `a i = 3^i`, with marker exponent `d = max_i a_i = 3^(n−1)`.
The fixed numerals are

    S = Σ_i 3^(a i),   g = 3^d,   I = 3^(a 0),
    hs = 3^(d + bs),   hz = 3^(d + bz),
    K = Σ_i ( 3^(d + a (f i) − a i)  +  3^(d − a i)
              + [sign i] 3^(d + bs − a i)  +  [zero i] 3^(d + bz − a i) ).

The edge terms route a selected state to its successor at the marker scale, the marker
terms count the step, and the two port terms carry the sign and zero-request labels.

Two structural facts follow from this shape alone, and they are exactly the two layout
hypotheses of `decode_layout100`.  Every exponent of `K` except one is positive: the marker
term of the *last* state contributes `3^(d − d) = 1`, while every other term has a positive
exponent, because `a i < d` for `i < n − 1`, because destination coordinates are positive,
and because the two ports sit above the marker.  So `K` is `1`-led at zero, which is
`d − amax` with `amax = d`.  And the cyclic entry is state zero, so `I = 3^(a 0)` with
`a 0 = 1 < d`.

`rom_sidon` and `rom_layout` are those two facts, so `decode_compiled_controller100`
decodes any solution over a compiled controller from the single decoded-control bound
`2q ≤ R D` of §5.

The module also proves the whole of the routing note's §1.  `sidon_coord` is the property
the coordinates are named for: a pair sum `a i + a j` determines the unordered pair, which
is the uniqueness of ternary digits since the coefficients of such a sum are at most two.
From it, `edge_exponent_inj`: an equality of two edge exponents is an equality of two pair
sums, so either the two states agree or both edges are self-loops, and the phase split has
removed the latter.  With the marker and port families separated by their heights, all four
families are distinct, so `romK_bool` — the table is a Boolean ternary numeral.

`dg_romK_shift` is then the note's coefficient statement: for a single selected state `i`,
the digit of `K · 3^(a i)` at the target exponent `d + a j` is `1` exactly when `j = f i`.
An individual summand can reach that target only if `a i + a (f k) = a j + a k`; the Sidon
alternatives are `k = i` with `f i = j`, or `i = j` with `f k = k`, and the second is the
self-loop contamination the phase split removed.  `dg_romK_shift_mark`,
`dg_romK_shift_sgn` and `dg_romK_shift_zreq` complete the picture: the marker term counts
the step and the two port terms carry the labels.

This is the engine of the ROM and count-marker argument that §5 of the counter note cites
rather than reproves.  What it does not yet do is run it over the rows of an actual state
word, which is what turns the twelve decoded fields into a controller path.

Finally `rom_ok`: the compiled ROM over the grid numeral `zonChoice` satisfies the fixed
grid inequalities.  The only one with content is `K < hz`, which holds because every
exponent of the table is below `d + bz` and a sum of distinct powers below a bound is below
that bound's power.  So the hypotheses of the decoding are not vacuous, and
`decode_controller100` decodes a solution over a compiled controller's own ROM from the
decoded-control bound alone — the grid inequalities and the radix geometry both come from
the compilation.
-/

namespace Jones1980

open Finset

/-- The Sidon exponent of state `i`. -/
def coord (i : ℕ) : ℕ := 3 ^ i

/-- The leading trit of a pair sum `3^a + 3^b` with `a ≤ b`: a `2` at `a` when the two
coordinates coincide, and a `1` at `a` otherwise. -/
theorem lead_pair {a b : ℕ} (hab : a ≤ b) :
    Ternary.Lead a (if a = b then 2 else 1) (3 ^ a + 3 ^ b) := by
  by_cases h : a = b
  · subst h
    exact ⟨2, by ring, by simp⟩
  · refine ⟨1 + 3 ^ (b - a), ?_, ?_⟩
    · rw [Nat.mul_add, mul_one, ← pow_add]
      congr 2
      omega
    · obtain ⟨cc, hcc⟩ : ∃ cc, b - a = cc + 1 := ⟨b - a - 1, by omega⟩
      rw [hcc, pow_succ, if_neg h]
      omega

/-- The Sidon property for ordered pairs. -/
theorem sidon_aux {i j k l : ℕ} (hij : i ≤ j) (hkl : k ≤ l)
    (h : 3 ^ i + 3 ^ j = 3 ^ k + 3 ^ l) : i = k ∧ j = l := by
  have h1 := lead_pair hij
  have h2 := lead_pair hkl
  rw [h] at h1
  have hne1 : (if i = j then 2 else 1) ≠ 0 := by split <;> norm_num
  have hne2 : (if k = l then 2 else 1) ≠ 0 := by split <;> norm_num
  obtain ⟨hik, -⟩ := h1.unique h2 hne1 hne2
  subst hik
  refine ⟨rfl, ?_⟩
  have hjl : (3 : ℕ) ^ j = 3 ^ l := by omega
  exact Nat.pow_right_injective (by norm_num) hjl

/-- **The Sidon property.**  `a i = 3^i` is a Sidon set: a pair sum determines the
unordered pair, including when the two indices coincide.  This is the uniqueness of
ternary digits, whose coefficients in such a sum are at most two. -/
theorem sidon_coord {i j k l : ℕ} (h : coord i + coord j = coord k + coord l) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  unfold coord at h
  rcases le_total i j with hij | hij <;> rcases le_total k l with hkl | hkl
  · exact Or.inl (sidon_aux hij hkl h)
  · exact Or.inr (sidon_aux hij hkl (by omega))
  · exact Or.inr (And.symm (sidon_aux hij hkl (by omega)))
  · exact Or.inl (And.symm (sidon_aux hij hkl (by omega)))

/-- The ternary digits of a sum of powers with distinct exponents: a `1` exactly at the
exponents that occur. -/
theorem Ternary.dg_sum_pow (s : Finset ℕ) :
    ∀ p, Ternary.dg (∑ e ∈ s, 3 ^ e) p = if p ∈ s then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => intro p; simp [Ternary.dg]
  | insert a s ha ih =>
    intro p
    rw [Finset.sum_insert ha]
    have hle : ∀ j, Ternary.dg (3 ^ a) j + Ternary.dg (∑ e ∈ s, 3 ^ e) j ≤ 2 := by
      intro j
      have h1 : Ternary.dg (3 ^ a) j ≤ 1 := by rw [Ternary.dg_pow]; split <;> omega
      have h2 : Ternary.dg (∑ e ∈ s, 3 ^ e) j ≤ 1 := by rw [ih j]; split <;> omega
      omega
    rw [Ternary.dg_add_of_le_two hle, Ternary.dg_pow, ih p]
    by_cases hpa : p = a
    · subst hpa
      simp [ha]
    · simp [hpa, Finset.mem_insert]

/-- Hence such a sum is a Boolean ternary numeral. -/
theorem Ternary.bool3_sum_pow (s : Finset ℕ) : Ternary.Bool3 (∑ e ∈ s, 3 ^ e) := by
  intro p
  rw [Ternary.dg_sum_pow]
  split <;> omega

/-- A sum of two powers of three is never a power of three. -/
theorem pow_add_pow_ne_pow_of_le {p q r : ℕ} (hpq : p ≤ q) : (3 : ℕ) ^ p + 3 ^ q ≠ 3 ^ r := by
  intro h
  have hr : Ternary.Lead r 1 (3 ^ r) := ⟨1, by ring, rfl⟩
  have h1 := lead_pair hpq
  rw [h] at h1
  obtain ⟨hpr, hdig⟩ := h1.unique hr (by split <;> norm_num) (by norm_num)
  have hne : p ≠ q := by intro he; rw [if_pos he] at hdig; omega
  subst hpr
  have hq0 : 0 < (3 : ℕ) ^ q := by positivity
  omega

/-- A sum of two powers of three is never a power of three. -/
theorem pow_add_pow_ne_pow (p q r : ℕ) : (3 : ℕ) ^ p + 3 ^ q ≠ 3 ^ r := by
  rcases le_total p q with hpq | hpq
  · exact pow_add_pow_ne_pow_of_le hpq
  · intro h
    have h' : (3 : ℕ) ^ q + 3 ^ p = 3 ^ r := by omega
    exact pow_add_pow_ne_pow_of_le hpq h'

/-- A compiled fixed controller: at least two states numbered from zero, a successor
function, the sign and zero-request labels, and the two port offsets above the marker. -/
structure Controller where
  /-- The number of states, after the phase split. -/
  n : ℕ
  /-- At least two states. -/
  two_le : 2 ≤ n
  /-- The successor function on states. -/
  f : ℕ → ℕ
  /-- The successor is a state. -/
  f_lt : ∀ i, i < n → f i < n
  /-- The phase split leaves no self-loop. -/
  f_ne : ∀ i, i < n → f i ≠ i
  /-- The sign label. -/
  sgn : ℕ → Bool
  /-- The zero-request label. -/
  zreq : ℕ → Bool
  /-- The sign port offset. -/
  bs : ℕ
  /-- The zero-request port offset. -/
  bz : ℕ
  /-- The sign port sits above the marker. -/
  bs_pos : 0 < bs
  /-- The zero-request port sits above the sign port. -/
  bs_lt : bs < bz
  /-- The sign port sits above every edge and marker exponent.  The routing note asks only
  that the ports be above all state coordinates; a compiler takes them higher, and its own
  conclusion that all table exponents are distinct needs that. -/
  bs_high : 2 * 3 ^ (n - 1) < bs
  /-- And the zero-request port above every sign exponent. -/
  bz_high : 3 ^ (n - 1) + bs < bz

namespace Controller

variable (P : Controller)

/-- The marker exponent `d = max_i a_i`. -/
def mark : ℕ := 3 ^ (P.n - 1)

/-- The fixed state word `S = Σ_i 3^(a i)`. -/
def romS : ℕ := ∑ i ∈ range P.n, 3 ^ coord i

/-- The marker numeral `g = 3^d`. -/
def romg : ℕ := 3 ^ P.mark

/-- The sign port `hs = 3^(d + bs)`. -/
def romhs : ℕ := 3 ^ (P.mark + P.bs)

/-- The zero-request port `hz = 3^(d + bz)`. -/
def romhz : ℕ := 3 ^ (P.mark + P.bz)

/-- One state's contribution to the fixed table. -/
def tableTerm (i : ℕ) : ℕ :=
  3 ^ (P.mark + coord (P.f i) - coord i) + 3 ^ (P.mark - coord i)
    + (if P.sgn i then 3 ^ (P.mark + P.bs - coord i) else 0)
    + (if P.zreq i then 3 ^ (P.mark + P.bz - coord i) else 0)

/-- The fixed table `K`. -/
def romK : ℕ := ∑ i ∈ range P.n, P.tableTerm i

/-- The compiled ROM, over a choice of fixed grid numeral and spacing. -/
def rom (Zon B0 : ℕ) : ROM100 :=
  { Zon := Zon, B0 := B0, K := P.romK, g := P.romg, I := 3 ^ coord 0,
    hs := P.romhs, hz := P.romhz, S := P.romS }

/-- The coordinates below the last one are below the marker. -/
theorem coord_lt_mark {i : ℕ} (hi : i < P.n - 1) : coord i < P.mark :=
  Nat.pow_lt_pow_right (by norm_num) hi

/-- The last coordinate is the marker. -/
theorem coord_last : coord (P.n - 1) = P.mark := rfl

/-- Every coordinate is at most the marker. -/
theorem coord_le_mark {i : ℕ} (hi : i < P.n) : coord i ≤ P.mark :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The table has distinct edge exponents.**  An equality of two edge exponents is an
equality of two Sidon pair sums, so either the two states agree or both edges are
self-loops, and the phase split has removed the latter. -/
theorem edge_exponent_inj {i j : ℕ} (hi : i < P.n) (hj : j < P.n)
    (h : P.mark + coord (P.f i) - coord i = P.mark + coord (P.f j) - coord j) : i = j := by
  have hci := P.coord_le_mark hi
  have hcj := P.coord_le_mark hj
  have hsum : coord (P.f i) + coord j = coord (P.f j) + coord i := by omega
  rcases sidon_coord hsum with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact h2.symm
  · exact absurd h1 (P.f_ne i hi)

/-! ### The four exponent families -/

/-- The edge exponent of state `i`. -/
def edgeExp (i : ℕ) : ℕ := P.mark + coord (P.f i) - coord i

/-- The marker exponent of state `i`. -/
def markExp (i : ℕ) : ℕ := P.mark - coord i

/-- The sign-port exponent of state `i`. -/
def sgnExp (i : ℕ) : ℕ := P.mark + P.bs - coord i

/-- The zero-request-port exponent of state `i`. -/
def zreqExp (i : ℕ) : ℕ := P.mark + P.bz - coord i

theorem one_le_coord (i : ℕ) : 1 ≤ coord i := Nat.one_le_pow _ _ (by norm_num)

theorem one_le_mark : 1 ≤ P.mark := Nat.one_le_pow _ _ (by norm_num)

theorem markExp_lt {i : ℕ} (hi : i < P.n) : P.markExp i < P.mark := by
  have h1 := P.coord_le_mark hi
  have h2 := one_le_coord i
  have h3 : 1 ≤ P.mark := P.one_le_mark
  unfold markExp
  omega

theorem edgeExp_le {i : ℕ} (hi : i < P.n) : P.edgeExp i ≤ 2 * P.mark := by
  have h1 := P.coord_le_mark hi
  have h2 : coord (P.f i) ≤ P.mark := P.coord_le_mark (P.f_lt i hi)
  unfold edgeExp
  omega

theorem le_sgnExp {i : ℕ} (hi : i < P.n) : P.bs ≤ P.sgnExp i := by
  have h1 := P.coord_le_mark hi
  unfold sgnExp
  omega

theorem sgnExp_lt {i : ℕ} (hi : i < P.n) : P.sgnExp i < P.mark + P.bs := by
  have h1 := P.coord_le_mark hi
  have h2 := one_le_coord i
  unfold sgnExp
  omega

theorem le_zreqExp {i : ℕ} (hi : i < P.n) : P.bz ≤ P.zreqExp i := by
  have h1 := P.coord_le_mark hi
  unfold zreqExp
  omega

theorem zreqExp_lt {i : ℕ} (hi : i < P.n) : P.zreqExp i < P.mark + P.bz := by
  have h1 := P.coord_le_mark hi
  have h2 := one_le_coord i
  unfold zreqExp
  omega

/-- The marker exponents are distinct. -/
theorem markExp_inj {i j : ℕ} (hi : i < P.n) (hj : j < P.n) (h : P.markExp i = P.markExp j) :
    i = j := by
  have h1 := P.coord_le_mark hi
  have h2 := P.coord_le_mark hj
  unfold markExp at h
  have : coord i = coord j := by omega
  exact Nat.pow_right_injective (by norm_num) this

/-- The sign-port exponents are distinct. -/
theorem sgnExp_inj {i j : ℕ} (hi : i < P.n) (hj : j < P.n) (h : P.sgnExp i = P.sgnExp j) :
    i = j := by
  have h1 := P.coord_le_mark hi
  have h2 := P.coord_le_mark hj
  unfold sgnExp at h
  have : coord i = coord j := by omega
  exact Nat.pow_right_injective (by norm_num) this

/-- The zero-request-port exponents are distinct. -/
theorem zreqExp_inj {i j : ℕ} (hi : i < P.n) (hj : j < P.n) (h : P.zreqExp i = P.zreqExp j) :
    i = j := by
  have h1 := P.coord_le_mark hi
  have h2 := P.coord_le_mark hj
  unfold zreqExp at h
  have : coord i = coord j := by omega
  exact Nat.pow_right_injective (by norm_num) this

/-- **No edge exponent is a marker exponent.**  Equality would say `a (f i) + a j = a i`,
and a sum of two coordinates is never a coordinate. -/
theorem edgeExp_ne_markExp {i j : ℕ} (hi : i < P.n) (hj : j < P.n) :
    P.edgeExp i ≠ P.markExp j := by
  intro h
  have h1 := P.coord_le_mark hi
  have h2 := P.coord_le_mark hj
  have h3 : coord (P.f i) ≤ P.mark := P.coord_le_mark (P.f_lt i hi)
  unfold edgeExp markExp at h
  have hsum : coord (P.f i) + coord j = coord i := by omega
  exact pow_add_pow_ne_pow _ _ _ hsum

/-! ### The table is a Boolean ternary numeral -/

/-- The exponent set of the table. -/
def expSet : Finset ℕ :=
  ((range P.n).image P.edgeExp) ∪ ((range P.n).image P.markExp)
    ∪ ((range P.n).filter (fun i => P.sgn i = true)).image P.sgnExp
    ∪ ((range P.n).filter (fun i => P.zreq i = true)).image P.zreqExp

theorem disj_of_lt {s t : Finset ℕ} (b : ℕ) (hs : ∀ e ∈ s, e < b) (ht : ∀ e ∈ t, b ≤ e) :
    Disjoint s t := by
  rw [Finset.disjoint_left]
  intro e he het
  have h1 := hs e he
  have h2 := ht e het
  omega

theorem mem_edge_image {e : ℕ} (he : e ∈ (range P.n).image P.edgeExp) : e ≤ 2 * P.mark := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
  exact P.edgeExp_le (Finset.mem_range.1 hi)

theorem mem_mark_image {e : ℕ} (he : e ∈ (range P.n).image P.markExp) : e < P.mark := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
  exact P.markExp_lt (Finset.mem_range.1 hi)

theorem mem_sgn_image {e : ℕ}
    (he : e ∈ ((range P.n).filter (fun i => P.sgn i = true)).image P.sgnExp) :
    P.bs ≤ e ∧ e < P.mark + P.bs := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
  have hi' := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
  exact ⟨P.le_sgnExp hi', P.sgnExp_lt hi'⟩

theorem mem_zreq_image {e : ℕ}
    (he : e ∈ ((range P.n).filter (fun i => P.zreq i = true)).image P.zreqExp) : P.bz ≤ e := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
  exact P.le_zreqExp (Finset.mem_range.1 (Finset.mem_filter.1 hi).1)

theorem disj_edge_mark : Disjoint ((range P.n).image P.edgeExp) ((range P.n).image P.markExp) := by
  rw [Finset.disjoint_left]
  intro e he het
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.1 het
  exact P.edgeExp_ne_markExp (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hji.symm

theorem disj_low_sgn :
    Disjoint (((range P.n).image P.edgeExp) ∪ ((range P.n).image P.markExp))
      (((range P.n).filter (fun i => P.sgn i = true)).image P.sgnExp) := by
  refine disj_of_lt P.bs (fun e he => ?_) (fun e he => (P.mem_sgn_image he).1)
  rcases Finset.mem_union.1 he with h | h
  · have := P.mem_edge_image h
    have := P.bs_high
    unfold mark at *
    omega
  · have := P.mem_mark_image h
    have := P.bs_high
    unfold mark at *
    omega

theorem disj_low_zreq :
    Disjoint ((((range P.n).image P.edgeExp) ∪ ((range P.n).image P.markExp))
        ∪ (((range P.n).filter (fun i => P.sgn i = true)).image P.sgnExp))
      (((range P.n).filter (fun i => P.zreq i = true)).image P.zreqExp) := by
  refine disj_of_lt P.bz (fun e he => ?_) (fun e he => P.mem_zreq_image he)
  have hbs := P.bs_high
  have hbz := P.bz_high
  rcases Finset.mem_union.1 he with h | h
  · rcases Finset.mem_union.1 h with h' | h'
    · have := P.mem_edge_image h'
      unfold mark at *
      omega
    · have := P.mem_mark_image h'
      unfold mark at *
      omega
  · have := (P.mem_sgn_image h).2
    unfold mark at *
    omega

/-- **The table is a Boolean ternary numeral**, since all four families of exponents are
distinct: edges from edges by the Sidon property, edges from markers because a sum of two
coordinates is never a coordinate, markers from markers because the coordinates are
distinct, and the two port families from everything below them by their heights. -/
theorem romK_eq : P.romK = ∑ e ∈ P.expSet, 3 ^ e := by
  have hEinj : ∀ i ∈ range P.n, ∀ j ∈ range P.n, P.edgeExp i = P.edgeExp j → i = j :=
    fun i hi j hj h => P.edge_exponent_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h
  have hMinj : ∀ i ∈ range P.n, ∀ j ∈ range P.n, P.markExp i = P.markExp j → i = j :=
    fun i hi j hj h => P.markExp_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h
  have hSinj : ∀ i ∈ (range P.n).filter (fun i => P.sgn i = true),
      ∀ j ∈ (range P.n).filter (fun i => P.sgn i = true), P.sgnExp i = P.sgnExp j → i = j :=
    fun i hi j hj h => P.sgnExp_inj (Finset.mem_range.1 (Finset.mem_filter.1 hi).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 hj).1) h
  have hZinj : ∀ i ∈ (range P.n).filter (fun i => P.zreq i = true),
      ∀ j ∈ (range P.n).filter (fun i => P.zreq i = true), P.zreqExp i = P.zreqExp j → i = j :=
    fun i hi j hj h => P.zreqExp_inj (Finset.mem_range.1 (Finset.mem_filter.1 hi).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 hj).1) h
  rw [expSet, Finset.sum_union P.disj_low_zreq, Finset.sum_union P.disj_low_sgn,
    Finset.sum_union P.disj_edge_mark, Finset.sum_image hEinj, Finset.sum_image hMinj,
    Finset.sum_image hSinj, Finset.sum_image hZinj, Finset.sum_filter, Finset.sum_filter]
  simp only [romK, tableTerm, edgeExp, markExp, sgnExp, zreqExp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]

theorem romK_bool : Ternary.Bool3 P.romK := by
  rw [P.romK_eq]
  exact Ternary.bool3_sum_pow _

/-! ### The projection of a selected state -/

theorem dg_romK (p : ℕ) : Ternary.dg P.romK p = if p ∈ P.expSet then 1 else 0 := by
  rw [P.romK_eq]
  exact Ternary.dg_sum_pow _ p

theorem target_mem_expSet {i : ℕ} (hi : i < P.n) :
    (P.mark + coord (P.f i) - coord i) ∈ P.expSet := by
  show P.edgeExp i ∈ P.expSet
  rw [expSet]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩)))

theorem target_not_mem_expSet {i j : ℕ} (hi : i < P.n) (hj : j < P.n) (hne : j ≠ P.f i) :
    (P.mark + coord j - coord i) ∉ P.expSet := by
  intro hmem
  have hm : P.mark = 3 ^ (P.n - 1) := rfl
  have hci := P.coord_le_mark hi
  have hcj := P.coord_le_mark hj
  have hbs := P.bs_high
  have hbz := P.bz_high
  rw [expSet] at hmem
  rcases Finset.mem_union.1 hmem with h | h
  · rcases Finset.mem_union.1 h with h' | h'
    · rcases Finset.mem_union.1 h' with h'' | h''
      · obtain ⟨k, hk, hkeq⟩ := Finset.mem_image.1 h''
        have hk' := Finset.mem_range.1 hk
        have hck := P.coord_le_mark hk'
        have hcfk : coord (P.f k) ≤ P.mark := P.coord_le_mark (P.f_lt k hk')
        unfold edgeExp at hkeq
        have hsum : coord j + coord k = coord (P.f k) + coord i := by omega
        rcases sidon_coord hsum with ⟨h1, h2⟩ | ⟨-, h2⟩
        · exact hne (h2 ▸ h1)
        · exact P.f_ne k hk' h2.symm
      · obtain ⟨k, hk, hkeq⟩ := Finset.mem_image.1 h''
        have hk' := Finset.mem_range.1 hk
        have hck := P.coord_le_mark hk'
        unfold markExp at hkeq
        have hsum : coord j + coord k = coord i := by omega
        exact pow_add_pow_ne_pow _ _ _ hsum
    · have := (P.mem_sgn_image h').1
      omega
  · have := P.mem_zreq_image h
    omega

/-- **The projection.**  For a single selected state `i`, the digit of `K · 3^(a i)` at the
target exponent `d + a j` is `1` exactly when `j = f i`, and `0` otherwise.  An individual
summand can reach that target only if `a i + a (f k) = a j + a k`; by the Sidon property the
alternatives are `k = i` with `f i = j`, or `i = j` with `f k = k`, and the phase split has
removed the second.  This is the coefficient statement of the routing note's §1. -/
theorem dg_romK_shift {i j : ℕ} (hi : i < P.n) (hj : j < P.n) :
    Ternary.dg (3 ^ coord i * P.romK) (P.mark + coord j) = if j = P.f i then 1 else 0 := by
  have hci := P.coord_le_mark hi
  have hsplit : P.mark + coord j = coord i + (P.mark + coord j - coord i) := by omega
  rw [hsplit, Ternary.dg_mul_pow_add, P.dg_romK]
  by_cases hjf : j = P.f i
  · subst hjf
    rw [if_pos (P.target_mem_expSet hi), if_pos rfl]
  · rw [if_neg (P.target_not_mem_expSet hi hj hjf), if_neg hjf]

/-! ### The marker and the two port digits -/

/-- The marker term counts the step. -/
theorem dg_romK_shift_mark {i : ℕ} (hi : i < P.n) :
    Ternary.dg (3 ^ coord i * P.romK) P.mark = 1 := by
  have hci := P.coord_le_mark hi
  have hsplit : P.mark = coord i + (P.mark - coord i) := by omega
  rw [hsplit, Ternary.dg_mul_pow_add, P.dg_romK, if_pos]
  show P.markExp i ∈ P.expSet
  rw [expSet]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩)))

/-- The sign port carries the sign label. -/
theorem dg_romK_shift_sgn {i : ℕ} (hi : i < P.n) :
    Ternary.dg (3 ^ coord i * P.romK) (P.mark + P.bs) = if P.sgn i then 1 else 0 := by
  have hm : P.mark = 3 ^ (P.n - 1) := rfl
  have hci := P.coord_le_mark hi
  have hc1 := one_le_coord i
  have hbs := P.bs_high
  have hbz := P.bz_high
  have hsplit : P.mark + P.bs = coord i + (P.mark + P.bs - coord i) := by omega
  rw [hsplit, Ternary.dg_mul_pow_add, P.dg_romK]
  by_cases hs : P.sgn i = true
  · rw [if_pos, if_pos hs]
    show P.sgnExp i ∈ P.expSet
    rw [expSet]
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hs⟩, rfl⟩))
  · rw [if_neg, if_neg hs]
    intro hmem
    rw [expSet] at hmem
    rcases Finset.mem_union.1 hmem with h | h
    · rcases Finset.mem_union.1 h with h' | h'
      · rcases Finset.mem_union.1 h' with h'' | h''
        · have := P.mem_edge_image h''; omega
        · have := P.mem_mark_image h''; omega
      · obtain ⟨k, hk, hkeq⟩ := Finset.mem_image.1 h'
        have hk' := Finset.mem_range.1 (Finset.mem_filter.1 hk).1
        have hck := P.coord_le_mark hk'
        unfold sgnExp at hkeq
        have hcc : coord k = coord i := by omega
        have : k = i := Nat.pow_right_injective (by norm_num) hcc
        exact hs (this ▸ (Finset.mem_filter.1 hk).2)
    · have := P.mem_zreq_image h; omega

/-- The zero-request port carries the zero-request label. -/
theorem dg_romK_shift_zreq {i : ℕ} (hi : i < P.n) :
    Ternary.dg (3 ^ coord i * P.romK) (P.mark + P.bz) = if P.zreq i then 1 else 0 := by
  have hm : P.mark = 3 ^ (P.n - 1) := rfl
  have hci := P.coord_le_mark hi
  have hc1 := one_le_coord i
  have hbs := P.bs_high
  have hbz := P.bz_high
  have hsplit : P.mark + P.bz = coord i + (P.mark + P.bz - coord i) := by omega
  rw [hsplit, Ternary.dg_mul_pow_add, P.dg_romK]
  by_cases hz : P.zreq i = true
  · rw [if_pos, if_pos hz]
    show P.zreqExp i ∈ P.expSet
    rw [expSet]
    exact Finset.mem_union_right _
      (Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hz⟩, rfl⟩)
  · rw [if_neg, if_neg hz]
    intro hmem
    rw [expSet] at hmem
    rcases Finset.mem_union.1 hmem with h | h
    · rcases Finset.mem_union.1 h with h' | h'
      · rcases Finset.mem_union.1 h' with h'' | h''
        · have := P.mem_edge_image h''; omega
        · have := P.mem_mark_image h''; omega
      · have := (P.mem_sgn_image h').2; omega
    · obtain ⟨k, hk, hkeq⟩ := Finset.mem_image.1 h
      have hk' := Finset.mem_range.1 (Finset.mem_filter.1 hk).1
      have hck := P.coord_le_mark hk'
      unfold zreqExp at hkeq
      have hcc : coord k = coord i := by omega
      have : k = i := Nat.pow_right_injective (by norm_num) hcc
      exact hz (this ▸ (Finset.mem_filter.1 hk).2)

/-- Every state's contribution but the last is divisible by three. -/
theorem three_dvd_tableTerm {i : ℕ} (hi : i < P.n - 1) : 3 ∣ P.tableTerm i := by
  have hlt := P.coord_lt_mark hi
  have hpos : 0 < coord (P.f i) := by unfold coord; positivity
  have hbs := P.bs_pos
  have hbz : 0 < P.bz := by have := P.bs_lt; omega
  unfold tableTerm
  refine Nat.dvd_add (Nat.dvd_add (Nat.dvd_add ?_ ?_) ?_) ?_
  · exact dvd_pow_self 3 (by omega)
  · exact dvd_pow_self 3 (by omega)
  · by_cases hs : P.sgn i
    · simp only [hs, if_true]; exact dvd_pow_self 3 (by omega)
    · simp [hs]
  · by_cases hz : P.zreq i
    · simp only [hz, if_true]; exact dvd_pow_self 3 (by omega)
    · simp [hz]

/-- The last state's contribution is one more than a multiple of three: its marker term is
`3^(d − d) = 1`, and every other term of it has a positive exponent. -/
theorem tableTerm_last_mod : P.tableTerm (P.n - 1) % 3 = 1 := by
  have hpos : 0 < coord (P.f (P.n - 1)) := by unfold coord; positivity
  have hbs := P.bs_pos
  have hbz : 0 < P.bz := by have := P.bs_lt; omega
  have hlast := P.coord_last
  have h1 : (3 : ℕ) ∣ 3 ^ (P.mark + coord (P.f (P.n - 1)) - coord (P.n - 1)) := by
    rw [hlast]; exact dvd_pow_self 3 (by omega)
  have h2 : (3 : ℕ) ^ (P.mark - coord (P.n - 1)) = 1 := by rw [hlast]; simp
  have h3 : (3 : ℕ) ∣ (if P.sgn (P.n - 1) then 3 ^ (P.mark + P.bs - coord (P.n - 1))
      else 0) := by
    by_cases hs : P.sgn (P.n - 1)
    · simp only [hs, if_true]; rw [hlast]; exact dvd_pow_self 3 (by omega)
    · simp [hs]
  have h4 : (3 : ℕ) ∣ (if P.zreq (P.n - 1) then 3 ^ (P.mark + P.bz - coord (P.n - 1))
      else 0) := by
    by_cases hz : P.zreq (P.n - 1)
    · simp only [hz, if_true]; rw [hlast]; exact dvd_pow_self 3 (by omega)
    · simp [hz]
  unfold tableTerm
  rw [h2]
  omega

/-- **The table is `1`-led at zero.** -/
theorem romK_mod : P.romK % 3 = 1 := by
  obtain ⟨N, hN⟩ : ∃ N, P.n = N + 1 := ⟨P.n - 1, by have := P.two_le; omega⟩
  have hNn : P.n - 1 = N := by omega
  have hlow : (3 : ℕ) ∣ ∑ i ∈ range N, P.tableTerm i := by
    refine Finset.dvd_sum fun i hi => P.three_dvd_tableTerm ?_
    rw [hNn]
    exact Finset.mem_range.1 hi
  have hlast := P.tableTerm_last_mod
  rw [hNn] at hlast
  unfold romK
  rw [hN, Finset.sum_range_succ]
  omega

theorem romK_lead : Ternary.Lead 0 1 P.romK :=
  ⟨P.romK, by rw [pow_zero, one_mul], P.romK_mod⟩

theorem one_lt_mark : 1 < P.mark := by
  have h : (3 : ℕ) ^ 1 ≤ 3 ^ (P.n - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by have := P.two_le; omega)
  show 1 < 3 ^ (P.n - 1)
  omega

/-! ### The compiled ROM meets the fixed grid inequalities -/

theorem sum_pow_lt (N : ℕ) : ∑ i ∈ range N, 3 ^ i < 3 ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hp : (0 : ℕ) < 3 ^ N := by positivity
    rw [Finset.sum_range_succ, pow_succ]
    omega

theorem expSet_subset : P.expSet ⊆ range (P.mark + P.bz) := by
  intro e he
  have hm : P.mark = 3 ^ (P.n - 1) := rfl
  have hbs := P.bs_high
  have hbz := P.bz_high
  rw [Finset.mem_range]
  rw [expSet] at he
  rcases Finset.mem_union.1 he with h | h
  · rcases Finset.mem_union.1 h with h' | h'
    · rcases Finset.mem_union.1 h' with h'' | h''
      · have := P.mem_edge_image h''; omega
      · have := P.mem_mark_image h''; omega
    · have := (P.mem_sgn_image h').2; omega
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h
    exact P.zreqExp_lt (Finset.mem_range.1 (Finset.mem_filter.1 hi).1)

/-- **`K < hz`.**  Every exponent of the table is below `d + bz`, and a sum of distinct
powers below a bound is below that bound's power. -/
theorem romK_lt_hz : P.romK < P.romhz := by
  calc P.romK = ∑ e ∈ P.expSet, 3 ^ e := P.romK_eq
    _ ≤ ∑ e ∈ range (P.mark + P.bz), 3 ^ e :=
        Finset.sum_le_sum_of_subset P.expSet_subset
    _ < 3 ^ (P.mark + P.bz) := sum_pow_lt _

theorem romS_pos : 0 < P.romS := by
  have hne : (range P.n).Nonempty := ⟨0, Finset.mem_range.2 (by have := P.two_le; omega)⟩
  exact Finset.sum_pos (fun i _ => by positivity) hne

theorem romK_pos : 0 < P.romK := by have := P.romK_mod; omega

/-- A grid numeral wide enough for the fixed program. -/
def zonChoice : ℕ :=
  81 + 4 * P.romS + P.romg * (3 ^ coord 0 + 1) + (P.romK + P.romg) * (P.romS + 1)
    + 8 * (P.romhs + P.romhz)

/-- **The compiled ROM satisfies the fixed grid inequalities.**  So the hypotheses of the
decoding are not vacuous: every compiled controller supplies a `ROM100.Ok`. -/
theorem rom_ok : (P.rom P.zonChoice 9).Ok where
  B0_ge := le_refl 9
  Zon_ge := by show 81 ≤ P.zonChoice; unfold zonChoice; omega
  Zon_gt_S := by show 4 * P.romS < P.zonChoice; unfold zonChoice; omega
  Zon_gt_gI := by
    show P.romg * (3 ^ coord 0 + 1) < P.zonChoice
    unfold zonChoice; omega
  Zon_gt_KgS := by
    show (P.romK + P.romg) * (P.romS + 1) < P.zonChoice
    unfold zonChoice; omega
  S_pos := P.romS_pos
  I_pos := by show (0 : ℕ) < 3 ^ coord 0; positivity
  g_pow := ⟨P.mark, rfl⟩
  K_lt_hz := P.romK_lt_hz
  K_pos := P.romK_pos
  Zon_gt_ports := by
    show 8 * (P.romhs + P.romhz) < P.zonChoice
    unfold zonChoice; omega

theorem pow_mem_le_romK {ex : ℕ} (hex : ex ∈ P.expSet) : 3 ^ ex ≤ P.romK := by
  rw [P.romK_eq]
  exact Finset.single_le_sum (f := fun k => 3 ^ k) (fun j _ => Nat.zero_le _) hex

theorem pow_coord_le_romS {i : ℕ} (hi : i < P.n) : 3 ^ coord i ≤ P.romS := by
  unfold romS
  exact Finset.single_le_sum (f := fun k => 3 ^ coord k) (fun j _ => Nat.zero_le _)
    (Finset.mem_range.2 hi)

/-- The compiled ROM has the Sidon layout, with `pK = d − amax = 0`. -/
theorem rom_sidon (Zon B0 : ℕ) : (P.rom Zon B0).Sidon P.mark 0 where
  g_eq := rfl
  hs_eq := ⟨P.bs, rfl⟩
  hz_eq := ⟨P.bz, rfl⟩
  K_lead := P.romK_lead

/-- And the state-column layout, with `amin = a 0 = 1` and `amax = d`. -/
theorem rom_layout (Zon B0 : ℕ) : (P.rom Zon B0).Layout P.mark 0 1 P.mark where
  I_eq := rfl
  pK_eq := by omega
  amin_lt := P.one_lt_mark
  amax_le := le_refl _

end Controller

/-- **The counter certificate over a compiled controller.**  For a solution of `Sys100`
whose ROM is compiled from a fixed controller, both layout hypotheses hold automatically,
so the decoding needs only the decoded-control bound `2q ≤ R D` of §5. -/
theorem decode_compiled_controller100 {P : Controller} {Zon B0 : ℕ}
    {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
    {e m u : ℕ}
    (hOk : (P.rom Zon B0).Ok)
    (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
    (hS : Sys100 (P.rom Zon B0) x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k
      o s w τ η ζ γ y)
    (hG : Geometry100 H R q e m u)
    (hDq : 2 * q ≤ R * D) :
    Doubled e Kp ∧ Doubled e Km ∧ Doubled e (H - D) ∧ Doubled e D ∧
    Doubled e (t - A0) ∧ Doubled e A0 ∧ Doubled e (t - A1) ∧ Doubled e A1 ∧
    Doubled e (z * H - PV) ∧ Doubled e PV ∧
    Doubled e ((P.rom Zon B0).S * H - PC) ∧ Doubled e PC :=
  decode_layout100 hOk hP hS hG (P.rom_sidon Zon B0) (P.rom_layout Zon B0) hDq

/-- **The counter certificate over a compiled controller, with its grid supplied.**  Every
positive solution of `Sys100` over a compiled controller's own ROM which satisfies the
decoded-control bound `2q ≤ R D` of §5 has all twelve conceptual fields equal to twice a
Boolean ternary word below `rep e`.  Nothing else is assumed: the fixed grid inequalities
and the radix geometry are both supplied by the compilation. -/
theorem decode_controller100 {P : Controller}
    {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
    (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
    (hS : Sys100 (P.rom P.zonChoice 9) x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h
      i j k o s w τ η ζ γ y)
    (hDq : 2 * q ≤ R * D) :
    ∃ e, Doubled e Kp ∧ Doubled e Km ∧ Doubled e (H - D) ∧ Doubled e D ∧
      Doubled e (t - A0) ∧ Doubled e A0 ∧ Doubled e (t - A1) ∧ Doubled e A1 ∧
      Doubled e (z * H - PV) ∧ Doubled e PV ∧
      Doubled e ((P.rom P.zonChoice 9).S * H - PC) ∧ Doubled e PC := by
  obtain ⟨e, m, u, hG⟩ := geometry100 hP hS P.rom_ok.Zon_ge P.rom_ok.B0_ge
  exact ⟨e, decode_compiled_controller100 P.rom_ok hP hS hG hDq⟩

/-- **The ROM fits inside one row.**  The fixed grid inequalities put the zero-request port
below the grid width, so for a compiled controller every table exponent is below the row
width `m`.  This is what keeps one row's table output from spilling into the next, and it
is the first hypothesis of the row transport. -/
theorem rom_span_lt100 {P : Controller} {Zon B0 : ℕ}
    {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
    {e m u : ℕ}
    (hOk : (P.rom Zon B0).Ok)
    (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
    (hS : Sys100 (P.rom Zon B0) x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k
      o s w τ η ζ γ y)
    (hG : Geometry100 H R q e m u) :
    P.mark + P.bz < m := by
  have h : (3 : ℕ) ^ (P.mark + P.bz) < 3 ^ m := by
    have h0 := hz_lt_R hOk hP hS
    rw [hG.hR] at h0
    exact h0
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h

/-- **One row's table output stays inside that row.**  Every exponent of `K`, shifted by any
state coordinate, is below the row width, because the table times the state word fits inside
a row.  This is the routing note's condition `W > K S`, and it is what lets the projection
be read row by row. -/
theorem shift_span_lt100 {P : Controller} {Zon B0 : ℕ}
    {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
    {e m u ex st : ℕ}
    (hOk : (P.rom Zon B0).Ok)
    (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
    (hS : Sys100 (P.rom Zon B0) x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k
      o s w τ η ζ γ y)
    (hG : Geometry100 H R q e m u)
    (hex : ex ∈ P.expSet) (hst : st < P.n) :
    ex + coord st < m := by
  have hKS := KS_lt_R hOk hP hS
  have h1 : (3 : ℕ) ^ ex ≤ P.romK := P.pow_mem_le_romK hex
  have h2 : (3 : ℕ) ^ coord st ≤ P.romS := P.pow_coord_le_romS hst
  have h5 : (3 : ℕ) ^ (ex + coord st) < 3 ^ m := by
    rw [pow_add]
    calc 3 ^ ex * 3 ^ coord st ≤ P.romK * P.romS := Nat.mul_le_mul h1 h2
      _ < R := hKS
      _ = 3 ^ m := hG.hR
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h5

end Jones1980
