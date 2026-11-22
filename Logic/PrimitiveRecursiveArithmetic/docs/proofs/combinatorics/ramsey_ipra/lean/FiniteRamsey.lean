import Std

/-!
# Finite Ramsey by constructive tail stabilization

Checked with Lean 4.19.0 and its standard library. The finite input is an ordered
list. Its sublists model subsets when the input has no repetitions. The color
map may be arbitrary on lists of the wrong length.
-/

namespace FiniteRamsey

def patterns {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => patterns xs ++ (patterns xs).map (x :: ·)

theorem patterns_complete {α : Type} {u xs : List α} (h : u.Sublist xs) :
    u ∈ patterns xs := by
  induction h with
  | slnil => simp [patterns]
  | cons x h ih => exact List.mem_append_left _ ih
  | cons₂ x h ih => exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩)

theorem patterns_length {α : Type} (xs : List α) :
    (patterns xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [patterns, ih, Nat.pow_succ, Nat.mul_two]

private theorem count_partition {α : Type} (p : α → Bool) (xs : List α) :
    (xs.filter p).length + (xs.filter (fun x => !(p x))).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x <;> simp [List.filter_cons, hp] <;> omega

/-- Strict-budget finite pigeonhole. Each step uses the decidable size of one fiber. -/
theorem bucket {α : Type} (q n : Nat) (c : α → Nat) (xs : List α)
    (range : ∀ x ∈ xs, c x < q) (enough : q * n < xs.length) :
    ∃ ys : List α, ys.Sublist xs ∧ n < ys.length ∧ ∃ d, ∀ y ∈ ys, c y = d := by
  induction q generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at enough
    | cons x xs => exact False.elim (Nat.not_lt_zero _ (range x (by simp)))
  | succ q ih =>
    let p := fun x => c x == q
    let yes := xs.filter p
    let no := xs.filter (fun x => !(p x))
    by_cases large : n < yes.length
    · refine ⟨yes, List.filter_sublist, large, q, ?_⟩
      intro y hy
      have he := (List.mem_filter.mp hy).2
      simpa [p] using he
    · have split : yes.length + no.length = xs.length := count_partition p xs
      have enough' : q * n < no.length := by
        rw [Nat.succ_mul] at enough
        omega
      have range' : ∀ x ∈ no, c x < q := by
        intro x hx
        obtain ⟨hxmem, hxne⟩ := List.mem_filter.mp hx
        have hneq : c x ≠ q := by simpa [p] using hxne
        have := range x hxmem
        omega
      obtain ⟨ys, hsub, hn, hd⟩ := ih no range' enough'
      exact ⟨ys, hsub.trans List.filter_sublist, hn, hd⟩

/-- Thin once for every test. Colors of every test agree throughout the survivor. -/
theorem thin {α β : Type} {q : Nat} (test : β → α → Fin q)
    (ts : List β) (xs : List α) (n : Nat) (enough : q ^ ts.length * n < xs.length) :
    ∃ ys : List α, ys.Sublist xs ∧ n < ys.length ∧
      ∀ t ∈ ts, ∀ y ∈ ys, ∀ z ∈ ys, test t y = test t z := by
  induction ts generalizing xs with
  | nil => exact ⟨xs, List.Sublist.refl _, by simpa using enough, by simp⟩
  | cons t ts ih =>
    have budget : q * (q ^ ts.length * n) < xs.length := by
      simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using enough
    obtain ⟨ys, hys, hny, _, common⟩ :=
      bucket q (q ^ ts.length * n) (fun x => (test t x).val) xs
        (fun x _ => (test t x).isLt) budget
    obtain ⟨zs, hzs, hnz, rest⟩ := ih ys hny
    refine ⟨zs, hzs.trans hys, hnz, ?_⟩
    intro a ha y hy z hz
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Fin.ext ((common y (hzs.subset hy)).trans (common z (hzs.subset hz)).symm)
    · exact rest a ha y hy z hz

/-- A pool longer than this budget supplies the prescribed number of pivots
and retains a sentinel. The tests per round use the uniform factor `scale`. -/
def reserve (scale : Nat) : Nat → Nat
  | 0 => 0
  | s + 1 => scale * (reserve scale s + 1)

def bound (q t : Nat) : Nat → Nat
  | 0 => t
  | r + 1 =>
    let m := bound q t r
    reserve (q ^ (2 ^ m)) m + 1

/-- Earlier choices agree with every remaining sentinel candidate on all extensions. -/
def Stable {q : Nat} (c : List Nat → Fin q) (picked pool : List Nat) : Prop :=
  ∀ (u : List Nat) (y : Nat), (y :: u).Sublist picked →
    ∀ z ∈ pool, c (y :: u) = c (z :: u)

private theorem snoc_of_nonempty {α : Type} (xs : List α) (h : 0 < xs.length) :
    ∃ ys x, xs = ys ++ [x] := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    cases xs with
    | nil => exact ⟨[], x, rfl⟩
    | cons a as =>
      obtain ⟨ys, z, he⟩ := ih (by simp)
      exact ⟨x :: ys, z, congrArg (x :: ·) he⟩

/-- Build a stable picked list. In this orientation the pool is left of the
picked list, so each new pivot is taken from the right end of the survivor. -/
theorem stabilize {q : Nat} (hq : 0 < q) (c : List Nat → Fin q) (m s : Nat)
    (picked pool : List Nat) (count : picked.length + s = m)
    (enough : reserve (q ^ (2 ^ m)) s < pool.length)
    (old : Stable c picked pool) :
    ∃ (ys : List Nat) (a : Nat), ys.Sublist (pool ++ picked) ∧ ys.length = m ∧
      Stable c ys [a] := by
  induction s generalizing picked pool with
  | zero =>
    obtain ⟨pool', a, he⟩ := snoc_of_nonempty pool enough
    refine ⟨picked, a, List.sublist_append_right _ _, by simpa using count, ?_⟩
    intro u y hy z hz
    have hza : z = a := by simpa using hz
    subst z
    exact old u y hy a (by simp [he])
  | succ s ih =>
    let scale := q ^ (2 ^ m)
    let n := reserve scale s + 1
    have hpat : (patterns picked).length ≤ 2 ^ m := by
      rw [patterns_length]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have smaller := Nat.mul_le_mul_right n (Nat.pow_le_pow_right hq hpat)
    have budget : q ^ (patterns picked).length * n < pool.length :=
      Nat.lt_of_le_of_lt smaller enough
    obtain ⟨ys, hys, hlen, equal⟩ :=
      thin (fun u y => c (y :: u)) (patterns picked) pool n budget
    obtain ⟨tail, x, he⟩ := snoc_of_nonempty ys (by omega)
    subst ys
    have hx : x ∈ tail ++ [x] := by simp
    have htail : ∀ z ∈ tail, z ∈ tail ++ [x] := fun z hz => List.mem_append_left _ hz
    have next : Stable c (x :: picked) tail := by
      intro u y h z hz
      rcases List.sublist_cons_iff.mp h with hp | ⟨v, hv, hsub⟩
      · exact old u y hp z (hys.subset (htail z hz))
      · cases hv
        exact equal u (patterns_complete hsub) x hx z (htail z hz)
    have enough' : reserve scale s < tail.length := by
      simp [n] at hlen
      omega
    obtain ⟨out, a, hout, hm, ha⟩ :=
      ih (x :: picked) tail (by simp; omega) enough' next
    have step : (tail ++ (x :: picked)).Sublist (pool ++ picked) := by
      simpa [List.append_assoc] using hys.append_right picked
    exact ⟨out, a, hout.trans step, hm, ha⟩

def Homogeneous {q : Nat} (c : List Nat → Fin q) (r : Nat)
    (xs : List Nat) (d : Fin q) : Prop :=
  ∀ u : List Nat, u.Sublist xs → u.length = r → c u = d

/-- All arities, all positive color counts, exact target size, arbitrary base list. -/
theorem finiteRamsey {q : Nat} (hq : 0 < q) (t r : Nat) (c : List Nat → Fin q)
    (xs : List Nat) (enough : bound q t r ≤ xs.length) :
    ∃ (ys : List Nat) (d : Fin q), ys.Sublist xs ∧ ys.length = t ∧ Homogeneous c r ys d := by
  induction r generalizing c xs with
  | zero =>
    refine ⟨xs.take t, c [], List.take_sublist .., ?_, ?_⟩
    · simp [List.length_take, Nat.min_eq_left (show t ≤ xs.length from enough)]
    · intro u _ hu
      rw [List.eq_nil_of_length_eq_zero hu]
  | succ r ih =>
    let m := bound q t r
    have budget : reserve (q ^ (2 ^ m)) m < xs.length := Nat.lt_of_succ_le enough
    obtain ⟨picked, a, hp, hm, stable⟩ :=
      stabilize hq c m m [] xs (by simp) budget (by simp [Stable])
    have hp' : picked.Sublist xs := by simpa using hp
    obtain ⟨ys, d, hy, ht, hd⟩ := ih (fun u => c (a :: u)) picked (Nat.le_of_eq hm.symm)
    refine ⟨ys, d, hy.trans hp', ht, ?_⟩
    intro v hv hl
    cases v with
    | nil => exact False.elim (Nat.noConfusion hl)
    | cons y u =>
      have hu : u.Sublist ys := (List.Sublist.cons y (List.Sublist.refl u)).trans hv
      exact (stable u y (hv.trans hy) a (by simp)).trans
        (hd u hu (Nat.succ.inj hl))

/-- The initial segment of naturals is the standard finite vertex set. -/
theorem rangeRamsey {q : Nat} (hq : 0 < q) (t r N : Nat) (c : List Nat → Fin q)
    (h : bound q t r ≤ N) :
    ∃ (ys : List Nat) (d : Fin q), ys.Sublist (List.range N) ∧ ys.length = t ∧
      Homogeneous c r ys d :=
  finiteRamsey hq t r c (List.range N) (by simpa using h)

theorem patterns_sound {α : Type} {u xs : List α} (h : u ∈ patterns xs) :
    u.Sublist xs := by
  induction xs generalizing u with
  | nil =>
    have hu : u = [] := by simpa [patterns] using h
    subst u
    exact .slnil
  | cons x xs ih =>
    rcases List.mem_append.mp h with a | b
    · exact (ih a).cons x
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp b
      exact (ih hv).cons₂ x

/-- Exhaustive certificate test, decidable on a finite candidate. -/
def checks {q : Nat} (t r : Nat) (c : List Nat → Fin q) (v : List Nat × Fin q) : Bool :=
  v.1.length == t && (patterns v.1).all (fun u => u.length != r || c u == v.2)

theorem checks_spec {q : Nat} (t r : Nat) (c : List Nat → Fin q) (ys : List Nat)
    (d : Fin q) :
    checks t r c (ys, d) = true ↔ ys.length = t ∧ Homogeneous c r ys d := by
  simp only [checks, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨hl, ?_⟩
    intro u hu hs
    simpa [hs] using h u (patterns_complete hu)
  · rintro ⟨hl, h⟩
    refine ⟨hl, ?_⟩
    intro u hu
    by_cases hs : u.length = r
    · simp [hs, h u (patterns_sound hu) hs]
    · simp [hs]

/-- Enumerate pairs of a vertex sublist and a candidate common color. -/
def candidates (q : Nat) (xs : List Nat) : List (List Nat × Fin q) :=
  (patterns xs).flatMap (fun ys => (List.ofFn (fun i : Fin q => i)).map (fun d => (ys, d)))

theorem candidates_spec {q : Nat} {ys xs : List Nat} {d : Fin q} :
    (ys, d) ∈ candidates q xs ↔ ys.Sublist xs := by
  constructor
  · intro h
    obtain ⟨zs, hz, hmem⟩ := List.mem_flatMap.mp h
    obtain ⟨_, _, he⟩ := List.mem_map.mp hmem
    cases he
    exact patterns_sound hz
  · intro h
    apply List.mem_flatMap.mpr
    exact ⟨ys, patterns_complete h, List.mem_map.mpr ⟨d, List.mem_ofFn.mpr ⟨d, rfl⟩, rfl⟩⟩

/-- A total executable witness extractor. Its search is bounded by the actual
input length and can succeed below the sufficient theoretical bound as well. -/
def search {q : Nat} (t r : Nat) (c : List Nat → Fin q) (xs : List Nat) :
    Option (List Nat × Fin q) :=
  (candidates q xs).find? (checks t r c)

theorem search_sound {q : Nat} {t r : Nat} {c : List Nat → Fin q}
    {xs ys : List Nat} {d : Fin q} (h : search t r c xs = some (ys, d)) :
    ys.Sublist xs ∧ ys.length = t ∧ Homogeneous c r ys d :=
  ⟨candidates_spec.mp (List.mem_of_find?_eq_some h),
    (checks_spec t r c ys d).mp (List.find?_some h)⟩

theorem search_total {q : Nat} (hq : 0 < q) (t r : Nat) (c : List Nat → Fin q)
    (xs : List Nat) (enough : bound q t r ≤ xs.length) :
    (search t r c xs).isSome = true := by
  obtain ⟨ys, d, hy, ht, hd⟩ := finiteRamsey hq t r c xs enough
  exact List.find?_isSome.mpr
    ⟨(ys, d), candidates_spec.mpr hy, (checks_spec t r c ys d).mpr ⟨ht, hd⟩⟩

/-- Arithmetic address of a set, on the increasing sublists of `range N`. -/
def mask : List Nat → Nat
  | [] => 0
  | x :: xs => 2 ^ x + mask xs

/-- Total arithmetic table lookup. The final remainder also interprets malformed
digits. For valid digits it is the identity, including for the one-color case. -/
def tableColor (q : Nat) (hq : 0 < q) (code : Nat) (u : List Nat) : Fin q :=
  let b := max 2 q
  ⟨(code / (b ^ mask u) % b) % q, Nat.mod_lt _ hq⟩

theorem tableColor_of_valid (q : Nat) (hq : 0 < q) (code : Nat) (u : List Nat)
    (valid : code / ((max 2 q) ^ mask u) % (max 2 q) < q) :
    (tableColor q hq code u).val = code / ((max 2 q) ^ mask u) % (max 2 q) :=
  Nat.mod_eq_of_lt valid

/-- For every natural table code the search terminates with a valid certificate
on a long enough initial segment. Ordinary list search suffices for this specialization. -/
theorem codedSearch (q : Nat) (hq : 0 < q) (t r n code : Nat)
    (h : bound q t r ≤ n) :
    ∃ ys d, search t r (tableColor q hq code) (List.range n) = some (ys, d) ∧
      ys.Sublist (List.range n) ∧ ys.length = t ∧ Homogeneous (tableColor q hq code) r ys d := by
  obtain ⟨⟨ys, d⟩, hs⟩ := Option.isSome_iff_exists.mp
    (search_total hq t r (tableColor q hq code) (List.range n) (by simpa using h))
  exact ⟨ys, d, hs, search_sound hs⟩

/-- With a separate target for each color, a bound for their common upper limit
suffices. The homogeneous subset produced here has the exact size requested. -/
theorem asymmetricRamsey {q : Nat} (hq : 0 < q) (t r : Nat)
    (target : Fin q → Nat) (ht : ∀ d, target d ≤ t) (c : List Nat → Fin q)
    (xs : List Nat) (enough : bound q t r ≤ xs.length) :
    ∃ (ys : List Nat) (d : Fin q), ys.Sublist xs ∧ ys.length = target d ∧
      Homogeneous c r ys d := by
  obtain ⟨ys, d, hy, hlen, hd⟩ := finiteRamsey hq t r c xs enough
  have small : (ys.take (target d)).Sublist ys := List.take_sublist ..
  exact ⟨ys.take (target d), d, small.trans hy, by simp [hlen, Nat.min_eq_left (ht d)],
    fun u hu hl => hd u (hu.trans small) hl⟩

/- Reproducible small exhaustive examples. Edges of the 5-cycle form one color,
and their complements form the other. Vertex 5 in the extension has only color
0 edges. Both tests use the same executable search as the general theorem. -/
private def cycleColor : List Nat → Fin 2
  | [x, y] => if y < 5 && (y == x + 1 || (x == 0 && y == 4)) then 1 else 0
  | _ => 0

example : search 3 2 cycleColor (List.range 5) = none := by decide
example : (search 3 2 cycleColor (List.range 6)).isSome = true := by decide
example : mask [0, 2, 5] = 37 := by decide
example : (tableColor 2 (by decide) (2 ^ 37) [0, 2, 5]).val = 1 := by decide

end FiniteRamsey
