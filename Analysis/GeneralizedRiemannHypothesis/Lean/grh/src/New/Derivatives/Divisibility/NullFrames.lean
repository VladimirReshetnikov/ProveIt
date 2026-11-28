import Lib.Cohomology.Etale.Basic
import Lib.General.Algebra.SeriesCongruences

/-!
# The change of directions

This file gives matrices over the integers of `ℂ_p`, one for each place and height, that change
given directions. For a divisor `π` of `p`, the pairings `∑ β_a ^ p ^ e * β'_a` of new directions at
a place and at its partner become divisible by `π`, apart from the exempt pairs of heights, which
involve a marked place. The valuations of the determinants, one for each column, add up to at most
the deduction: `v(π)` times the sum of the numbers `New.deductionTerm`.

## Main definitions and results

* `New.deductionTerm`: the term of the deduction for a place, a partner and an exponent `e`.
* `New.CongruenceChoice`, `New.exists_congruenceChoice_cost_eq_and_covers`: which congruences are
  imposed for a place and a partner; a choice of cost `New.deductionTerm` covers the pairs of
  heights that are not exempt (`New.IsExemptPair`).
* `New.newDirection`, `New.exists_newDirection_dvd`: integral changes of direction at each place
  and height that make the pairings that are not exempt divisible by `π`, and whose determinants
  cost at most the deduction.

Notions from other files:
* `New.valRingCp p`: the integers of `ℂ_p`.
-/

/-!
## Changing the directions

Finitely many congruences on the rows of one matrix are met by elimination, at the price of the
product of the moduli.
-/

section NullFrames

open Finset Matrix

/-- One step of elimination over the integers `valRingCp p` of `ℂ_p`. Given the values `a k` of a
linear form on the rows of a matrix and a modulus `α`, there are row operations `u`, with
determinant dividing `α`, after which `α` divides all values. -/
lemma New.exists_det_dvd_and_dvd_mulVec {p : ℕ} [Fact p.Prime] {m : ℕ} (a : Fin m → valRingCp p)
    (α : valRingCp p) :
    ∃ u : Matrix (Fin m) (Fin m) (valRingCp p), u.det ∣ α ∧ ∀ k : Fin m, α ∣ (u *ᵥ a) k := by
  obtain h_empty | h_nonempty := isEmpty_or_nonempty (Fin m)
  · exact ⟨1, by simp, fun k ↦ h_empty.elim k⟩
  -- Take a row `k₀` of least valuation, subtract multiples of it from the other rows so that their
  -- values vanish, and multiply it by `α`.
  obtain ⟨k₀, h_max⟩ := Finite.exists_max fun k ↦ ‖(a k : ℂ_[p])‖
  have h_dvd (k : Fin m) : ∃ c : valRingCp p, a k = a k₀ * c := dvd_iff_norm_le.2 (h_max k)
  choose c hc using h_dvd
  let b (k : Fin m) : valRingCp p := if k = k₀ then α else -c k
  let u : Matrix (Fin m) (Fin m) (valRingCp p) := updateCol 1 k₀ b
  have h_det : u.det = α := by simp [u, b, ← cramer_apply, cramer_one]
  have h_value (k : Fin m) : (u *ᵥ a) k = b k * a k₀ + if k = k₀ then 0 else a k := by
    have h_rest : ∑ l ∈ univ.erase k₀, u k l * a l =
        ∑ l ∈ univ.erase k₀, if k = l then a l else 0 :=
      sum_congr rfl fun l hl ↦ by simp [u, ne_of_mem_erase hl, Matrix.one_apply]
    rw [mulVec, dotProduct, ← add_sum_erase univ _ (mem_univ k₀), h_rest]
    simp [u]
  refine ⟨u, h_det.dvd, fun k ↦ ?_⟩
  obtain rfl | hk := eq_or_ne k k₀
  · simp [h_value, b]
  · simp [h_value, b, hk, hc k, mul_comm]

/-- For finitely many linear forms with coefficient vectors `A i` and moduli `α i` over the integers
`valRingCp p` of `ℂ_p`, there is a square matrix `g`, with determinant dividing the product of the
moduli, such that `α i` divides the value of the `i`-th form on every row of `g`. -/
lemma New.exists_det_dvd_prod_and_dvd_mulVec {p : ℕ} [Fact p.Prime] {ι : Type*} {m : ℕ}
    (t : Finset ι) (A : ι → Fin m → valRingCp p) (α : ι → valRingCp p) :
    ∃ g : Matrix (Fin m) (Fin m) (valRingCp p),
      g.det ∣ ∏ i ∈ t, α i ∧ ∀ i ∈ t, ∀ k : Fin m, α i ∣ (g *ᵥ A i) k := by
  -- Start from the identity matrix and treat the forms one after the other.
  induction t using Finset.cons_induction with
  | empty => exact ⟨1, by simp, by simp⟩
  | cons i t hi ih =>
    obtain ⟨g, hg_det, hg_dvd⟩ := ih
    obtain ⟨u, hu_det, hu_dvd⟩ := exists_det_dvd_and_dvd_mulVec (g *ᵥ A i) (α i)
    refine ⟨u * g, ?_, fun j hj k ↦ ?_⟩
    · simpa only [det_mul, prod_cons] using mul_dvd_mul hu_det hg_det
    · rw [← mulVec_mulVec]
      obtain rfl | hj_old := mem_cons.1 hj
      · exact hu_dvd k
      · -- The new rows are integral combinations of the old ones.
        rw [mulVec, dotProduct]
        exact dvd_sum fun l _ ↦ (hg_dvd j hj_old l).mul_left (u k l)

/-- Let `π` divide `p`, and let `root x` be a `p ^ e`-th root of `x`. If `root π` divides the linear
form `∑ root (y' a) * β a`, then `π` divides the pairing `∑ β a ^ p ^ e * y' a`, as `p ^ e`-th
powers are additive modulo `p`. -/
lemma New.dvd_sum_pow_mul_of_root_dvd {p : ℕ} [Fact p.Prime] {O n : Type*} [CommRing O] [Fintype n]
    {π : O} (hπ : π ∣ (p : O)) {e : ℕ} {root : O → O} (h_root : ∀ x : O, root x ^ p ^ e = x)
    {β y' : n → O} (h_dvd : root π ∣ ∑ a : n, root (y' a) * β a) :
    π ∣ ∑ a : n, β a ^ p ^ e * y' a := by
  have h_pow : π ∣ (∑ a, root (y' a) * β a) ^ p ^ e := by
    simpa only [h_root] using pow_dvd_pow_of_dvd h_dvd (p ^ e)
  have h_additive : π ∣ (∑ a, root (y' a) * β a) ^ p ^ e - ∑ a, β a ^ p ^ e * y' a := by
    simpa only [mul_pow, h_root, mul_comm] using
      dvd_sum_pow_sub_sum hπ univ (fun a ↦ root (y' a) * β a) e
  exact (dvd_sub_right h_pow).1 h_additive

/-- The value of the form with coefficients `∑ a, x a * y a k` on a row `u` is the pairing of `x`
with the combination of the vectors `y · k` given by `u`. -/
lemma New.dotProduct_sum_mul {O n : Type*} [CommRing O] [Fintype n] {h : ℕ} (u : Fin h → O)
    (x : n → O) (y : n → ℕ → O) :
    (u ⬝ᵥ fun k : Fin h ↦ ∑ a : n, x a * y a k) =
      ∑ a : n, x a * (u ⬝ᵥ fun k : Fin h ↦ y a k) := by
  simp only [dotProduct, mul_sum, mul_left_comm]
  exact sum_comm

/-- The term of the deduction, in units of `v(π)`, for a place `σ`, a partner `σ'` and an exponent
`e`, when `κ σ h` is the number of columns of height `h` at `σ`, counted only for `h < n'`, and
`ev` is the set of marked places. Let `t σ` be the number of columns of height one (`0` if `σ` is
marked), `r σ` the number of columns of height other than one, and `B σ` the sum of their heights,
that is, their number of boxes. The term is the real number
`min (t σ / p ^ e) (r σ' + t σ') + r σ / p ^ e + min (B σ / p ^ e) (B σ')`. -/
noncomputable def New.deductionTerm {Φ : Type*} [DecidableEq Φ] (p : ℕ) (κ : Φ → ℕ → ℕ) (n' : ℕ)
    (ev : Finset Φ) (σ σ' : Φ) (e : ℕ) : ℝ :=
  let t (σ : Φ) : ℕ := ∑ h ∈ range n', if h = 1 ∧ σ ∉ ev then κ σ h else 0
  let r (σ : Φ) : ℕ := ∑ h ∈ range n', if h = 1 then 0 else κ σ h
  let B (σ : Φ) : ℕ := ∑ h ∈ range n', h * if h = 1 then 0 else κ σ h
  min (t σ / p ^ e : ℝ) (r σ' + t σ') + r σ / p ^ e + min (B σ / p ^ e : ℝ) (B σ')

/-- The pair of heights `h` at the place `σ` and `h'` at the place `σ'` is exempt for the set `ev`
of marked places: `h = 1`, and either `σ` is marked or `h' = 1` and `σ'` is marked. -/
def New.IsExemptPair {Φ : Type*} (ev : Finset Φ) (σ σ' : Φ) (h h' : ℕ) : Prop :=
  h = 1 ∧ (σ ∈ ev ∨ h' = 1 ∧ σ' ∈ ev)

/-- A choice of congruences for a place (the source) and its partner: for each height `h`, which
of four kinds of congruence are imposed on the rows of height `h`. -/
structure New.CongruenceChoice where
  /-- Congruences on all `h` entries of each row at the source. -/
  sourceEntries : ℕ → Bool
  /-- One congruence on the pairing of each row at the source with direction `0` at the partner. -/
  sourcePairing : ℕ → Bool
  /-- Congruences on all `h` entries of each row at the partner. -/
  partnerEntries : ℕ → Bool
  /-- One congruence on the pairing of each row at the partner with direction `0` at the source. -/
  partnerPairing : ℕ → Bool

/-- The two sides of a pairing from a place to its partner. -/
inductive New.PairingSide
  /-- The side of the place itself. -/
  | source
  /-- The side of the partner. -/
  | partner
  deriving DecidableEq

namespace New.PairingSide

instance : Fintype PairingSide where
  elems := {source, partner}
  complete side := by cases side <;> simp

/-- The place of a side, for a pairing from `σ` to `σ'`. -/
def place {Φ : Type*} (side : PairingSide) (σ σ' : Φ) : Φ :=
  match side with
  | source => σ
  | partner => σ'

/-- For a pairing at the exponent `e`, congruences on a side are taken modulo a `p ^ r`-th root of
`π`, where `r` is this number: `e` at the source and `0` at the partner. -/
def rootExponent (side : PairingSide) (e : ℕ) : ℕ :=
  match side with
  | source => e
  | partner => 0

lemma sum_univ {M : Type*} [AddCommMonoid M] (f : PairingSide → M) :
    ∑ side : PairingSide, f side = f source + f partner :=
  sum_pair (by decide : source ≠ partner)

end New.PairingSide

namespace New.CongruenceChoice

/-- The number of congruences on a row of height `h` at the source. -/
def sourceCount (c : CongruenceChoice) (h : ℕ) : ℕ :=
  (if c.sourcePairing h then 1 else 0) + h * if c.sourceEntries h then 1 else 0

/-- The number of congruences on a row of height `h` at the partner. -/
def partnerCount (c : CongruenceChoice) (h : ℕ) : ℕ :=
  (if c.partnerPairing h then 1 else 0) + h * if c.partnerEntries h then 1 else 0

/-- The number of congruences on the heights `h < N`, counted once for each of the `κ h` columns
at the source, with weight `1 / p ^ e`, and once for each of the `κ' h` columns at the partner. -/
noncomputable def cost (c : CongruenceChoice) (p e N : ℕ) (κ κ' : ℕ → ℕ) : ℝ :=
  ∑ h ∈ range N, (c.sourceCount h * κ h / p ^ e + c.partnerCount h * κ' h : ℝ)

/-- The pair of heights `h` at the source and `h'` at the partner is covered by one of the four
kinds of congruence. A congruence on a pairing counts only if the height on the other side is
one. -/
def Covers (c : CongruenceChoice) (h h' : ℕ) : Prop :=
  c.partnerPairing h' ∧ h = 1 ∨ c.partnerEntries h' ∨
    c.sourcePairing h ∧ h' = 1 ∨ c.sourceEntries h

/-- Whether a congruence is imposed on the rows of height `h` on the given side, on the pairing
(`none`) or on the entry `k` (`some k`). -/
def imposes (c : CongruenceChoice) (h : ℕ) : PairingSide → Option (Fin h) → Bool
  | .source, none => c.sourcePairing h
  | .source, some _ => c.sourceEntries h
  | .partner, none => c.partnerPairing h
  | .partner, some _ => c.partnerEntries h

lemma sum_imposes_source (c : CongruenceChoice) (h : ℕ) :
    ∑ form : Option (Fin h), (if c.imposes h .source form then 1 else 0) = c.sourceCount h :=
  calc _ = (if c.sourcePairing h then 1 else 0) +
        ∑ _k : Fin h, if c.sourceEntries h then 1 else 0 := Fintype.sum_option _
    _ = c.sourceCount h := by rw [sourceCount, Fin.sum_const, smul_eq_mul]

lemma sum_imposes_partner (c : CongruenceChoice) (h : ℕ) :
    ∑ form : Option (Fin h), (if c.imposes h .partner form then 1 else 0) = c.partnerCount h :=
  calc _ = (if c.partnerPairing h then 1 else 0) +
        ∑ _k : Fin h, if c.partnerEntries h then 1 else 0 := Fintype.sum_option _
    _ = c.partnerCount h := by rw [partnerCount, Fin.sum_const, smul_eq_mul]

end New.CongruenceChoice

/-- For a place `σ`, a partner `σ'` and an exponent `e` there is a choice of congruences
(`CongruenceChoice`): for each height, whether a row at `σ`, and a row at `σ'`, gets one congruence
on its pairing with direction `0` at the other place, one on each entry, or both. Its `cost`, the
number of congruences on all columns with those at `σ` weighted by `1 / p ^ e`, equals
`deductionTerm`. Each pair of heights `h` at `σ` and `h'` at `σ'` that is not exempt is covered
(`Covers`): there are congruences on the entries of one of the two rows, or on the pairing of one of
them and the other height is one. -/
lemma New.exists_congruenceChoice_cost_eq_and_covers {Φ : Type*} [DecidableEq Φ] (p : ℕ)
    (κ : Φ → ℕ → ℕ) (N : ℕ) (marked : Finset Φ) (σ σ' : Φ) (e : ℕ) :
    ∃ c : CongruenceChoice,
      c.cost p e N (κ σ) (κ σ') = deductionTerm p κ N marked σ σ' e ∧
      ∀ h h' : ℕ, ¬IsExemptPair marked σ σ' h h' → c.Covers h h' := by
  -- The choice always pays for the columns of height other than one at `σ`, and takes the cheaper
  -- side in two comparisons.
  let oneCols (τ : Φ) : ℕ := ∑ h ∈ range N, if h = 1 ∧ τ ∉ marked then κ τ h else 0
  let neOneCols (τ : Φ) : ℕ := ∑ h ∈ range N, if h = 1 then 0 else κ τ h
  let neOneBoxes (τ : Φ) : ℕ := ∑ h ∈ range N, h * if h = 1 then 0 else κ τ h
  have h_deduction : deductionTerm p κ N marked σ σ' e =
      min (oneCols σ / p ^ e : ℝ) (neOneCols σ' + oneCols σ') + neOneCols σ / p ^ e +
        min (neOneBoxes σ / p ^ e : ℝ) (neOneBoxes σ') := rfl
  -- The first minimum decides between the entries of height one at `σ` and the pairings at `σ'`,
  -- the second between the entries of the heights other than one at `σ` and at `σ'`.
  let oneAtSource : Prop := (oneCols σ / p ^ e : ℝ) ≤ neOneCols σ' + oneCols σ'
  let neOneAtSource : Prop := (neOneBoxes σ / p ^ e : ℝ) ≤ neOneBoxes σ'
  let c : CongruenceChoice :=
    { sourceEntries h := decide (if h = 1 then σ ∉ marked ∧ oneAtSource else neOneAtSource)
      sourcePairing h := decide (h ≠ 1)
      partnerEntries h := decide (h ≠ 1 ∧ ¬neOneAtSource)
      partnerPairing h := decide (¬oneAtSource ∧ (h = 1 → σ' ∉ marked)) }
  -- The number of congruences on all columns at `σ` and at `σ'`, computed height by height.
  have source_sum : ∑ h ∈ range N, c.sourceCount h * κ σ h =
      (if oneAtSource then oneCols σ else 0) + neOneCols σ +
        if neOneAtSource then neOneBoxes σ else 0 := by
    simp only [oneCols, neOneCols, neOneBoxes, ite_sum_zero, ← sum_add_distrib]
    refine sum_congr rfl fun h _ ↦ ?_
    by_cases h_one : h = 1 <;> by_cases hσ : σ ∈ marked <;>
      simp [c, CongruenceChoice.sourceCount, h_one, hσ, add_mul]
  have partner_sum : ∑ h ∈ range N, c.partnerCount h * κ σ' h =
      (if oneAtSource then 0 else neOneCols σ' + oneCols σ') +
        if neOneAtSource then 0 else neOneBoxes σ' := by
    simp only [oneCols, neOneCols, neOneBoxes, ite_zero_sum, ← sum_add_distrib]
    refine sum_congr rfl fun h _ ↦ ?_
    by_cases h_one : h = 1 <;> simp [c, CongruenceChoice.partnerCount, h_one, ite_and, add_mul]
  refine ⟨c, ?_, fun (h h' : ℕ) not_exempt ↦ ?_⟩
  · have h_cost : c.cost p e N (κ σ) (κ σ') =
        (∑ h ∈ range N, c.sourceCount h * κ σ h : ℕ) / p ^ e +
          (∑ h ∈ range N, c.partnerCount h * κ σ' h : ℕ) := by
      simp [CongruenceChoice.cost, sum_add_distrib, Finset.sum_div]
    rw [h_cost, source_sum, partner_sum, h_deduction, min_def, min_def]
    push_cast
    -- In each case of the two minima, both sides are the same sum.
    split_ifs <;> ring
  · -- A height `h = 1` is covered by the first minimum, since the places concerned are not marked;
    -- otherwise `h' = 1` is covered by the pairing at `σ`, and `h' ≠ 1` by the second minimum.
    simp only [c, CongruenceChoice.Covers, decide_eq_true_eq]
    grind [IsExemptPair]

/-- The moduli of the congruences on the rows of height `h` at the place `τ`, when `c e σ` is the
choice of congruences for the place `σ` and its partner `pr e σ` at the exponent `e ∈ S`. They are
indexed by `e`, `σ`, the side of the pairing from `σ` to `pr e σ` and the form (`none` for the
pairing, `some k` for an entry). If `τ` is the place of that side and `c e σ` imposes the
congruence, the modulus is `root e` at `σ` and `root 0` at `pr e σ`; otherwise it is `1`. -/
def New.congruenceModulus {O Φ : Type*} [One O] [DecidableEq Φ] (pr : ℕ → Φ → Φ) (S : Finset ℕ)
    (root : ℕ → O) (c : ℕ → Φ → CongruenceChoice) (τ : Φ) (h : ℕ) :
    S × Φ × PairingSide × Option (Fin h) → O :=
  fun (e, σ, side, form) ↦
    if side.place σ (pr e σ) = τ ∧ (c e σ).imposes h side form then root (side.rootExponent e)
    else 1

/-- Let `c e σ` be a choice of congruences for each exponent `e ∈ S`, place `σ` and partner
`pr e σ`, let `κ τ h` be the number of columns of height `h` at the place `τ`, and let `root e` be a
`p ^ e`-th root of `π`. The modulus `congruenceModulus` of the congruence indexed by
`(e, σ, side, form)`, on the rows of height `h` at `τ`, is `root e` at the side `σ` and `root 0` at
the side `pr e σ`, if that side is the place `τ` and the congruence is imposed; otherwise it is `1`.
The product of all moduli, over all `τ` and `h < N` and once for each of the `κ τ h` columns, has
norm `‖π‖` raised to the sum over `e` and `σ` of the `cost` of `c e σ`: the number of congruences
imposed on all columns of height less than `N` at `σ`, divided by `p ^ e`, plus the number of those
at `pr e σ`. -/
lemma New.norm_rpow_sum_cost_eq_prod_congruenceModulus {p : ℕ} [Fact p.Prime] {Φ : Type*}
    [Fintype Φ]
    [DecidableEq Φ] (pr : ℕ → Φ → Φ) (S : Finset ℕ) (N : ℕ) (κ : Φ → ℕ → ℕ) {π : valRingCp p}
    {root : ℕ → valRingCp p} (h_root : ∀ e : ℕ, root e ^ p ^ e = π)
    (c : ℕ → Φ → CongruenceChoice) :
    ‖π‖ ^ ∑ e ∈ S, ∑ σ : Φ, (c e σ).cost p e N (κ σ) (κ (pr e σ)) =
      ∏ τ : Φ, ∏ h : Fin N,
        ‖∏ i : S × Φ × PairingSide × Option (Fin h), congruenceModulus pr S root c τ h i‖ ^
          κ τ h := by
  have norm_root (e : ℕ) : ‖root e‖ = ‖π‖ ^ (p ^ e : ℝ)⁻¹ := by
    rw [← h_root e, norm_pow, ← Nat.cast_pow,
      Real.pow_rpow_inv_natCast (norm_nonneg _) (pow_ne_zero e (Fact.out : p.Prime).ne_zero)]
  -- The number of congruences on a row of height `h` on one side of the pairing from `σ`.
  let count (e : ℕ) (σ : Φ) (side : PairingSide) (h : ℕ) : ℕ :=
    ∑ form : Option (Fin h), if (c e σ).imposes h side form then 1 else 0
  -- The exponent of `‖π‖` in the product of their moduli, if `τ` is the place of that side.
  let weight (τ : Φ) (h e : ℕ) (σ : Φ) (side : PairingSide) : ℝ :=
    if side.place σ (pr e σ) = τ then count e σ side h / p ^ side.rootExponent e else 0
  have norm_side (τ : Φ) (h : ℕ) (e : S) (σ : Φ) (side : PairingSide) :
      ∏ form : Option (Fin h), ‖congruenceModulus pr S root c τ h (e, σ, side, form)‖ =
        ‖π‖ ^ weight τ h e σ side := by
    by_cases hτ : side.place σ (pr e σ) = τ
    · calc _ = ‖root (side.rootExponent e)‖ ^ count e σ side h := by
            simp only [congruenceModulus, hτ, true_and, ← pow_boole, norm_pow, prod_pow_eq_pow_sum,
              count]
        _ = ‖π‖ ^ weight τ h e σ side := by
            simp only [norm_root, ← Real.rpow_mul_natCast (norm_nonneg π), weight, hτ, ite_true,
              div_eq_inv_mul]
    · simp [congruenceModulus, weight, hτ]
  have weight_sum (τ : Φ) (h e : ℕ) (σ : Φ) : ∑ side : PairingSide, weight τ h e σ side =
      (if σ = τ then ((c e σ).sourceCount h / p ^ e : ℝ) else 0) +
        if pr e σ = τ then ((c e σ).partnerCount h / p ^ 0 : ℝ) else 0 := by
    rw [← CongruenceChoice.sum_imposes_source, ← CongruenceChoice.sum_imposes_partner]
    exact PairingSide.sum_univ (weight τ h e σ)
  -- The exponent of `‖π‖` in the product of all moduli at `τ` and height `h`.
  let exponent (τ : Φ) (h : ℕ) : ℝ := ∑ e : S, ∑ σ : Φ, ∑ side : PairingSide, weight τ h e σ side
  have norm_moduli (τ : Φ) (h : ℕ) :
      ‖∏ i, congruenceModulus pr S root c τ h i‖ = ‖π‖ ^ exponent τ h := by
    simp only [norm_prod, Fintype.prod_prod_type, norm_side]
    simp (disch := exact fun _ _ ↦ by positivity) only [exponent, weight,
      Real.rpow_sum_of_nonneg (norm_nonneg π)]
  have total_cost : ∑ e ∈ S, ∑ σ : Φ, (c e σ).cost p e N (κ σ) (κ (pr e σ)) =
      ∑ τ : Φ, ∑ h : Fin N, exponent τ h * κ τ h := by
    rw [← Fintype.sum_prod_type']
    simp only [exponent, weight_sum, ← S.sum_coe_sort, sum_mul,
      sum_comm (s := (univ : Finset (Φ × Fin N)))]
    congr! with e _ σ
    simp [CongruenceChoice.cost, Fintype.sum_prod_type, sum_range, sum_add_distrib, add_mul,
      div_mul_eq_mul_div]
  simp (disch := exact fun _ _ ↦ by positivity) only [total_cost, norm_moduli,
    ← Real.rpow_mul_natCast (norm_nonneg π), Real.rpow_sum_of_nonneg (norm_nonneg π)]

/-- Coordinate `a` of the new direction `k` for the place `τ` and the height `h`: the combination
`∑ k' : Fin h, g τ h k k' * y τ a k'` of the given directions `y τ · k'`. -/
def New.newDirection {Φ n R : Type} [CommRing R] (g : Φ → ∀ h : ℕ, Matrix (Fin h) (Fin h) R)
    (y : Φ → n → ℕ → R) (τ : Φ) (h : ℕ) (k : Fin h) (a : n) : R :=
  g τ h k ⬝ᵥ fun k' : Fin h ↦ y τ a k'

/-- **Changing the directions.** Let `π` divide `p` in the integers `valRingCp p` of `ℂ_p`, and let
`y τ a k'` be coordinate `a` of direction `k'` at the place `τ`. There are square matrices `g τ h`,
one for each place and height, such that the new directions `newDirection g y τ h k a = ∑ k' : Fin
h, g τ h k k' * y τ a k'` have two properties. First, for `e ∈ S`, the pairing
`∑ a, β a ^ p ^ e * β' a` of a new direction `β` of height `h` at `τ` with a new direction `β'` of
height `h'` at the partner `pr e τ` is divisible by `π`, unless the pair of heights is exempt.
Second, the determinants of the `g τ h`, one for each of the `κ τ h` columns of height `h < N`, have
total valuation at most `v(π)` times the sum of `deductionTerm` over `e ∈ S` and places `τ`. -/
lemma New.exists_newDirection_dvd {p : ℕ} [Fact p.Prime] {Φ n : Type} [Fintype Φ] [DecidableEq Φ]
    [Fintype n] {π : valRingCp p} (hπ : π ∣ p) (pr : ℕ → Φ → Φ) (S : Finset ℕ) (N : ℕ)
    (κ : Φ → ℕ → ℕ) (marked : Finset Φ) (y : Φ → n → ℕ → valRingCp p) :
    ∃ g : Φ → ∀ h : ℕ, Matrix (Fin h) (Fin h) (valRingCp p),
      (∀ e ∈ S, ∀ (τ : Φ) (h : ℕ) (k : Fin h) (h' : ℕ) (k' : Fin h'),
        ¬IsExemptPair marked τ (pr e τ) h h' →
          π ∣ ∑ a : n, newDirection g y τ h k a ^ p ^ e * newDirection g y (pr e τ) h' k' a) ∧
      ‖(π : ℂ_[p])‖ ^ ∑ e ∈ S, ∑ τ : Φ, deductionTerm p κ N marked τ (pr e τ) e ≤
        ∏ τ : Φ, ∏ h : Fin N, ‖((g τ h).det : ℂ_[p])‖ ^ κ τ h := by
  -- A pairing from `σ` to `pr e σ` is made divisible by congruences on the rows of `g`, either at
  -- `σ` modulo a `p ^ e`-th root of `π` or at `pr e σ` modulo `π`. The forms depend on `y` only,
  -- so all congruences on one matrix are collected and imposed together.
  have exists_root (e : ℕ) (x : valRingCp p) : ∃ r : valRingCp p, r ^ p ^ e = x :=
    (Variety.IsAbsIntegrallyClosed.of_isIntegrallyClosedIn ℂ_[p]).exists_pow_eq (p ^ e) x
  choose root h_root using exists_root
  have exists_choice (e : ℕ) (σ : Φ) : ∃ c : CongruenceChoice,
      c.cost p e N (κ σ) (κ (pr e σ)) = deductionTerm p κ N marked σ (pr e σ) e ∧
      ∀ h h' : ℕ, ¬IsExemptPair marked σ (pr e σ) h h' → c.Covers h h' :=
    exists_congruenceChoice_cost_eq_and_covers p κ N marked σ (pr e σ) e
  choose c cost_eq cover using exists_choice
  let α (τ : Φ) (h : ℕ) : S × Φ × PairingSide × Option (Fin h) → valRingCp p :=
    congruenceModulus pr S (fun e : ℕ ↦ root e π) c τ h
  -- The forms on these rows: the pairing with direction `0` at the other place, or a single entry.
  let A (τ : Φ) (h : ℕ) : S × Φ × PairingSide × Option (Fin h) → Fin h → valRingCp p
    | (e, σ, .source, none) => fun k ↦ ∑ a : n, root e (y (pr e σ) a 0) * y τ a k
    | (e, σ, .partner, none) => fun k ↦ ∑ a : n, y σ a 0 ^ p ^ (e : ℕ) * y τ a k
    | (_, _, _, some l) => Pi.single l 1
  have exists_matrix (τ : Φ) (h : ℕ) : ∃ g : Matrix (Fin h) (Fin h) (valRingCp p),
      g.det ∣ ∏ i, α τ h i ∧ ∀ i ∈ univ, ∀ k : Fin h, α τ h i ∣ (g *ᵥ A τ h i) k :=
    exists_det_dvd_prod_and_dvd_mulVec univ (A τ h) (α τ h)
  choose g det_dvd row_dvd using exists_matrix
  refine ⟨g, fun e he τ h k h' k' not_exempt ↦ ?_, ?_⟩
  · let β : n → valRingCp p := newDirection g y τ h k
    let β' : n → valRingCp p := newDirection g y (pr e τ) h' k'
    change π ∣ ∑ a : n, β a ^ p ^ e * β' a
    have source_dvd (form : Option (Fin h)) (h_imposed : (c e τ).imposes h .source form) :
        root e π ∣ g τ h k ⬝ᵥ A τ h (⟨e, he⟩, τ, .source, form) := by
      simpa [α, congruenceModulus, PairingSide.place, PairingSide.rootExponent, h_imposed,
        mulVec] using row_dvd τ h (⟨e, he⟩, τ, .source, form) (mem_univ _) k
    have partner_dvd (form : Option (Fin h')) (h_imposed : (c e τ).imposes h' .partner form) :
        π ∣ g (pr e τ) h' k' ⬝ᵥ A (pr e τ) h' (⟨e, he⟩, τ, .partner, form) := by
      have h_root_zero : root 0 π = π := by simpa using h_root 0 π
      simpa [α, congruenceModulus, PairingSide.place, PairingSide.rootExponent, h_imposed,
        h_root_zero, mulVec] using row_dvd (pr e τ) h' (⟨e, he⟩, τ, .partner, form) (mem_univ _) k'
    obtain ⟨h_imposed, rfl⟩ | h_imposed | ⟨h_imposed, rfl⟩ | h_imposed :=
      cover e τ h h' not_exempt
    · -- `β` is a multiple of the first direction at `τ`, and `π` divides its pairing with `β'`.
      have h_pair : π ∣ ∑ a, y τ a 0 ^ p ^ e * β' a := by
        simpa only [A, β', newDirection, dotProduct_sum_mul] using partner_dvd none h_imposed
      have h_factor : ∑ a, β a ^ p ^ e * β' a =
          g τ 1 k 0 ^ p ^ e * ∑ a, y τ a 0 ^ p ^ e * β' a := by
        simp [β, newDirection, dotProduct, mul_pow, mul_sum, mul_assoc]
      simpa only [h_factor] using h_pair.mul_left _
    · -- All entries of the row at the partner are divisible by `π`, hence so is `β'`.
      have h_entry (j : Fin h') : π ∣ g (pr e τ) h' k' j := by
        simpa [A] using partner_dvd (some j) h_imposed
      have h_direction (a : n) : π ∣ β' a := by
        simpa only [β', newDirection, dotProduct] using dvd_sum fun j _ ↦ (h_entry j).mul_right _
      exact dvd_sum fun a _ ↦ (h_direction a).mul_left _
    · -- `β'` is a multiple of the first direction at the partner, and its pairing with `β` is
      -- divisible by `π` through one congruence modulo the root of `π`.
      have h_form : root e π ∣ ∑ a, root e (y (pr e τ) a 0) * β a := by
        simpa only [A, β, newDirection, dotProduct_sum_mul] using source_dvd none h_imposed
      have h_pair : π ∣ ∑ a, β a ^ p ^ e * y (pr e τ) a 0 :=
        dvd_sum_pow_mul_of_root_dvd hπ (h_root e) h_form
      have h_factor : ∑ a, β a ^ p ^ e * β' a =
          g (pr e τ) 1 k' 0 * ∑ a, β a ^ p ^ e * y (pr e τ) a 0 := by
        simp [β', newDirection, dotProduct, mul_sum, mul_left_comm]
      simpa only [h_factor] using h_pair.mul_left _
    · -- All entries of the row at `τ` are divisible by the root of `π`, hence so is `β`.
      have h_entry (j : Fin h) : root e π ∣ g τ h k j := by
        simpa [A] using source_dvd (some j) h_imposed
      have h_direction (a : n) : root e π ∣ β a := by
        simpa only [β, newDirection, dotProduct] using dvd_sum fun j _ ↦ (h_entry j).mul_right _
      have h_pow (a : n) : π ∣ β a ^ p ^ e := by
        simpa only [h_root] using pow_dvd_pow_of_dvd (h_direction a) (p ^ e)
      exact dvd_sum fun a _ ↦ (h_pow a).mul_right _
  · -- The cost: `det (g τ h)` divides the product of the moduli, whose norm is known.
    calc ‖π‖ ^ ∑ e ∈ S, ∑ τ : Φ, deductionTerm p κ N marked τ (pr e τ) e
        = ∏ τ : Φ, ∏ h : Fin N, ‖∏ i, α τ h i‖ ^ κ τ h := by
          simp only [← cost_eq]
          exact norm_rpow_sum_cost_eq_prod_congruenceModulus pr S N κ (fun e : ℕ ↦ h_root e π) c
      _ ≤ ∏ τ : Φ, ∏ h : Fin N, ‖((g τ h).det : ℂ_[p])‖ ^ κ τ h := by
        gcongr with τ _ h
        exact dvd_iff_norm_le.1 (det_dvd τ h)

end NullFrames
