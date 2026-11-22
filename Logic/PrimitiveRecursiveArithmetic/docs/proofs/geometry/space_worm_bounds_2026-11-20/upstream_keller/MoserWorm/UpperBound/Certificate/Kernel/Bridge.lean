/- Exact certificate arithmetic and its kernel-checked proof interface. -/
import MoserWorm.UpperBound.Certificate.Kernel.Arithmetic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace MoserWorm.UpperBound.Certificate.Kernel

open MoserWorm.UpperBound.Certificate

/-! ### 1. Value lemmas for `KQ` -/

theorem den_cast_pos (x : KQ) : (0 : ℚ) < ((x.2 + 1 : ℕ) : ℚ) := by
  exact_mod_cast Nat.succ_pos x.2

theorem den_cast_ne (x : KQ) : ((x.2 + 1 : ℕ) : ℚ) ≠ 0 :=
  ne_of_gt (den_cast_pos x)

theorem dmul_cast (a b : ℕ) :
    ((dmul a b + 1 : ℕ) : ℚ) = ((a + 1 : ℕ) : ℚ) * ((b + 1 : ℕ) : ℚ) := by
  unfold dmul; push_cast; ring

theorem toQ_kAdd (x y : KQ) : toQ (kAdd x y) = toQ x + toQ y := by
  unfold toQ kAdd
  by_cases h : x.2 = y.2
  · rw [if_pos (by simpa using h), h, ← add_div]
    norm_cast
  · rw [if_neg (by simpa using h), dmul_cast]
    have hx := den_cast_ne x
    have hy := den_cast_ne y
    field_simp
    push_cast
    ring

theorem toQ_kSub (x y : KQ) : toQ (kSub x y) = toQ x - toQ y := by
  unfold toQ kSub
  by_cases h : x.2 = y.2
  · rw [if_pos (by simpa using h), h, ← sub_div]
    norm_cast
  · rw [if_neg (by simpa using h), dmul_cast]
    have hx := den_cast_ne x
    have hy := den_cast_ne y
    field_simp
    push_cast
    ring

theorem toQ_kMul (x y : KQ) : toQ (kMul x y) = toQ x * toQ y := by
  unfold toQ kMul
  rw [dmul_cast]
  have hx := den_cast_ne x
  have hy := den_cast_ne y
  field_simp
  push_cast
  ring

theorem kLe_eq (x y : KQ) : kLe x y = decide (toQ x ≤ toQ y) := by
  unfold kLe
  by_cases h : x.2 = y.2
  · rw [if_pos (by simpa using h), Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    rw [toQ, toQ, h, div_le_div_iff_of_pos_right (den_cast_pos y)]
    constructor <;> intro hh <;> exact_mod_cast hh
  · rw [if_neg (by simpa using h), Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    rw [toQ, toQ, div_le_div_iff₀ (den_cast_pos x) (den_cast_pos y)]
    constructor <;> intro hh <;> exact_mod_cast hh

theorem kLt_eq (x y : KQ) : kLt x y = decide (toQ x < toQ y) := by
  unfold kLt
  by_cases h : x.2 = y.2
  · rw [if_pos (by simpa using h), Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    rw [toQ, toQ, h, div_lt_div_iff_of_pos_right (den_cast_pos y)]
    constructor <;> intro hh <;> exact_mod_cast hh
  · rw [if_neg (by simpa using h), Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    rw [toQ, toQ, div_lt_div_iff₀ (den_cast_pos x) (den_cast_pos y)]
    constructor <;> intro hh <;> exact_mod_cast hh

theorem toQ_eq_zero_iff (x : KQ) : toQ x = 0 ↔ x.1 = 0 := by
  unfold toQ
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact_mod_cast h
    · exact absurd h (den_cast_ne x)
  · intro h
    left
    exact_mod_cast h

theorem kEqZero_eq (x : KQ) : kEqZero x = decide (toQ x = 0) := by
  rw [Bool.eq_iff_iff]
  simp only [kEqZero, beq_iff_eq, decide_eq_true_eq, toQ_eq_zero_iff]

theorem kNegative_eq (x : KQ) : kNegative x = decide (toQ x < 0) := by
  rw [Bool.eq_iff_iff]
  simp only [kNegative, decide_eq_true_eq]
  rw [toQ, div_lt_iff₀ (den_cast_pos x), zero_mul]
  constructor <;> intro h <;> exact_mod_cast h

theorem kNonneg_eq (x : KQ) : kNonneg x = decide (0 ≤ toQ x) := by
  rw [Bool.eq_iff_iff]
  simp only [kNonneg, decide_eq_true_eq]
  rw [toQ, le_div_iff₀ (den_cast_pos x), zero_mul]
  constructor <;> intro h <;> exact_mod_cast h

theorem toQ_kRed (x : KQ) : toQ (kRed x) = toQ x := by
  unfold toQ kRed
  have hg1 : (Nat.gcd x.1.natAbs (x.2 + 1) : ℤ) ∣ x.1 :=
    dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _))
      (Int.natAbs_dvd.mpr dvd_rfl)
  have hg2 : Nat.gcd x.1.natAbs (x.2 + 1) ∣ x.2 + 1 := Nat.gcd_dvd_right _ _
  have hgpos : 0 < Nat.gcd x.1.natAbs (x.2 + 1) :=
    Nat.gcd_pos_of_pos_right _ (Nat.succ_pos _)
  set g := Nat.gcd x.1.natAbs (x.2 + 1) with hgdef
  have hden : (x.2 + 1) / g - 1 + 1 = (x.2 + 1) / g := by
    have : 0 < (x.2 + 1) / g := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos _) hg2) hgpos
    omega
  rw [hden]
  have hq : ((x.2 + 1) / g : ℕ) * g = x.2 + 1 := Nat.div_mul_cancel hg2
  have hqz : (((x.2 + 1) / g : ℕ) : ℚ) ≠ 0 := by
    have : 0 < (x.2 + 1) / g := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos _) hg2) hgpos
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  have hgz : ((g : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hgpos
  have hnum : ((x.1 / (g : ℤ) : ℤ) : ℚ) * ((g : ℕ) : ℚ) = (x.1 : ℚ) := by
    rw [show ((g : ℕ) : ℚ) = ((g : ℤ) : ℚ) by push_cast; ring,
      ← Int.cast_mul, Int.ediv_mul_cancel hg1]
  rw [div_eq_div_iff hqz (den_cast_ne x)]
  calc ((x.1 / (g : ℤ) : ℤ) : ℚ) * ((x.2 + 1 : ℕ) : ℚ)
      = ((x.1 / (g : ℤ) : ℤ) : ℚ) * (((x.2 + 1) / g : ℕ) : ℚ) * ((g : ℕ) : ℚ) := by
        rw [mul_assoc, ← Nat.cast_mul, hq]
    _ = (x.1 : ℚ) * (((x.2 + 1) / g : ℕ) : ℚ) := by
        rw [mul_right_comm, hnum]

/-! Constants. -/

theorem toQ_kQ0 : toQ kQ0 = 0 := by norm_num [toQ, kQ0]
theorem toQ_kQ1 : toQ kQ1 = 1 := by norm_num [toQ, kQ1]
theorem toQ2_kQ2z : toQ2 kQ2z = ((0 : ℚ), (0 : ℚ)) := by
  simp [toQ2, kQ2z, toQ_kQ0]

/-! Vector versions. -/

theorem toQ2_kAdd2 (u v : KQ2) : toQ2 (kAdd2 u v) = qadd (toQ2 u) (toQ2 v) := by
  simp [toQ2, kAdd2, qadd, toQ_kAdd]

theorem toQ2_kSub2 (u v : KQ2) : toQ2 (kSub2 u v) = qsub (toQ2 u) (toQ2 v) := by
  simp [toQ2, kSub2, qsub, toQ_kSub]

theorem toQ2_kSmul (c : KQ) (u : KQ2) :
    toQ2 (kSmul c u) = qsmul (toQ c) (toQ2 u) := by
  simp [toQ2, kSmul, qsmul, toQ_kMul]

theorem toQ_kNorm2 (u : KQ2) : toQ (kNorm2 u) = qnorm2 (toQ2 u) := by
  simp [kNorm2, qnorm2, toQ2, toQ_kAdd, toQ_kMul]

theorem toQ2_kRed2 (u : KQ2) : toQ2 (kRed2 u) = toQ2 u := by
  simp [kRed2, toQ2, toQ_kRed]

/-! ### 2. `KVec` access lemmas -/

namespace KVec

variable {α : Type} {d : α} {f : α → α}

theorem getD_modify_ne (t : KVec α) (i j : ℕ) (h : i ≠ j) :
    (t.modify f i).getD d j = t.getD d j := by
  induction t generalizing i j with
  | nil => rfl
  | node v o e iho ihe =>
    match i, j with
    | 0, 0 => omega
    | 0, m + 1 => rfl
    | n + 1, 0 =>
      rw [modify]
      split <;> rfl
    | n + 1, m + 1 =>
      rw [modify]
      by_cases hn : n % 2 == 0
      · rw [if_pos hn, getD, getD]
        by_cases hm : m % 2 == 0
        · rw [if_pos hm, if_pos hm]
          simp only [beq_iff_eq] at hn hm
          exact iho _ _ (by omega)
        · rw [if_neg hm, if_neg hm]
      · rw [if_neg hn, getD, getD]
        by_cases hm : m % 2 == 0
        · rw [if_pos hm, if_pos hm]
        · rw [if_neg hm, if_neg hm]
          simp only [beq_iff_eq] at hn hm
          exact ihe _ _ (by omega)

theorem getD_modify_self (t : KVec α) (i : ℕ) :
    (t.modify f i).getD d i = if t.has i then f (t.getD d i) else d := by
  induction t generalizing i with
  | nil => simp [modify, getD, has]
  | node v o e iho ihe =>
    match i with
    | 0 => simp [modify, getD, has]
    | n + 1 =>
      rw [modify]
      by_cases hn : n % 2 == 0
      · rw [if_pos hn, getD, if_pos hn, has, if_pos hn, getD, if_pos hn]
        exact iho _
      · rw [if_neg hn, getD, if_neg hn, has, if_neg hn, getD, if_neg hn]
        exact ihe _

theorem has_modify (t : KVec α) (i j : ℕ) :
    (t.modify f i).has j = t.has j := by
  induction t generalizing i j with
  | nil => rfl
  | node v o e iho ihe =>
    match i, j with
    | 0, 0 => rfl
    | 0, m + 1 => rfl
    | n + 1, 0 =>
      rw [modify]; split <;> rfl
    | n + 1, m + 1 =>
      rw [modify]
      by_cases hn : n % 2 == 0
      · rw [if_pos hn, has, has]
        split
        · exact iho _ _
        · rfl
      · rw [if_neg hn, has, has]
        split
        · rfl
        · exact ihe _ _

theorem getD_full (h j : ℕ) : (full d h).getD d j = d := by
  induction h generalizing j with
  | zero => rfl
  | succ h ih =>
    match j with
    | 0 => rfl
    | n + 1 =>
      rw [full, getD]
      split <;> exact ih _

theorem has_full (h j : ℕ) (hj : j < 2 ^ h - 1) : (full d h).has j = true := by
  induction h generalizing j with
  | zero => simp at hj
  | succ h ih =>
    match j with
    | 0 => rfl
    | n + 1 =>
      rw [full, has]
      have h2 : 2 ^ (h + 1) = 2 * 2 ^ h := by rw [pow_succ]; ring
      split
      · exact ih _ (by omega)
      · exact ih _ (by omega)

theorem getD_setFrom_lt (l : List α) (t : KVec α) (i j : ℕ) (h : j < i) :
    (setFrom t i l).getD d j = t.getD d j := by
  induction l generalizing t i with
  | nil => rfl
  | cons x xs ih =>
    rw [setFrom, ih _ _ (by omega), set, getD_modify_ne _ _ _ (by omega)]

theorem getD_setFrom_ge (l : List α) (t : KVec α) (i j : ℕ)
    (h : i + l.length ≤ j) : (setFrom t i l).getD d j = t.getD d j := by
  induction l generalizing t i with
  | nil => rfl
  | cons x xs ih =>
    rw [setFrom, ih _ _ (by simp only [List.length_cons] at h; omega), set,
      getD_modify_ne _ _ _ (by simp only [List.length_cons] at h; omega)]

theorem has_setFrom (l : List α) (t : KVec α) (i j : ℕ) :
    (setFrom t i l).has j = t.has j := by
  induction l generalizing t i with
  | nil => rfl
  | cons x xs ih => rw [setFrom, ih, set, has_modify]

theorem getD_setFrom_in (l : List α) (t : KVec α) (i n : ℕ)
    (hn : n < l.length) (ht : t.has (i + n) = true) :
    (setFrom t i l).getD d (i + n) = l.getD n d := by
  induction l generalizing t i n with
  | nil => simp at hn
  | cons x xs ih =>
    match n with
    | 0 =>
      rw [setFrom, getD_setFrom_lt _ _ _ _ (by omega), set,
        Nat.add_zero, getD_modify_self, if_pos (by rw [← Nat.add_zero i]; exact ht)]
      rfl
    | n + 1 =>
      rw [setFrom, show i + (n + 1) = (i + 1) + n by omega,
        ih _ _ _ (by simpa using hn)
          (by rw [set, has_modify, show i + 1 + n = i + (n + 1) by omega]; exact ht)]
      rfl

end KVec

theorem bitsAux_lt (fuel n : ℕ) (h : n ≤ fuel) : n < 2 ^ bitsAux fuel n := by
  induction fuel generalizing n with
  | zero =>
    have hz : n = 0 := by omega
    subst hz
    simp [bitsAux]
  | succ fuel ih =>
    rw [bitsAux]
    by_cases hz : n == 0
    · simp only [hz, if_pos]
      simp only [beq_iff_eq] at hz
      simp [hz]
    · rw [if_neg hz]
      simp only [beq_iff_eq] at hz
      have := ih (n / 2) (by omega)
      have h2 : 2 ^ (bitsAux fuel (n / 2) + 1) = 2 * 2 ^ bitsAux fuel (n / 2) := by
        rw [pow_succ]; ring
      omega

theorem lt_two_pow_bits (n : ℕ) : n < 2 ^ bits n := bitsAux_lt n n le_rfl

/-- The main trie lemma: `ofList` behaves exactly like `List.getD`. -/
theorem KVec.getD_ofList (d : α) (l : List α) (j : ℕ) :
    (KVec.ofList d l).getD d j = l.getD j d := by
  unfold KVec.ofList
  by_cases hj : j < l.length
  · have hcap : j < 2 ^ (bits l.length + 1) - 1 := by
      have h1 : l.length < 2 ^ bits l.length := lt_two_pow_bits _
      have h2 : 2 ^ (bits l.length + 1) = 2 * 2 ^ bits l.length := by
        rw [pow_succ]; ring
      omega
    have := KVec.getD_setFrom_in (d := d) l (KVec.full d (bits l.length + 1)) 0 j hj
      (by rw [Nat.zero_add]; exact KVec.has_full _ _ hcap)
    rw [Nat.zero_add] at this
    exact this
  · rw [KVec.getD_setFrom_ge _ _ _ _ (by omega), KVec.getD_full,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- Same, with an arbitrary read default when it matches the fill. -/
theorem KVec.has_ofList (d : α) (l : List α) (j : ℕ) (hj : j < l.length) :
    (KVec.ofList d l).has j = true := by
  unfold KVec.ofList
  rw [KVec.has_setFrom]
  refine KVec.has_full _ _ ?_
  have h1 : l.length < 2 ^ bits l.length := lt_two_pow_bits _
  have h2 : 2 ^ (bits l.length + 1) = 2 * 2 ^ bits l.length := by
    rw [pow_succ]; ring
  omega

/-! ### 3. Loop desugaring: the original checker as structural folds

The `Id.run do` loops of `checkLeaf` and `familyMaxNorm2` are
rewritten to explicit `List.foldl`s over `List.range'` (`q*Spec` below), by
`Std.Legacy.Range.forIn_eq_forIn_range'`, `List.forIn_pure_yield_eq_foldl`
and the two `forIn` helpers here.  The `q*Spec` forms are then related to
the `k*` functions value-by-value in section 4. -/

theorem range_size (a b : ℕ) : [a:b].size = b - a := by
  simp

/-- Push `pure ∘ ForInStep.yield` out of an `if` (prepares
`List.forIn_pure_yield_eq_foldl`). -/
theorem ite_pure_yield {σ : Type} {c : Prop} [Decidable c] (a b : σ) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep σ))
     else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

/-- Early-exit accumulation, as desugared from
`for kv in mu do match step … with | none => return false | some s => …`. -/
def foldE (step : σ → α → Option σ) : List α → σ → Option Bool × σ
  | [], s => (none, s)
  | x :: xs, s =>
    match step s x with
    | none => (some false, s)
    | some s' => foldE step xs s'

theorem forIn_foldE {σ α : Type} (step : σ → α → Option σ) (xs : List α)
    (s : σ) (f : α → Option Bool × σ → Id (ForInStep (Option Bool × σ)))
    (hf : ∀ x t, f x (none, t) =
      match step t x with
      | none => pure (ForInStep.done (some false, t))
      | some t' => pure (ForInStep.yield (none, t'))) :
    forIn (m := Id) xs ((none : Option Bool), s) f = pure (foldE step xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons, hf, foldE]
    cases h : step s x with
    | none => rfl
    | some s' => exact ih s'

/-- `kFoldN` is `List.foldl` over `List.range'`. -/
theorem kFoldN_eq_foldl (f : σ → ℕ → σ) (s : σ) (a n : ℕ) :
    kFoldN f s a n = (List.range' a n).foldl f s := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih => rw [kFoldN, List.range', List.foldl_cons, ih]

/-! The `Id.run do` bodies as plain folds (`q*Spec`), shapes matching the
desugared originals verbatim. -/

/-- Cumulative-sum array (the two build loops of `familyMaxNorm2`). -/
def qCum (C : Array Q2) (base cnt : ℕ) : Array Q2 :=
  (List.range' 0 cnt).foldl
    (fun b a => b.push (qadd (b.getD a (0, 0)) (Array.getD C (base + a) (0, 0))))
    ((Array.mkEmpty (cnt + 1)).push (0, 0))

/-- `familyMaxNorm2` as folds. -/
def qFamilySpec (k m : ℕ) (C : Array Q2) (pLo pHi qLo qHi : ℕ) : ℚ :=
  let A := qCum C (3 + k) m
  let B := qCum C 3 k
  let best := (List.range' qLo (m - qLo)).foldl
    (fun best a => (List.range' a (m - a)).foldl
      (fun b a1 =>
        if qnorm2 (qsub (A.getD (a1 + 1) (0, 0)) (A.getD a (0, 0))) > b then
          qnorm2 (qsub (A.getD (a1 + 1) (0, 0)) (A.getD a (0, 0)))
        else b) best) 0
  let best := (List.range' 0 (min qHi m + 1)).foldl
    (fun b j =>
      if qnorm2 (qadd (qsub (A.getD m (0, 0)) (A.getD j (0, 0)))
          (Array.getD C 0 (0, 0))) > b then
        qnorm2 (qadd (qsub (A.getD m (0, 0)) (A.getD j (0, 0)))
          (Array.getD C 0 (0, 0)))
      else b) best
  let best := (List.range' pLo (k + 1 - pLo)).foldl
    (fun b j =>
      if qnorm2 (qadd (Array.getD C 1 (0, 0)) (B.getD j (0, 0))) > b then
        qnorm2 (qadd (Array.getD C 1 (0, 0)) (B.getD j (0, 0)))
      else b) best
  (List.range' 0 (pHi + 1)).foldl
    (fun best a => (List.range' a (pHi + 1 - a)).foldl
      (fun b a1 =>
        if qnorm2 (qsub (B.getD a1 (0, 0)) (B.getD a (0, 0))) > b then
          qnorm2 (qsub (B.getD a1 (0, 0)) (B.getD a (0, 0)))
        else b) best) best

theorem familyMaxNorm2_eq_qspec (T : LabelTables) (C : Forces)
    (pLo pHi qLo qHi : ℕ) :
    familyMaxNorm2 T C pLo pHi qLo qHi =
      qFamilySpec T.kR T.kL C pLo pHi qLo qHi := by
  unfold familyMaxNorm2 qFamilySpec qCum
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', pure_bind,
    List.forIn_pure_yield_eq_foldl, range_size, Nat.sub_zero]
  rfl

/-- `checkLeaf` with the row loop as `foldE` and the tail explicit. -/
def qLeafSpec (ctx : Ctx) (assign : List (ℕ × Fin 2))
    (rect : ℕ × ℕ × ℕ × ℕ) (mu : List (RowKey × ℚ)) : Bool :=
  match foldE (fun s kv => applyRow ctx assign s.1 s.2 kv) mu
      (Array.replicate ctx.T.nLab ((0 : ℚ), (0 : ℚ)), (0 : ℚ)) with
  | (some r, _) => r
  | (none, C, LB) =>
    let s := Array.foldl qadd (0, 0) C
    if (s != ((0 : ℚ), (0 : ℚ))) = true then false
    else
      match rect with
      | (pLo, pHi, qLo, qHi) =>
        let maxNorm2 := familyMaxNorm2 ctx.T C pLo pHi qLo qHi
        decide (maxNorm2 ≤ 1) && decide (LB ≥ ctx.target)

theorem checkLeaf_eq_qspec (ctx : Ctx) (assign : List (ℕ × Fin 2))
    (rect : ℕ × ℕ × ℕ × ℕ) (mu : List (RowKey × ℚ)) :
    checkLeaf ctx assign rect mu = qLeafSpec ctx assign rect mu := by
  unfold checkLeaf qLeafSpec
  set_option linter.unusedSimpArgs false in
  simp only [letFun]
  rw [forIn_foldE (step := fun s kv => applyRow ctx assign s.1 s.2 kv)]
  · cases hE : foldE (fun s kv => applyRow ctx assign s.1 s.2 kv) mu
        (Array.replicate ctx.T.nLab ((0 : ℚ), (0 : ℚ)), (0 : ℚ)) with
    | mk r st =>
      cases r with
      | none => rfl
      | some b => rfl
  · intro x t
    cases happ : applyRow ctx assign t.1 t.2 x with
    | none => rfl
    | some s' => rfl

/-! ### 4. Value-level equivalences -/

/-- Fold two lists in lockstep, carrying a relation. -/
theorem foldl_rel {β γ ι : Type _} (R : β → γ → Prop) (l : List ι)
    (f : β → ι → β) (g : γ → ι → γ) {b : β} {c : γ} (hbc : R b c)
    (h : ∀ x y i, i ∈ l → R x y → R (f x i) (g y i)) :
    R (l.foldl f b) (l.foldl g c) := by
  induction l generalizing b c with
  | nil => exact hbc
  | cons i is ih =>
    exact ih (h _ _ _ List.mem_cons_self hbc)
      (fun x y j hj => h x y j (List.mem_cons_of_mem _ hj))

/-- `List.getD` through a `map`, with matching defaults. -/
theorem getD_map_default {α β : Type _} (f : α → β) (l : List α) (i : ℕ)
    (d : α) : (l.map f).getD i (f d) = f (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

/-- `Array.getD` on `List.toArray`. -/
theorem toArray_getD {α : Type _} (l : List α) (i : ℕ) (d : α) :
    l.toArray.getD i d = l.getD i d := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    List.getElem?_toArray]

/-- The force-accumulator relation: same size/coverage, pointwise decoded. -/
def CRel (n : ℕ) (A : Array Q2) (t : KVec KQ2) : Prop :=
  A.size = n ∧ (∀ j, j < n → t.has j = true) ∧
    ∀ j, j < n → toQ2 (t.getD kQ2z j) = A.getD j ((0 : ℚ), (0 : ℚ))

theorem CRel.modify {n : ℕ} {A : Array Q2} {t : KVec KQ2}
    (h : CRel n A t) (i : ℕ) {f : Q2 → Q2} {g : KQ2 → KQ2}
    (hfg : ∀ kc, toQ2 (g kc) = f (toQ2 kc)) :
    CRel n (A.modify i f) (t.modify g i) := by
  obtain ⟨hsz, hhas, hpt⟩ := h
  refine ⟨by rw [Array.size_modify, hsz], fun j hj => by
    rw [KVec.has_modify]; exact hhas j hj, fun j hj => ?_⟩
  by_cases hij : i = j
  · subst hij
    rw [KVec.getD_modify_self, if_pos (hhas i hj), hfg, hpt i hj,
      Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_modify, if_pos rfl]
    have hi : i < A.size := by omega
    rw [Array.getElem?_eq_getElem hi]
    rfl
  · rw [KVec.getD_modify_ne _ _ _ (fun hh => hij hh), hpt j hj,
      Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_modify, if_neg hij]

/-- Result relation for one row application. -/
def ARel (n : ℕ) : Option (Array Q2 × ℚ) → Option (KVec KQ2 × KQ) → Prop
  | none, none => True
  | some (A, LB), some (t, LBk) => CRel n A t ∧ toQ LBk = LB
  | _, _ => False

theorem applyRow_rel (ctx : Ctx) (nt : KVec KQ2) (et : KVec (Option KRow))
    (assign : List (ℕ × Fin 2)) (A : Array Q2) (LB : ℚ) (t : KVec KQ2)
    (LBk : KQ) (key : RowKey) (kv : KQ)
    (H1 : ∀ l, l < ctx.T.nLab → toQ2 (nt.getD kQ2z l) = ctx.T.normalOf l)
    (H2 : ∀ j, Option.map decodeRow (et.getD none j) = ctx.eRows.getD j none)
    (hC : CRel ctx.T.nLab A t) (hLB : toQ LBk = LB) :
    ARel ctx.T.nLab (applyRow ctx assign A LB (key, toQ kv))
      (kApplyRow ctx.T.nLab nt et assign t LBk (key, kv)) := by
  unfold applyRow kApplyRow
  dsimp only
  rw [kNegative_eq]
  by_cases hv : toQ kv < 0
  · simp only [decide_eq_true hv, if_pos hv]
    trivial
  · simp only [decide_eq_false hv, Bool.false_eq_true, if_false, if_neg hv]
    match key with
    | .s d p =>
      dsimp only
      by_cases hcond : (d == p || decide (d ≥ ctx.T.nLab) ||
          decide (p ≥ ctx.T.nLab)) = true
      · rw [if_pos hcond, if_pos hcond]
        trivial
      · rw [if_neg hcond, if_neg hcond]
        have hd : d < ctx.T.nLab := by
          simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          omega
        refine ⟨?_, hLB⟩
        have hnd : toQ2 (nt.getD kQ2z d) = ctx.T.normalOf d := H1 d hd
        refine CRel.modify (CRel.modify hC d ?_) p ?_
        · intro kc
          rw [toQ2_kRed2, toQ2_kAdd2, toQ2_kSmul, hnd]
        · intro kc
          rw [toQ2_kRed2, toQ2_kSub2, toQ2_kSmul, hnd]
    | .n =>
      dsimp only
      refine ⟨?_, hLB⟩
      refine CRel.modify (CRel.modify hC 1 ?_) 0 ?_
      · intro kc
        rw [toQ2_kRed2, toQ2_kAdd2]
        simp only [toQ2, toQ_kQ0, qadd]
      · intro kc
        rw [toQ2_kRed2, toQ2_kSub2]
        simp only [toQ2, toQ_kQ0, qsub]
    | .e m r =>
      dsimp only
      by_cases hmem : assign.contains (m, r)
      · rw [if_pos hmem, if_pos hmem]
        have h2 := H2 (2 * m + r.val)
        cases hket : et.getD none (2 * m + r.val) with
        | none =>
          rw [hket] at h2
          rw [← h2]
          trivial
        | some krow =>
          rw [hket] at h2
          rw [← h2]
          dsimp only [Option.map_some]
          refine ⟨?_, ?_⟩
          · rw [decodeRow]
            dsimp only
            rw [List.foldl_map]
            exact foldl_rel (CRel ctx.T.nLab) krow.coeffs _ _ hC
              (fun A' t' lv _ hR => CRel.modify hR lv.1
                (fun kc => by rw [toQ2_kRed2, toQ2_kAdd2, toQ2_kSmul]))
          · rw [toQ_kRed, toQ_kSub, toQ_kMul, hLB, decodeRow]
      · rw [if_neg hmem, if_neg hmem]
        trivial

/-! #### Cumulative sums and `familyMaxNorm2` -/

theorem qCum_succ (C : Array Q2) (base cnt : ℕ) :
    qCum C base (cnt + 1) = (qCum C base cnt).push
      (qadd ((qCum C base cnt).getD cnt (0, 0))
        (Array.getD C (base + cnt) (0, 0))) := by
  unfold qCum
  rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [Nat.one_mul, Nat.zero_add]
  rfl

theorem qCum_size (C : Array Q2) (base : ℕ) :
    ∀ cnt, (qCum C base cnt).size = cnt + 1
  | 0 => rfl
  | cnt + 1 => by rw [qCum_succ, Array.size_push, qCum_size C base cnt]

theorem kCum_length (Ct : KVec KQ2) (base : ℕ) :
    ∀ cnt, (kCum Ct base cnt).length = cnt + 1
  | 0 => rfl
  | cnt + 1 => by
    rw [kCum, List.length_append, kCum_length Ct base cnt]
    rfl

theorem getD_append_lt {α : Type _} {l : List α} {x d : α} {i : ℕ}
    (h : i < l.length) : (l ++ [x]).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h,
    ← List.getD_eq_getElem?_getD]

theorem getD_append_len {α : Type _} {l : List α} {x d : α} {i : ℕ}
    (h : i = l.length) : (l ++ [x]).getD i d = x := by
  subst h
  rw [List.getD_eq_getElem?_getD, List.getElem?_concat_length]
  rfl

theorem getD_append_gt {α : Type _} {l : List α} {x d : α} {i : ℕ}
    (h : l.length < i) : (l ++ [x]).getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
  rfl

theorem getD_push_lt {α : Type _} {A : Array α} {x d : α} {i : ℕ}
    (h : i < A.size) : (A.push x).getD i d = A.getD i d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, if_neg (by omega),
    ← Array.getD_eq_getD_getElem?]

theorem getD_push_len {α : Type _} {A : Array α} {x d : α} {i : ℕ}
    (h : i = A.size) : (A.push x).getD i d = x := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, if_pos h]
  rfl

theorem getD_push_gt {α : Type _} {A : Array α} {x d : α} {i : ℕ}
    (h : A.size < i) : (A.push x).getD i d = d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, if_neg (by omega),
    Array.getElem?_eq_none (by omega)]
  rfl

theorem kCum_rel (Ct : KVec KQ2) (A : Array Q2) (base : ℕ) (cnt : ℕ)
    (hC : ∀ i, i < cnt →
      toQ2 (Ct.getD kQ2z (base + i)) = A.getD (base + i) ((0 : ℚ), (0 : ℚ))) :
    ∀ j, toQ2 ((kCum Ct base cnt).getD j kQ2z) =
      (qCum A base cnt).getD j ((0 : ℚ), (0 : ℚ)) := by
  induction cnt with
  | zero =>
    intro j
    match j with
    | 0 => exact toQ2_kQ2z
    | j + 1 =>
      change toQ2 kQ2z = _
      rw [toQ2_kQ2z]
      rfl
  | succ cnt ih =>
    have hC' : ∀ i, i < cnt →
        toQ2 (Ct.getD kQ2z (base + i)) = A.getD (base + i) ((0 : ℚ), (0 : ℚ)) :=
      fun i hi => hC i (by omega)
    intro j
    rw [kCum, qCum_succ]
    rcases Nat.lt_trichotomy j (cnt + 1) with hj | hj | hj
    · rw [getD_append_lt (by rw [kCum_length]; omega),
        getD_push_lt (by rw [qCum_size]; omega)]
      exact ih hC' j
    · rw [getD_append_len (by rw [kCum_length]; omega),
        getD_push_len (by rw [qCum_size]; omega),
        toQ2_kRed2, toQ2_kAdd2, toQ2_kRed2, ih hC' cnt, hC cnt (by omega)]
    · rw [getD_append_gt (by rw [kCum_length]; omega),
        getD_push_gt (by rw [qCum_size]; omega)]
      exact toQ2_kQ2z

theorem toQ_kToDen (dp : ℕ) (x : KQ) : toQ (kToDen dp x) = toQ x := by
  unfold kToDen
  dsimp only
  set q := (dp + 1) / (x.2 + 1) with hq
  by_cases h : (x.2 + 1) * q = dp + 1
  · rw [if_pos (by simpa using h), toQ, toQ]
    rw [div_eq_div_iff (by exact_mod_cast Nat.succ_ne_zero dp) (den_cast_ne x)]
    conv_rhs => rw [← h]
    push_cast
    ring
  · rw [if_neg (by simpa using h)]

theorem toQ2_kToDen2 (dp : ℕ) (u : KQ2) : toQ2 (kToDen2 dp u) = toQ2 u := by
  simp [kToDen2, toQ2, toQ_kToDen]

/-- `kCommon` is value-transparent at every index. -/
theorem kCommon_getD (l : List KQ2) (j : ℕ) :
    toQ2 ((kCommon l).getD j kQ2z) = toQ2 (l.getD j kQ2z) := by
  unfold kCommon
  by_cases hj : j < l.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hj]
    dsimp only [Option.map_some, Option.getD_some]
    rw [toQ2_kToDen2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  · have hlen : l.length ≤ j := by omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simpa using hlen), List.getElem?_eq_none hlen]

theorem kUpd_eq {b : KQ} {qb : ℚ} {v : KQ2} {qv : Q2}
    (hb : toQ b = qb) (hv : toQ2 v = qv) :
    toQ (kUpd b v) = if qnorm2 qv > qb then qnorm2 qv else qb := by
  unfold kUpd
  rw [kLt_eq, toQ_kNorm2, hv, hb]
  by_cases h : qb < qnorm2 qv
  · rw [if_pos (by simpa using h), if_pos h, toQ_kNorm2, hv]
  · rw [if_neg (by simpa using h), if_neg h, hb]


theorem kFamily_eq (kR kL : ℕ) (A : Array Q2) (Ct : KVec KQ2)
    (hC : ∀ j, j < 3 + kR + kL →
      toQ2 (Ct.getD kQ2z j) = A.getD j ((0 : ℚ), (0 : ℚ)))
    (pLo pHi qLo qHi : ℕ) :
    toQ (kFamilyMaxNorm2 kR kL Ct pLo pHi qLo qHi)
      = qFamilySpec kR kL A pLo pHi qLo qHi := by
  have hA : ∀ j, toQ2 ((kCommon (kCum Ct (3 + kR) kL)).getD j kQ2z)
      = (qCum A (3 + kR) kL).getD j ((0 : ℚ), (0 : ℚ)) :=
    fun j => (kCommon_getD _ j).trans
      (kCum_rel Ct A (3 + kR) kL (fun i hi => hC (3 + kR + i) (by omega)) j)
  have hB : ∀ j, toQ2 ((kCommon (kCum Ct 3 kR)).getD j kQ2z)
      = (qCum A 3 kR).getD j ((0 : ℚ), (0 : ℚ)) :=
    fun j => (kCommon_getD _ j).trans
      (kCum_rel Ct A 3 kR (fun i hi => hC (3 + i) (by omega)) j)
  have hFm : toQ2 (kRed2 (Ct.getD kQ2z 0)) = A.getD 0 ((0 : ℚ), (0 : ℚ)) := by
    rw [toQ2_kRed2]; exact hC 0 (by omega)
  have hFp : toQ2 (kRed2 (Ct.getD kQ2z 1)) = A.getD 1 ((0 : ℚ), (0 : ℚ)) := by
    rw [toQ2_kRed2]; exact hC 1 (by omega)
  unfold kFamilyMaxNorm2 qFamilySpec
  dsimp only
  simp only [kFoldN_eq_foldl]
  refine foldl_rel (fun x y => toQ x = y) _ _ _ ?_ ?_
  · -- init of stage (iv) = result of stage (iii)
    refine foldl_rel (fun x y => toQ x = y) _ _ _ ?_ ?_
    · -- stage (ii)
      refine foldl_rel (fun x y => toQ x = y) _ _ _ ?_ ?_
      · -- stage (i)
        refine foldl_rel (fun x y => toQ x = y) _ _ _ toQ_kQ0 ?_
        intro x y a _ hxy
        refine foldl_rel (fun x y => toQ x = y) _ _ _ hxy ?_
        intro x' y' b _ h
        exact kUpd_eq h (by rw [toQ2_kSub2, hA, hA])
      · intro x y j _ h
        exact kUpd_eq h (by rw [toQ2_kAdd2, toQ2_kSub2, hA, hA, hFm])
    · intro x y j _ h
      refine kUpd_eq h ?_
      rw [toQ2_kAdd2, hFp, hB]
  · intro x y a _ h
    refine foldl_rel (fun x y => toQ x = y) _ _ _ h ?_
    intro x' y' b _ h'
    exact kUpd_eq h' (by rw [toQ2_kSub2, hB, hB])

theorem foldl_getD_aux {α β : Type _} (f : β → α → β) (d : α) :
    ∀ (l : List α) (L : List α) (a : ℕ) (init : β),
      (∀ k, k < l.length → L.getD (a + k) d = l.getD k d) →
      l.foldl f init =
        (List.range' a l.length).foldl (fun s i => f s (L.getD i d)) init := by
  intro l
  induction l with
  | nil => intros; rfl
  | cons x xs ih =>
    intro L a init hk
    rw [List.foldl_cons, List.length_cons, List.range'_succ, List.foldl_cons]
    have h0 : L.getD a d = x := by simpa using hk 0 (by simp)
    rw [h0]
    exact ih L (a + 1) _ (fun k hk' => by
      have := hk (k + 1) (by simpa using Nat.succ_lt_succ hk')
      rwa [show a + (k + 1) = a + 1 + k by omega] at this)

theorem kSumTo_rel (Ct : KVec KQ2) (A : Array Q2) (n : ℕ)
    (hsz : A.size = n)
    (hC : ∀ j, j < n → toQ2 (Ct.getD kQ2z j) = A.getD j ((0 : ℚ), (0 : ℚ))) :
    toQ2 (kSumTo Ct n) = Array.foldl qadd ((0 : ℚ), (0 : ℚ)) A := by
  have h1 : Array.foldl qadd ((0 : ℚ), (0 : ℚ)) A =
      (List.range' 0 n).foldl (fun s i => qadd s (A.getD i ((0 : ℚ), (0 : ℚ))))
        ((0 : ℚ), (0 : ℚ)) := by
    rw [← Array.foldl_toList]
    have := foldl_getD_aux qadd ((0 : ℚ), (0 : ℚ)) A.toList A.toList 0
      ((0 : ℚ), (0 : ℚ)) (fun k _ => by rw [Nat.zero_add])
    rw [this]
    have hlen : A.toList.length = n := by simpa using hsz
    rw [hlen]
    congr 1
    funext s i
    rw [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_toList]
  rw [h1]
  have key : ∀ m, (∀ j, j < m →
      toQ2 (Ct.getD kQ2z j) = A.getD j ((0 : ℚ), (0 : ℚ))) →
      toQ2 (kSumTo Ct m) = (List.range' 0 m).foldl
        (fun s i => qadd s (A.getD i ((0 : ℚ), (0 : ℚ)))) ((0 : ℚ), (0 : ℚ)) := by
    intro m
    induction m with
    | zero => intro _; exact toQ2_kQ2z
    | succ m ihm =>
      intro hCm
      rw [kSumTo, List.range'_concat, List.foldl_append, List.foldl_cons,
        List.foldl_nil, toQ2_kRed2, toQ2_kAdd2, toQ2_kRed2,
        ihm (fun j hj => hCm j (by omega)), hCm m (by omega)]
      norm_num
  exact key n hC

/-! #### `checkLeaf` -/

theorem foldE_rel (ctx : Ctx) (nt : KVec KQ2) (et : KVec (Option KRow))
    (assign : List (ℕ × Fin 2))
    (H1 : ∀ l, l < ctx.T.nLab → toQ2 (nt.getD kQ2z l) = ctx.T.normalOf l)
    (H2 : ∀ j, Option.map decodeRow (et.getD none j) = ctx.eRows.getD j none) :
    ∀ (kmu : List (RowKey × KQ)) (A : Array Q2) (LB : ℚ) (t : KVec KQ2)
      (LBk : KQ), CRel ctx.T.nLab A t → toQ LBk = LB →
      (match kApplyRows ctx.T.nLab nt et assign kmu (t, LBk) with
       | none => (foldE (fun s kv => applyRow ctx assign s.1 s.2 kv)
           (kmu.map (fun kv => (kv.1, toQ kv.2))) (A, LB)).1 = some false
       | some (t', LBk') => ∃ A' LB',
           foldE (fun s kv => applyRow ctx assign s.1 s.2 kv)
             (kmu.map (fun kv => (kv.1, toQ kv.2))) (A, LB) = (none, A', LB') ∧
           CRel ctx.T.nLab A' t' ∧ toQ LBk' = LB') := by
  intro kmu
  induction kmu with
  | nil =>
    intro A LB t LBk hC hLB
    exact ⟨A, LB, rfl, hC, hLB⟩
  | cons kv rest ih =>
    obtain ⟨key, kvv⟩ := kv
    intro A LB t LBk hC hLB
    have harel := applyRow_rel ctx nt et assign A LB t LBk key kvv H1 H2 hC hLB
    rw [kApplyRows, List.map_cons, foldE]
    dsimp only
    cases happ : applyRow ctx assign A LB (key, toQ kvv) with
    | none =>
      cases hkapp : kApplyRow ctx.T.nLab nt et assign t LBk (key, kvv) with
      | none => rfl
      | some ks' =>
        rw [happ, hkapp] at harel
        exact harel.elim
    | some st =>
      obtain ⟨A', LB'⟩ := st
      cases hkapp : kApplyRow ctx.T.nLab nt et assign t LBk (key, kvv) with
      | none =>
        rw [happ, hkapp] at harel
        exact harel.elim
      | some ks' =>
        obtain ⟨t', LBk'⟩ := ks'
        rw [happ, hkapp] at harel
        obtain ⟨hC', hLB'⟩ := harel
        exact ih A' LB' t' LBk' hC' hLB'

theorem beq_pair_zero (sq : Q2) :
    (sq != ((0 : ℚ), (0 : ℚ))) = !(decide (sq.1 = 0) && decide (sq.2 = 0)) := by
  obtain ⟨a, b⟩ := sq
  rw [Bool.eq_iff_iff]
  simp [bne_iff_ne, Prod.ext_iff]
  tauto

theorem kCheckLeaf_eq (ctx : Ctx) (nt : KVec KQ2) (et : KVec (Option KRow))
    (kR kL : ℕ) (ktgt : KQ) (assign : List (ℕ × Fin 2))
    (rect : ℕ × ℕ × ℕ × ℕ) (kmu : List (RowKey × KQ))
    (H1 : ∀ l, l < ctx.T.nLab → toQ2 (nt.getD kQ2z l) = ctx.T.normalOf l)
    (H2 : ∀ j, Option.map decodeRow (et.getD none j) = ctx.eRows.getD j none)
    (hn : ctx.T.nLab = 3 + kR + kL) (hkR : ctx.T.kR = kR)
    (hkL : ctx.T.kL = kL) (htgt : toQ ktgt = ctx.target) :
    kCheckLeaf (3 + kR + kL) nt et kR kL ktgt assign rect kmu
      = checkLeaf ctx assign rect (kmu.map (fun kv => (kv.1, toQ kv.2))) := by
  obtain ⟨pLo, pHi, qLo, qHi⟩ := rect
  rw [checkLeaf_eq_qspec]
  unfold kCheckLeaf qLeafSpec
  rw [← hn]
  have hC0 : CRel ctx.T.nLab (Array.replicate ctx.T.nLab ((0 : ℚ), (0 : ℚ)))
      (KVec.full kQ2z (bits ctx.T.nLab + 1)) := by
    refine ⟨Array.size_replicate, fun j hj => ?_, fun j hj => ?_⟩
    · refine KVec.has_full _ _ ?_
      have h1 : ctx.T.nLab < 2 ^ bits ctx.T.nLab := lt_two_pow_bits _
      have h2 : 2 ^ (bits ctx.T.nLab + 1) = 2 * 2 ^ bits ctx.T.nLab := by
        rw [pow_succ]; ring
      omega
    · rw [KVec.getD_full, toQ2_kQ2z, Array.getD_eq_getD_getElem?,
        Array.getElem?_replicate, if_pos (by omega)]
      rfl
  have hfold := foldE_rel ctx nt et assign H1 H2 kmu _ _ _ _ hC0 toQ_kQ0
  cases hk : kApplyRows ctx.T.nLab nt et assign kmu
      (KVec.full kQ2z (bits ctx.T.nLab + 1), kQ0) with
  | none =>
    rw [hk] at hfold
    rcases hE : foldE (fun s kv => applyRow ctx assign s.1 s.2 kv)
        (kmu.map (fun kv => (kv.1, toQ kv.2)))
        (Array.replicate ctx.T.nLab ((0 : ℚ), (0 : ℚ)), (0 : ℚ)) with ⟨r, st⟩
    rw [hE] at hfold
    simp only at hfold
    rw [hE, hfold]
  | some p =>
    obtain ⟨t', LBk'⟩ := p
    rw [hk] at hfold
    obtain ⟨A', LB', hfe, hC', hLB'⟩ := hfold
    rw [hfe]
    dsimp only
    obtain ⟨hsz', hhas', hpt'⟩ := hC'
    -- the zero-sum test
    have hsum : toQ2 (kSumTo t' ctx.T.nLab) = Array.foldl qadd ((0 : ℚ), (0 : ℚ)) A' :=
      kSumTo_rel t' A' ctx.T.nLab hsz' hpt'
    have hzero : (!(kEqZero (kSumTo t' ctx.T.nLab).1 &&
        kEqZero (kSumTo t' ctx.T.nLab).2)) =
        (Array.foldl qadd ((0 : ℚ), (0 : ℚ)) A' != ((0 : ℚ), (0 : ℚ))) := by
      rw [beq_pair_zero, kEqZero_eq, kEqZero_eq]
      have h1 : toQ (kSumTo t' ctx.T.nLab).1 =
          (Array.foldl qadd ((0 : ℚ), (0 : ℚ)) A').1 := by rw [← hsum]; rfl
      have h2 : toQ (kSumTo t' ctx.T.nLab).2 =
          (Array.foldl qadd ((0 : ℚ), (0 : ℚ)) A').2 := by rw [← hsum]; rfl
      rw [h1, h2]
    rw [hzero]
    by_cases hz : (Array.foldl qadd ((0 : ℚ), (0 : ℚ)) A' != ((0 : ℚ), (0 : ℚ))) = true
    · rw [if_pos hz, if_pos hz]
    · rw [if_neg hz, if_neg hz]
      -- family value
      have hfam : toQ (kRed (kFamilyMaxNorm2 kR kL t' pLo pHi qLo qHi))
          = familyMaxNorm2 ctx.T A' pLo pHi qLo qHi := by
        rw [toQ_kRed, familyMaxNorm2_eq_qspec, hkR, hkL]
        exact kFamily_eq kR kL A' t' (fun j hj => hpt' j (by omega)) pLo pHi qLo qHi
      rw [kLe_eq, kLe_eq, hfam, toQ_kQ1, htgt, hLB']

/-! #### The tree recursion -/

theorem all_congr {α : Type _} (l : List α) (f g : α → Bool)
    (h : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.all_cons, List.all_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem kSplitStruct_eq (cells : List ((ℕ × ℕ × ℕ × ℕ) × KTree))
    (rect : ℕ × ℕ × ℕ × ℕ) :
    Partition.splitStruct (cells.map (fun x => (x.1, decodeTree x.2))) rect
      = kSplitStruct cells rect := by
  unfold Partition.splitStruct kSplitStruct
  rw [List.all_map, List.map_map]
  rfl

theorem kCheckTreeCore_eq (ctx : Ctx) (nt : KVec KQ2) (et : KVec (Option KRow))
    (esz kR kL : ℕ) (ktgt : KQ)
    (H1 : ∀ l, l < ctx.T.nLab → toQ2 (nt.getD kQ2z l) = ctx.T.normalOf l)
    (H2 : ∀ j, Option.map decodeRow (et.getD none j) = ctx.eRows.getD j none)
    (hn : ctx.T.nLab = 3 + kR + kL) (hkR : ctx.T.kR = kR)
    (hkL : ctx.T.kL = kL) (htgt : toQ ktgt = ctx.target)
    (hesz : esz = ctx.eRows.size) :
    ∀ (fuel : ℕ) (t : KTree) (assign : List (ℕ × Fin 2))
      (rect : ℕ × ℕ × ℕ × ℕ),
      kCheckTreeCore (3 + kR + kL) nt et esz kR kL ktgt fuel t assign rect
        = checkTree ctx fuel (decodeTree t) assign rect := by
  intro fuel
  induction fuel with
  | zero => intro t assign rect; rfl
  | succ fuel ih =>
    intro t assign rect
    match t with
    | .pl m c0 c1 =>
      rw [decodeTree, Partition.checkTree_pl_eq, kCheckTreeCore,
        ih c0 ((m, 0) :: assign) rect, ih c1 ((m, 1) :: assign) rect, hesz]
    | .split cells =>
      rw [decodeTree_split, Partition.checkTree_split_eq, kSplitStruct_eq,
        kCheckTreeCore]
      congr 1
      rw [List.all_map]
      exact (all_congr _ _ _ (fun x _ => (ih x.2 assign x.1).symm)).symm
    | .leaf mu =>
      rw [decodeTree, Partition.checkTree_leaf_eq, kCheckTreeCore]
      exact kCheckLeaf_eq ctx nt et kR kL ktgt assign rect mu
        H1 H2 hn hkR hkL htgt

/-! #### Top level -/

theorem kNormalOf_decode (c : KCtx) (l : ℕ) :
    toQ2 (kNormalOf c.kR c.right c.left l) = (decodeCtx c).T.normalOf l := by
  unfold kNormalOf LabelTables.normalOf decodeCtx
  dsimp only
  by_cases h0 : (l == 0) = true
  · rw [if_pos h0, if_pos h0]
    norm_num [toQ2, toQ, kQ0]
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : (l == 1) = true
    · rw [if_pos h1, if_pos h1]
      norm_num [toQ2, toQ, kQ0]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : (l == 2) = true
      · rw [if_pos h2, if_pos h2]
        norm_num [toQ2, toQ, kQ0]
      · rw [if_neg h2, if_neg h2]
        by_cases h3 : l < 3 + c.kR
        · rw [if_pos h3, if_pos h3, ← toQ2_kQ2z, toArray_getD, getD_map_default]
        · rw [if_neg h3, if_neg h3, ← toQ2_kQ2z, toArray_getD, getD_map_default]

theorem kCheckTree_eq_checkTree (c : KCtx) (fuel : ℕ) (t : KTree)
    (assign : List (ℕ × Fin 2)) (rect : ℕ × ℕ × ℕ × ℕ) :
    kCheckTree c fuel t assign rect
      = checkTree (decodeCtx c) fuel (decodeTree t) assign rect := by
  unfold kCheckTree
  dsimp only
  refine kCheckTreeCore_eq (decodeCtx c) _ _ _ c.kR c.kL c.target
    ?_ ?_ rfl rfl rfl rfl ?_ fuel t assign rect
  · intro l hl
    have hl' : l < 3 + c.kR + c.kL := hl
    rw [KVec.getD_ofList]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hl']
    dsimp only [Option.map_some, Option.getD_some]
    exact kNormalOf_decode c l
  · intro j
    rw [KVec.getD_ofList]
    unfold decodeCtx
    dsimp only
    rw [toArray_getD]
    rw [show (none : Option RowData) = Option.map decodeRow none from rfl,
      getD_map_default]
  · unfold decodeCtx
    simp

end MoserWorm.UpperBound.Certificate.Kernel
