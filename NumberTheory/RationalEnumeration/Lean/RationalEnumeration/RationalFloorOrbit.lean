import Init.Data.Rat.Lemmas
import Init.Tactics

namespace LeanProofs

/-! ## Stern–Brocot pair generator

`cwPair n` is the `n`-th coprime pair in Calkin–Wilf order, with its positivity,
coprimality, and left/right child equations. -/

def cwPair : Nat -> Nat × Nat
  | 0 => (1, 1)
  | n + 1 =>
      let p := cwPair (n / 2)
      if n % 2 = 0 then (p.1, p.1 + p.2) else (p.1 + p.2, p.2)
termination_by n => n
decreasing_by omega

@[simp] theorem cwPair_zero : cwPair 0 = (1, 1) := cwPair.eq_1

theorem cwPair_pos (n : Nat) : 0 < (cwPair n).1 ∧ 0 < (cwPair n).2 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp
    | succ m =>
      have hp := ih (m / 2) (by omega)
      rw [cwPair.eq_2]
      by_cases h : m % 2 = 0
      · simp [h]
        omega
      · simp [h]
        omega

theorem cwPair_coprime (n : Nat) : Nat.Coprime (cwPair n).1 (cwPair n).2 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [Nat.Coprime]
    | succ m =>
      have hp := ih (m / 2) (by omega)
      rw [cwPair.eq_2]
      by_cases h : m % 2 = 0
      · simp [h, Nat.Coprime] at hp ⊢
        simpa using hp
      · simp [h, Nat.Coprime] at hp ⊢
        simpa [Nat.gcd_comm] using hp

theorem cwPair_left (n : Nat) :
    cwPair (2 * n + 1) = (let p := cwPair n; (p.1, p.1 + p.2)) := by
  rw [cwPair.eq_2]
  have hdiv : (2 * n) / 2 = n := by omega
  have hmod : (2 * n) % 2 = 0 := by omega
  simp [hdiv, hmod]

theorem cwPair_right (n : Nat) :
    cwPair (2 * n + 2) = (let p := cwPair n; (p.1 + p.2, p.2)) := by
  rw [show 2 * n + 2 = (2 * n + 1).succ by omega]
  rw [cwPair.eq_2]
  have hdiv : (2 * n + 1) / 2 = n := by omega
  simp [hdiv]

/-! ## Inverse index and the pair ↔ position round-trips

`cwIndex a b` recovers the position of a coprime pair; `cwPair_cwIndex`,
`cwIndex_cwPair`, and `cwPair_succ` establish the bijection with `Nat`. -/

def cwIndex (a b : Nat) : Nat :=
  if a = 0 ∨ b = 0 then 0
  else if a = b then 0
  else if a < b then 2 * cwIndex a (b - a) + 1
  else 2 * cwIndex (a - b) b + 2
termination_by a + b
decreasing_by
  all_goals
    simp_all only [not_or]
    omega

theorem cwIndex_eq_of_eq {a b : Nat} (ha : 0 < a) (hb : 0 < b) (h : a = b) :
    cwIndex a b = 0 := by
  subst a
  rw [cwIndex.eq_def]
  have hz : ¬ (b = 0 ∨ b = 0) := by omega
  simp only [hz, ↓reduceIte]

theorem cwIndex_left {a b : Nat} (ha : 0 < a) (h : a < b) :
    cwIndex a b = 2 * cwIndex a (b - a) + 1 := by
  rw [cwIndex.eq_def]
  have hz : ¬ (a = 0 ∨ b = 0) := by omega
  have hne : ¬ a = b := by omega
  simp only [hz, hne, h, ↓reduceIte]

theorem cwIndex_right {a b : Nat} (hb : 0 < b) (h : b < a) :
    cwIndex a b = 2 * cwIndex (a - b) b + 2 := by
  rw [cwIndex.eq_def]
  have hz : ¬ (a = 0 ∨ b = 0) := by omega
  have hne : ¬ a = b := by omega
  have hnot : ¬ a < b := by omega
  simp only [hz, hne, hnot, ↓reduceIte]

theorem coprime_sub_right {a b : Nat} (h : a < b) (hc : Nat.Coprime a b) :
    Nat.Coprime a (b - a) := by
  rw [Nat.Coprime, Nat.gcd_sub_self_right (Nat.le_of_lt h)]
  exact hc

theorem coprime_sub_left {a b : Nat} (h : b < a) (hc : Nat.Coprime a b) :
    Nat.Coprime (a - b) b := by
  rw [Nat.Coprime, Nat.gcd_sub_self_left (Nat.le_of_lt h)]
  exact hc

theorem cwPair_cwIndex (a b : Nat) (ha : 0 < a) (hb : 0 < b)
    (hc : Nat.Coprime a b) :
    cwPair (cwIndex a b) = (a, b) := by
  revert ha hb hc
  induction a, b using cwIndex.induct with
  | case1 a b hz =>
      intro ha hb hc
      omega
  | case2 b hz =>
      intro ha hb hc
      have hb1 : b = 1 := by simpa using hc
      subst b
      simp [cwIndex_eq_of_eq]
  | case3 a b hz hne hlt ih =>
      intro ha hb hc
      have hbsub : 0 < b - a := by omega
      have hc' : Nat.Coprime a (b - a) := coprime_sub_right hlt hc
      have ih' := ih ha hbsub hc'
      rw [cwIndex_left ha hlt, cwPair_left, ih']
      simp
      omega
  | case4 a b hz hne hnlt ih =>
      intro ha hb hc
      have hba : b < a := by omega
      have hasub : 0 < a - b := by omega
      have hc' : Nat.Coprime (a - b) b := coprime_sub_left hba hc
      have ih' := ih hasub hb hc'
      rw [cwIndex_right hb hba, cwPair_right, ih']
      simp
      omega

theorem cwIndex_cwPair (n : Nat) : cwIndex (cwPair n).1 (cwPair n).2 = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      simp [cwIndex_eq_of_eq]
    | succ m =>
      have hp := cwPair_pos (m / 2)
      have ihp := ih (m / 2) (by omega)
      rw [cwPair.eq_2]
      by_cases h : m % 2 = 0
      · simp [h]
        rw [cwIndex_left hp.left (by omega)]
        rw [show (cwPair (m / 2)).1 + (cwPair (m / 2)).2 - (cwPair (m / 2)).1 =
            (cwPair (m / 2)).2 by omega]
        rw [ihp]
        omega
      · simp [h]
        rw [cwIndex_right hp.right (by omega)]
        rw [show (cwPair (m / 2)).1 + (cwPair (m / 2)).2 - (cwPair (m / 2)).2 =
            (cwPair (m / 2)).1 by omega]
        rw [ihp]
        omega

def pairNext (p : Nat × Nat) : Nat × Nat :=
  (p.2, (2 * (p.1 / p.2) + 1) * p.2 - p.1)

private theorem pairNext_right_child_arith {a b : Nat} (hb : 0 < b) :
    b + ((2 * (a / b) + 1) * b - a) =
      (2 * (a / b + 1) + 1) * b - (a + b) := by
  have hlt : a < a / b * b + b := Nat.lt_div_mul_add hb
  simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
  omega

theorem cwPair_succ (n : Nat) : cwPair (n + 1) = pairNext (cwPair n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      simp [cwPair.eq_1, cwPair.eq_2, pairNext]
    | succ m =>
      have hp := cwPair_pos (m / 2)
      by_cases h : m % 2 = 0
      · have hm : m = 2 * (m / 2) := by
          have := Nat.div_add_mod m 2
          omega
        rw [show (m + 1) + 1 = 2 * (m / 2) + 2 by omega]
        rw [show m + 1 = 2 * (m / 2) + 1 by omega]
        rw [cwPair_right, cwPair_left]
        simp [pairNext]
        have hdiv : (cwPair (m / 2)).1 /
            ((cwPair (m / 2)).1 + (cwPair (m / 2)).2) = 0 := by
          apply Nat.div_eq_of_lt
          omega
        simp [hdiv]
      · have hm1 : m % 2 = 1 := by omega
        have hm : m = 2 * (m / 2) + 1 := by
          have := Nat.div_add_mod m 2
          omega
        rw [show (m + 1) + 1 = 2 * ((m / 2) + 1) + 1 by omega]
        rw [show m + 1 = 2 * (m / 2) + 2 by omega]
        rw [cwPair_left, cwPair_right]
        have ihp := ih (m / 2) (by omega)
        simp [pairNext]
        rw [ihp]
        simp [pairNext]
        have hdiv : ((cwPair (m / 2)).1 + (cwPair (m / 2)).2) /
              (cwPair (m / 2)).2 =
            (cwPair (m / 2)).1 / (cwPair (m / 2)).2 + 1 := by
          rw [show (cwPair (m / 2)).1 + (cwPair (m / 2)).2 =
              (cwPair (m / 2)).1 + (cwPair (m / 2)).2 * 1 by omega]
          rw [Nat.add_mul_div_left _ _ hp.right]
        rw [hdiv]
        exact pairNext_right_child_arith hp.right

/-! ## Bridge to `Rat` and the orbit map

`pairRat` sends a coprime pair to a rational; `rationalNext`/`rationalFloorOrbit`
transport the successor map to `Rat`, with `rationalNext_cwRat` the key step. -/

def pairRat (p : Nat × Nat) : Rat :=
  match p with
  | (a, b) => Rat.divInt (a : Int) (b : Int)

theorem intCast_rat_divInt_one (z : Int) : (z : Rat) = Rat.divInt z 1 := by
  simpa using (Rat.mk_eq_divInt (num := z) (den := 1) (nz := by omega) (c := by simp))

/-- On a coprime pair with nonzero denominator, `pairRat` is literally the
canonical `Rat` structure; `pairRat_num` and `pairRat_den` project it. -/
theorem pairRat_eq_mk {a b : Nat} (hb : b ≠ 0) (hc : Nat.Coprime a b) :
    pairRat (a, b) =
      { num := (a : Int), den := b, den_nz := hb,
        reduced := by simpa using hc } := by
  simpa [pairRat] using
    (Rat.mk_eq_divInt (num := (a : Int)) (den := b) (nz := hb)
      (c := by simpa using hc)).symm

theorem pairRat_num {a b : Nat} (hb : b ≠ 0) (hc : Nat.Coprime a b) :
    (pairRat (a, b)).num = a := by
  rw [pairRat_eq_mk hb hc]

theorem pairRat_den {a b : Nat} (hb : b ≠ 0) (hc : Nat.Coprime a b) :
    (pairRat (a, b)).den = b := by
  rw [pairRat_eq_mk hb hc]

theorem pairRat_floor {a b : Nat} (hb : b ≠ 0) (hc : Nat.Coprime a b) :
    (pairRat (a, b)).floor = ((a / b : Nat) : Int) := by
  rw [Rat.floor_def]
  rw [pairRat_num hb hc, pairRat_den hb hc]
  exact (Int.natCast_ediv a b).symm

def rationalNext (q : Rat) : Rat :=
  1 / (1 - q + 2 * (q.floor : Rat))

private theorem denominatorExpr {a b : Nat} (hb : b ≠ 0) :
    1 - Rat.divInt (a : Int) (b : Int) + 2 * Rat.divInt ((a / b : Nat) : Int) 1 =
      Rat.divInt (((2 * (a / b) + 1) * b - a : Nat) : Int) (b : Int) := by
  have hbInt : (b : Int) ≠ 0 := by omega
  have hdInt : (((2 * (a / b) + 1) * b - a : Nat) : Int) =
      ((2 * (a / b) + 1 : Nat) * b : Int) - (a : Int) := by
    have hbpos : 0 < b := by omega
    have hle : a ≤ (2 * (a / b) + 1) * b := by
      have hlt : a < a / b * b + b := Nat.lt_div_mul_add hbpos
      simp [Nat.add_mul, Nat.mul_assoc]
      omega
    exact Int.natCast_sub hle
  rw [show (1 : Rat) = Rat.divInt 1 1 by exact intCast_rat_divInt_one 1]
  rw [show (2 : Rat) = Rat.divInt 2 1 by exact intCast_rat_divInt_one 2]
  rw [Rat.divInt_sub_divInt (1 : Int) (a : Int) (by omega) hbInt]
  rw [Rat.divInt_mul_divInt]
  rw [Rat.divInt_add_divInt _ _ (by omega) (by omega)]
  rw [hdInt]
  rw [Int.natCast_ediv a b]
  simp
  have hnum : (b : Int) - (a : Int) + 2 * ((a : Int) / (b : Int)) * (b : Int) =
      (2 * ((a : Int) / (b : Int)) + 1) * (b : Int) - (a : Int) := by
    simp [Int.add_mul, Int.mul_assoc, Int.sub_eq_add_neg, Int.add_assoc]
    omega
  rw [hnum]

theorem rationalNext_pairRat {a b : Nat} (hb : b ≠ 0) (hc : Nat.Coprime a b) :
    rationalNext (pairRat (a, b)) = pairRat (pairNext (a, b)) := by
  unfold rationalNext
  rw [pairRat_floor hb hc]
  simp only [pairRat, pairNext]
  rw [intCast_rat_divInt_one ((a / b : Nat) : Int)]
  rw [denominatorExpr hb]
  rw [show (1 : Rat) = Rat.divInt 1 1 by exact intCast_rat_divInt_one 1]
  rw [Rat.div_def, Rat.inv_divInt, Rat.divInt_mul_divInt]
  simp

def cwRat (n : Nat) : Rat := pairRat (cwPair n)

theorem rationalNext_cwRat (n : Nat) : rationalNext (cwRat n) = cwRat (n + 1) := by
  cases h : cwPair n with
  | mk a b =>
      have hpos := cwPair_pos n
      have hc := cwPair_coprime n
      rw [h] at hpos hc
      unfold cwRat
      rw [cwPair_succ, h]
      exact rationalNext_pairRat (by omega) hc

def rationalFloorOrbit : Nat -> Rat
  | 0 => 0
  | n + 1 => rationalNext (rationalFloorOrbit n)

@[simp] theorem rationalFloorOrbit_zero : rationalFloorOrbit 0 = 0 := rfl

theorem rationalNext_zero : rationalNext 0 = pairRat (1, 1) := by
  rw [show (0 : Rat) = pairRat (0, 1) by rfl]
  rw [rationalNext_pairRat (by omega) (by simp [Nat.Coprime])]
  rfl

theorem rationalFloorOrbit_succ (n : Nat) : rationalFloorOrbit (n + 1) = cwRat n := by
  induction n with
  | zero =>
      change rationalNext 0 = cwRat 0
      rw [rationalNext_zero]
      unfold cwRat
      rw [cwPair_zero]
  | succ n ih =>
      change rationalNext (rationalFloorOrbit (n + 1)) = cwRat (n + 1)
      rw [ih]
      exact rationalNext_cwRat n

theorem pairRat_ne_zero {a b : Nat} (ha : 0 < a) (hb : b ≠ 0) (hc : Nat.Coprime a b) :
    pairRat (a, b) ≠ 0 := by
  intro h
  have hn := congrArg Rat.num h
  rw [pairRat_num hb hc] at hn
  change (a : Int) = 0 at hn
  omega

theorem cwRat_ne_zero (n : Nat) : cwRat n ≠ 0 := by
  unfold cwRat
  exact pairRat_ne_zero (cwPair_pos n).left (by have h := (cwPair_pos n).right; omega)
    (cwPair_coprime n)

theorem rationalFloorOrbit_eq_zero_iff (n : Nat) : rationalFloorOrbit n = 0 ↔ n = 0 := by
  constructor
  · intro h
    cases n with
    | zero => rfl
    | succ n =>
        have hz : cwRat n = 0 := by
          rw [← rationalFloorOrbit_succ n]
          exact h
        exact False.elim ((cwRat_ne_zero n) hz)
  · intro h
    subst h
    rfl

/-! ## Injectivity and the exactly-once enumeration

`pairRat_inj` gives injectivity of the pair-to-rational map; combined with the
round-trips it yields the headline `rationalFloorOrbit_visits_each_nonnegative_
rat_exactly_once`. -/

theorem pairRat_inj {a b c d : Nat}
    (hb : b ≠ 0) (hd : d ≠ 0)
    (hab : Nat.Coprime a b) (hcd : Nat.Coprime c d)
    (h : pairRat (a, b) = pairRat (c, d)) :
    a = c ∧ b = d := by
  have hn := congrArg Rat.num h
  have hden := congrArg Rat.den h
  rw [pairRat_num hb hab, pairRat_num hd hcd] at hn
  rw [pairRat_den hb hab, pairRat_den hd hcd] at hden
  exact ⟨Int.ofNat.inj hn, hden⟩

private theorem nonzero_num_abs_pos {q : Rat} (hnez : q ≠ 0) :
    0 < q.num.natAbs := by
  have hnumNe : q.num ≠ 0 := by
    intro h
    exact hnez ((Rat.num_eq_zero).mp h)
  exact Int.natAbs_pos.mpr hnumNe

private theorem pairRat_of_nonneg {q : Rat} (hq : 0 ≤ q) :
    pairRat (q.num.natAbs, q.den) = q := by
  have hnumNonneg : 0 ≤ q.num := (Rat.num_nonneg).mpr hq
  simp only [pairRat]
  rw [Int.natAbs_of_nonneg hnumNonneg]
  exact Rat.num_divInt_den q

private theorem rationalFloorOrbit_exists_of_nonneg_nonzero {q : Rat}
    (hq : 0 ≤ q) (hnez : q ≠ 0) :
    rationalFloorOrbit (cwIndex q.num.natAbs q.den + 1) = q := by
  have ha : 0 < q.num.natAbs := nonzero_num_abs_pos hnez
  have hb : 0 < q.den := by have := q.den_nz; omega
  rw [rationalFloorOrbit_succ]
  unfold cwRat
  rw [cwPair_cwIndex q.num.natAbs q.den ha hb q.reduced]
  exact pairRat_of_nonneg hq

private theorem rationalFloorOrbit_unique_of_nonneg_nonzero {q : Rat} {n : Nat}
    (hq : 0 ≤ q) (hnez : q ≠ 0) (hn : rationalFloorOrbit n = q) :
    n = cwIndex q.num.natAbs q.den + 1 := by
  cases n with
  | zero =>
      have hqzero : q = 0 := by
        simpa using hn.symm
      exact False.elim (hnez hqzero)
  | succ k =>
      have hk : cwRat k = q := by
        rw [← rationalFloorOrbit_succ k]
        exact hn
      cases hpair : cwPair k with
      | mk a b =>
          have hpos := cwPair_pos k
          have hc := cwPair_coprime k
          rw [hpair] at hpos hc
          have hkpair : pairRat (a, b) = pairRat (q.num.natAbs, q.den) := by
            have hkq : pairRat (a, b) = q := by
              simpa [cwRat, hpair] using hk
            exact hkq.trans (pairRat_of_nonneg hq).symm
          have hs := pairRat_inj (by omega) q.den_nz hc q.reduced hkpair
          have hidx : cwIndex a b = k := by
            have h := cwIndex_cwPair k
            rw [hpair] at h
            exact h
          have hidxq : cwIndex q.num.natAbs q.den = k := by
            rw [← hs.left, ← hs.right]
            exact hidx
          omega

theorem rationalFloorOrbit_visits_each_nonnegative_rat_exactly_once
    (q : Rat) (hq : 0 ≤ q) :
    ∃ n : Nat, rationalFloorOrbit n = q ∧
      ∀ m : Nat, rationalFloorOrbit m = q → m = n := by
  by_cases hzero : q = 0
  · subst q
    refine ⟨0, rfl, ?_⟩
    intro n hn
    exact (rationalFloorOrbit_eq_zero_iff n).mp hn
  · refine ⟨cwIndex q.num.natAbs q.den + 1,
      rationalFloorOrbit_exists_of_nonneg_nonzero hq hzero, ?_⟩
    intro n hn
    exact rationalFloorOrbit_unique_of_nonneg_nonzero hq hzero hn

end LeanProofs
