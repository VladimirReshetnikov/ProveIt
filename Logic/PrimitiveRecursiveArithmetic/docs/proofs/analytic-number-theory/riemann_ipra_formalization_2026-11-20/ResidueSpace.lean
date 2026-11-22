import DivisorMatrices
import DiscreteForms
import EnergyInequality

/-! Finite residue-vector packets for the Bagchi formulation of the
Nyman–Beurling–Báez-Duarte criterion. The natural-number program constructs
actual closed formulas. The rational lemmas give their finite tail estimate
and the precision change; they use no Hilbert space or infinite sums. -/
namespace ResidueSpace
open LeanProofs.ConciseIPRA PacketLanguage DivisorMatrices

inductive Target | one | singleton | step
inductive Test | prefixes | certificate | fixedCutoff

/-- A coefficient word has K digits in base H+2, at moduli 2,...,K+1. -/
def row : PR 4 := program ["K","H","word","n"] <|
  sumTo "i" (v "K") <|
    digitE (v "word") (v "H"+2) (v "i") * modE (v "n") (v "i"+2)

def budget : PR 5 := program ["K","H","u","w","D"] <|
  v "D" + (sumTo "i" (v "K") <|
    (digitE (v "u") (v "H"+2) (v "i") + digitE (v "w") (v "H"+2) (v "i")) * (v "i"+1))

private def targetAt {ctx} (target : Target) (m n : E ctx) : E ctx :=
  match target with
  | .one => 1
  | .singleton => eqB m n
  | .step => leB m n

def residual (target : Target) : PR 7 := program ["m","K","H","u","w","D","n"] <|
  let x := v "D" * targetAt target (v "m") (v "n") +
    call row [v "K",v "H",v "w",v "n"]
  let y := call row [v "K",v "H",v "u",v "n"]
  (x-y)+(y-x)

def denominator : PR 1 := program ["N"] <|
  prodTo "j" (v "N") <| (v "j"+1)*(v "j"+2)

def numerator (target : Target) : PR 7 := program ["m","K","H","u","w","D","N"] <|
  sumTo "i" (v "N") <|
    powE (call (residual target) [v "m",v "K",v "H",v "u",v "w",v "D",v "i"+1]) 2 *
      (prodTo "j" (v "N") <| iteE (eqB (v "i") (v "j")) 1 ((v "j"+1)*(v "j"+2)))

private def excess {ctx} (target : Target) (buffered : Bool) (m K H u w D t N : E ctx) : E ctx :=
  let p := call denominator [N]
  let s := call (numerator target) [m,K,H,u,w,D,N]
  if buffered then
    let b := call budget [K,H,u,w,D]
    t*((N+1)*s + (powE b 2)*p) - powE D 2*(N+1)*p
  else t*s - powE D 2*p

/-- Offset binders give m,D,t ≥ 1. The one target ignores m. -/
def sentence (target : Target) (test : Test) : Fm PTm 0 :=
  allN (ctx := []) "m" <| allN "t" <| exN "K" <| exN "H" <| exN "u" <|
  exN "w" <| exN "d" <|
    match test with
    | .prefixes => allN "N" <| zeroTest <| excess target false (v "m"+1) (v "K")
        (v "H") (v "u") (v "w") (v "d"+1) (v "t"+1) (v "N")
    | .certificate => exN "J" <| zeroTest <| excess target true (v "m"+1) (v "K")
        (v "H") (v "u") (v "w") (v "d"+1) (v "t"+1) (v "J")
    | .fixedCutoff => zeroTest <|
        let D := v "d"+1
        let t := v "t"+1
        let b := call budget [v "K",v "H",v "u",v "w",D]
        excess target true (v "m"+1) (v "K") (v "H") (v "u") (v "w") D t (2*t*(powE b 2))

/-- The argument g n is the absolute unnormalized integer residual at n. -/
def energy (g : ℕ → ℕ) : ℕ → ℚ
  | 0 => 0
  | n+1 => energy g n + (g (n+1) : ℚ)^2 / ((n+1 : ℕ) * ((n+2 : ℕ) : ℚ))

private theorem incr_nonneg (g : ℕ → ℕ) (n : ℕ) : energy g n ≤ energy g (n+1) := by
  rw [energy]
  have h : (0 : ℚ) ≤ (g (n+1) : ℚ)^2 / ((n+1 : ℕ) * ((n+2 : ℕ) : ℚ)) :=
    div_nonneg (sq_nonneg _) (by positivity)
  linarith

theorem energy_mono (g : ℕ → ℕ) : Monotone (energy g) :=
  monotone_nat_of_le_succ (incr_nonneg g)

/-- The potential energy_N + B²/(N+1) decreases at every step. -/
theorem upper_decreases (g : ℕ → ℕ) (B : ℕ) (bound : ∀ n, g (n+1) ≤ B) (n : ℕ) :
    energy g (n+1) + (B : ℚ)^2 / ((n+2 : ℕ) : ℚ) ≤
      energy g n + (B : ℚ)^2 / ((n+1 : ℕ) : ℚ) := by
  have hg : (g (n+1) : ℚ) ≤ (B : ℚ) := by exact_mod_cast bound n
  have hs := pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ (g (n+1) : ℚ)) hg 2
  simp only [energy, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp
  nlinarith

theorem upper_antitone (g : ℕ → ℕ) (B : ℕ) (bound : ∀ n, g (n+1) ≤ B) :
    Antitone (fun n : ℕ => energy g n + (B : ℚ)^2 / ((n+1 : ℕ) : ℚ)) :=
  antitone_nat_of_succ_le (upper_decreases g B bound)

theorem covered (g : ℕ → ℕ) (B J N : ℕ) (bound : ∀ n, g (n+1) ≤ B) :
    energy g N ≤ energy g J + (B : ℚ)^2 / ((J+1 : ℕ) : ℚ) := by
  rcases le_total N J with h | h
  · exact (energy_mono g h).trans (le_add_of_nonneg_right (by positivity))
  · exact (le_add_of_nonneg_right (by positivity : (0 : ℚ) ≤ (B : ℚ)^2 / ((N+1 : ℕ) : ℚ))).trans
      (upper_antitone g B bound h)

structure Witness where
  /-- Unnormalized error magnitude on positive indices. -/
  err : ℕ → ℕ
  B : ℕ
  D : ℕ
  d_pos : 0 < D
  bounded : ∀ n, err (n+1) ≤ B

def Witness.good (w : Witness) (t N : ℕ) := (t : ℚ)*energy w.err N ≤ (w.D : ℚ)^2
def Witness.cert (w : Witness) (t J : ℕ) :=
  (t : ℚ)*(energy w.err J + (w.B : ℚ)^2 / ((J+1 : ℕ) : ℚ)) ≤ (w.D : ℚ)^2
def Witness.cutoff (w : Witness) (t : ℕ) := 2*t*w.B^2

theorem cert_covers (w : Witness) {t J : ℕ} (hc : w.cert t J) (N : ℕ) : w.good t N :=
  (mul_le_mul_of_nonneg_left (covered w.err w.B J N w.bounded) (Nat.cast_nonneg t)).trans hc

theorem fixed_of_prefix (w : Witness) (t : ℕ) (h : ∀ N, w.good (2*t) N) :
    w.cert t (w.cutoff t) := by
  let j := w.cutoff t
  have hj : (j : ℚ) = 2*(t : ℚ)*(w.B : ℚ)^2 := by simp [j,Witness.cutoff]
  have hbudget : 2*(t : ℚ)*(w.B : ℚ)^2 / ((j+1 : ℕ) : ℚ) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).2
    push_cast
    linarith
  have hden : 1 ≤ (w.D : ℚ) := by exact_mod_cast w.d_pos
  have hp := h j
  unfold Witness.good at hp
  push_cast at hp
  change (t : ℚ)*(energy w.err j + (w.B : ℚ)^2 / ((j+1 : ℕ) : ℚ)) ≤ _
  have hr : 2*(t : ℚ)*((w.B : ℚ)^2 / ((j+1 : ℕ) : ℚ)) ≤ 1 := by
    simpa only [mul_div_assoc] using hbudget
  nlinarith only [hp, hr, hden, sq_nonneg ((w.D : ℚ)-1)]

/-- C ranges over any particular family of encodable residue approximants. -/
theorem fixed_iff_prefix {C : Type*} (w : C → Witness) :
    (∀ t : ℕ, 0 < t → ∃ c, (w c).cert t ((w c).cutoff t)) ↔
    (∀ t : ℕ, 0 < t → ∃ c, ∀ N, (w c).good t N) := by
  constructor
  · intro h t ht
    obtain ⟨c, hc⟩ := h t ht
    exact ⟨c, cert_covers _ hc⟩
  · intro h t ht
    obtain ⟨c, hc⟩ := h (2*t) (by omega)
    exact ⟨c, fixed_of_prefix _ t hc⟩

theorem cert_iff_prefix {C : Type*} (w : C → Witness) :
    (∀ t : ℕ, 0 < t → ∃ c J, (w c).cert t J) ↔
    (∀ t : ℕ, 0 < t → ∃ c, ∀ N, (w c).good t N) := by
  constructor
  · intro h t ht
    obtain ⟨c, J, hc⟩ := h t ht
    exact ⟨c, cert_covers _ hc⟩
  · intro h t ht
    obtain ⟨c, hc⟩ := (fixed_iff_prefix w).2 h t ht
    exact ⟨c, _, hc⟩

section Reading
open RiemannIPRA.Discrete
open scoped BigOperators

private theorem read_sum {ctx} (name : String) (b : E ctx) (s : E (name::ctx)) (e) :
    denote (sumTo name b s) e = ∑ i ∈ Finset.range (denote b e), denote s (Fin.cases i e) := by
  change overRange 0 (fun i a => a + denote s (Fin.cases i e)) (denote b e) = _
  generalize denote b e = n
  induction n with
  | zero => simp [overRange]
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; rfl

private theorem read_prod {ctx} (name : String) (b : E ctx) (s : E (name::ctx)) (e) :
    denote (prodTo name b s) e = ∏ i ∈ Finset.range (denote b e), denote s (Fin.cases i e) := by
  change overRange 1 (fun i a => a * denote s (Fin.cases i e)) (denote b e) = _
  generalize denote b e = n
  induction n with
  | zero => simp [overRange]
  | succ n ih => rw [Finset.prod_range_succ, ← ih]; rfl

private theorem read_call {ctx r} (f : PR r) (xs : List (E ctx)) (h : xs.length = r) (e) :
    denote (call f xs h) e = value f (fun i => denote (xs[i.val]'(h ▸ i.isLt)) e) := rfl

private theorem read_le {ctx} (a b : E ctx) (e) :
    denote (leB a b) e = (if denote a e ≤ denote b e then 1 else 0) := by
  change value isZeroR _ = _
  rw [value_isZeroR]
  change (if denote (a-b) e = 0 then 1 else 0) = _
  simp [minus, Nat.sub_eq_zero_iff_le]

private theorem read_eq {ctx} (a b : E ctx) (e) :
    denote (eqB a b) e = (if denote a e = denote b e then 1 else 0) := by
  simp only [eqB, times, read_le]
  split <;> split <;> split <;> first | rfl | omega

private theorem read_ite {ctx} (a b c : E ctx) (e) :
    denote (iteE a b c) e = (if denote a e = 0 then denote c e else denote b e) := by
  simp only [iteE, plus, times, read_call, value_clipR, value_isZeroR]
  change bit (denote a e)*denote b e + (if denote a e = 0 then 1 else 0)*denote c e = _
  unfold bit
  split <;> simp

def digit (h word i : ℕ) := word / (h+2)^i % (h+2)
def rowValue (k h word n : ℕ) := ∑ i ∈ Finset.range k, digit h word i * (n % (i+2))
def budgetValue (k h u w d : ℕ) := d + ∑ i ∈ Finset.range k, (digit h u i + digit h w i)*(i+1)
def targetValue : Target → ℕ → ℕ → ℕ
  | .one, _, _ => 1
  | .singleton, m, n => if m = n then 1 else 0
  | .step, m, n => if m ≤ n then 1 else 0

def errorValue (target : Target) (m k h u w d n : ℕ) :=
  let a := d*targetValue target m n + rowValue k h w n
  let b := rowValue k h u n
  (a-b)+(b-a)

private theorem read_pow {ctx} (a b : E ctx) (e) :
    denote (a^b) e = denote a e ^ denote b e := power a b e

private theorem read_row (e) : value row e = rowValue (e 0) (e 1) (e 2) (e 3) := by
  unfold row
  rw [value_program]
  simp only [read_sum, times, digitE, denote_modE, denote_divE, plus,read_pow]
  rfl

private theorem read_budget (e) : value budget e = budgetValue (e 0) (e 1) (e 2) (e 3) (e 4) := by
  unfold budget
  rw [value_program]
  simp only [read_sum, times, digitE, denote_modE, denote_divE, plus,read_pow]
  rfl

private theorem read_target {ctx} (tar : Target) (m n : E ctx) (e) :
    denote (targetAt tar m n) e = targetValue tar (denote m e) (denote n e) := by
  cases tar with
  | one => rfl
  | singleton => exact read_eq _ _ _
  | step => exact read_le _ _ _

private theorem read_residual (tar : Target) (e) : value (residual tar) e =
    errorValue tar (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) := by
  unfold residual
  rw [value_program]
  simp only [plus,minus,times,read_target,read_call,read_row]
  rfl

private theorem error_bound (tar : Target) (m k h u w d n : ℕ) :
    errorValue tar m k h u w d n ≤ budgetValue k h u w d := by
  have htar : d * targetValue tar m n ≤ d := by
    cases tar <;> simp [targetValue] <;> split <;> simp
  have hsum : rowValue k h w n + rowValue k h u n ≤
      ∑ i ∈ Finset.range k, (digit h u i + digit h w i)*(i+1) := by
    simp only [rowValue, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hm : n % (i+2) ≤ i+1 := by have := Nat.mod_lt n (show 0 < i+2 by omega); omega
    rw [← Nat.add_mul, Nat.add_comm (digit h w i)]
    exact Nat.mul_le_mul_left _ hm
  simp only [errorValue,budgetValue]
  omega

def rden (N : ℕ) := ∏ i ∈ Finset.range N, (i+1)*(i+2)
def rnum (g : ℕ → ℕ) (N : ℕ) := ∑ i ∈ Finset.range N, g (i+1)^2 *
  (∏ j ∈ Finset.range N, if i=j then 1 else (j+1)*(j+2))

private theorem read_den (e) : value denominator e = rden (e 0) := by
  unfold denominator
  rw [value_program]
  simp only [read_prod,times,plus]
  rfl

private theorem read_res_call {ctx} (tar : Target) (a b c d l p n : E ctx) (e) :
    denote (call (residual tar) [a,b,c,d,l,p,n]) e =
    errorValue tar (denote a e) (denote b e) (denote c e) (denote d e) (denote l e) (denote p e)
      (denote n e) := by rw [read_call,read_residual]; rfl

private theorem read_num (tar : Target) (e) : value (numerator tar) e =
    rnum (errorValue tar (e 0) (e 1) (e 2) (e 3) (e 4) (e 5)) (e 6) := by
  unfold numerator
  rw [value_program]
  simp only [read_sum,read_prod,times,power,read_ite,read_eq,plus,read_res_call]
  change (∑ i ∈ Finset.range (e 6), _ * (∏ j ∈ Finset.range (e 6),
    if (if i=j then 1 else 0 : ℕ) = 0 then (j+1)*(j+2) else 1)) = _
  simp only [ite_eq_right_iff,one_ne_zero,imp_false,ite_not]
  rfl

private theorem rden_pos (N : ℕ) : 0 < rden N :=
  Finset.prod_pos (fun _ _ => Nat.mul_pos (by omega) (by omega))

private theorem split_den {i N : ℕ} (hi : i ∈ Finset.range N) :
    rden N = (i+1)*(i+2)*(∏ j ∈ Finset.range N, if i=j then 1 else (j+1)*(j+2)) := by
  unfold rden
  rw [← Finset.mul_prod_erase _ _ hi, ← Finset.mul_prod_erase _ (fun j => if i=j then 1 else (j+1)*(j+2)) hi]
  simp only [ite_true,one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [Ne.symm (Finset.mem_erase.mp hj).1]

private theorem energy_sum (g : ℕ → ℕ) (N : ℕ) :
    energy g N = ∑ i ∈ Finset.range N, (g (i+1) : ℚ)^2 / ((i+1 : ℕ) * ((i+2 : ℕ) : ℚ)) := by
  induction N with
  | zero => simp [energy]
  | succ N ih => rw [energy, Finset.sum_range_succ, ih]

theorem clear_denominators (g : ℕ → ℕ) (N : ℕ) :
    (rnum g N : ℚ) = energy g N * rden N := by
  rw [energy_sum,Finset.sum_mul]
  unfold rnum
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [split_den hi]
  push_cast
  field_simp

def residueWitness (tar : Target) (m k h u w d : ℕ) : Witness where
  err := errorValue tar m k h u w (d+1)
  B := budgetValue k h u w (d+1)
  D := d+1
  d_pos := by omega
  bounded := fun n => error_bound tar m k h u w _ _

private theorem read_num_call {ctx} (tar : Target) (m k h u w d n : E ctx) (e) :
    denote (call (numerator tar) [m,k,h,u,w,d,n]) e =
      rnum (errorValue tar (denote m e) (denote k e) (denote h e) (denote u e) (denote w e)
        (denote d e)) (denote n e) := by rw [read_call,read_num]; rfl

private theorem read_budget_call {ctx} (k h u w d : E ctx) (e) :
    denote (call budget [k,h,u,w,d]) e =
      budgetValue (denote k e) (denote h e) (denote u e) (denote w e) (denote d e) := by
  rw [read_call,read_budget]; rfl

private theorem read_den_call {ctx} (n : E ctx) (e) :
    denote (call denominator [n]) e = rden (denote n e) := by rw [read_call, read_den]; rfl

private theorem test_good (g : ℕ → ℕ) (d t n : ℕ) :
    t*rnum g n ≤ d^2*rden n ↔ (t : ℚ)*energy g n ≤ (d : ℚ)^2 := by
  rw [← Nat.cast_le (α := ℚ)]
  push_cast
  rw [clear_denominators, ← mul_assoc]
  exact mul_le_mul_iff_left₀ (by exact_mod_cast rden_pos n)

private theorem test_cert (g : ℕ → ℕ) (b d t n : ℕ) :
    t*((n+1)*rnum g n + b^2*rden n) ≤ d^2*(n+1)*rden n ↔
      (t : ℚ)*(energy g n + (b : ℚ)^2 / ((n+1 : ℕ) : ℚ)) ≤ (d : ℚ)^2 := by
  rw [← Nat.cast_le (α := ℚ)]
  push_cast
  rw [clear_denominators]
  have hn : (0 : ℚ) < n + 1 := by positivity
  have hd : (0 : ℚ) < rden n := by exact_mod_cast rden_pos n
  calc
    _ ↔ (t : ℚ)*(((n : ℚ)+1)*energy g n + (b : ℚ)^2)*rden n ≤ (d : ℚ)^2*(n+1)*rden n := by ring_nf
    _ ↔ (t : ℚ)*(((n : ℚ)+1)*energy g n + (b : ℚ)^2) ≤ (d : ℚ)^2*(n+1) := mul_le_mul_iff_left₀ hd
    _ ↔ _ := by field_simp

private theorem prefix_atom {ctx} (tar : Target) (m k h u w d t n : E ctx) (e) :
    denote (excess tar false m k h u w d t n) e = 0 ↔
    (denote t e : ℚ)*energy (errorValue tar (denote m e) (denote k e) (denote h e) (denote u e)
      (denote w e) (denote d e)) (denote n e) ≤ (denote d e : ℚ)^2 := by
  simp only [excess,Bool.false_eq_true,if_false,minus,times,power,read_num_call,read_den_call,Nat.sub_eq_zero_iff_le]
  exact test_good _ _ _ _

private theorem cert_atom {ctx} (tar : Target) (m k h u w d t n : E ctx) (e) :
    denote (excess tar true m k h u w d t n) e = 0 ↔
    (denote t e : ℚ)*(energy (errorValue tar (denote m e) (denote k e) (denote h e) (denote u e)
      (denote w e) (denote d e)) (denote n e) +
        (budgetValue (denote k e) (denote h e) (denote u e) (denote w e) (denote d e) : ℚ)^2 /
         ((denote n e + 1 : ℕ) : ℚ)) ≤ (denote d e : ℚ)^2 := by
  simp only [excess,if_true,minus,plus,times,power,read_num_call,read_den_call,read_budget_call,
    Nat.sub_eq_zero_iff_le]
  exact test_cert _ _ _ _ _

open RiemannIPRA in
private theorem read_atom {ctx} (a : E ctx) (e) :
    naturalTerms.Holds (zeroTest a) e ↔ denote a e = 0 := by
  change value (program ctx a) e = 0 ↔ _
  rw [value_program]

open RiemannIPRA in
private theorem read_all {ctx} (n : String) (A : SentenceAt (n::ctx)) (e) :
    naturalTerms.Holds (allN n A) e ↔ ∀ x, naturalTerms.Holds A (Fin.cases x e) := Iff.rfl

open RiemannIPRA in
private theorem read_ex {ctx} (n : String) (A : SentenceAt (n::ctx)) (e) :
    naturalTerms.Holds (exN n A) e ↔ ∃ x, naturalTerms.Holds A (Fin.cases x e) := Iff.rfl

open RiemannIPRA in
theorem reading_prefix (tar : Target) :
    naturalTerms.Holds (sentence tar .prefixes) Fin.elim0 ↔
    ∀ m t : ℕ, ∃ k h u w d, ∀ N, (residueWitness tar (m+1) k h u w d).good (t+1) N := by
  simp only [sentence,read_all,read_ex,read_atom,prefix_atom,plus]
  rfl

open RiemannIPRA in
theorem reading_cert (tar : Target) :
    naturalTerms.Holds (sentence tar .certificate) Fin.elim0 ↔
    ∀ m t : ℕ, ∃ k h u w d J, (residueWitness tar (m+1) k h u w d).cert (t+1) J := by
  simp only [sentence,read_all,read_ex,read_atom,cert_atom,plus]
  rfl

open RiemannIPRA in
theorem reading_fixed (tar : Target) :
    naturalTerms.Holds (sentence tar .fixedCutoff) Fin.elim0 ↔
    ∀ m t : ℕ, ∃ k h u w d, (residueWitness tar (m+1) k h u w d).cert (t+1)
      ((residueWitness tar (m+1) k h u w d).cutoff (t+1)) := by
  simp only [sentence,read_all,read_ex,read_atom,cert_atom,read_budget_call,plus,times,power]
  rfl

open RiemannIPRA in
theorem closed_fixed_iff_prefix (tar : Target) :
    naturalTerms.Holds (sentence tar .fixedCutoff) Fin.elim0 ↔
    naturalTerms.Holds (sentence tar .prefixes) Fin.elim0 := by
  rw [reading_fixed,reading_prefix]
  constructor
  · intro h m t
    obtain ⟨k,s,u,w,d,hc⟩ := h m t
    exact ⟨k,s,u,w,d,cert_covers _ hc⟩
  · intro h m t
    obtain ⟨k,s,u,w,d,hc⟩ := h m (2*t+1)
    refine ⟨k,s,u,w,d,fixed_of_prefix _ _ ?_⟩
    rwa [show 2*(t+1) = 2*t+1+1 by omega]

open RiemannIPRA in
theorem closed_cert_iff_prefix (tar : Target) :
    naturalTerms.Holds (sentence tar .certificate) Fin.elim0 ↔
    naturalTerms.Holds (sentence tar .prefixes) Fin.elim0 := by
  constructor
  · rw [reading_cert,reading_prefix]
    intro h m t
    obtain ⟨k,s,u,w,d,J,hc⟩ := h m t
    exact ⟨k,s,u,w,d,cert_covers _ hc⟩
  · intro h
    have hh := (reading_fixed tar).mp ((closed_fixed_iff_prefix tar).mpr h)
    apply (reading_cert tar).mpr
    intro m t
    obtain ⟨k,s,u,w,d,hc⟩ := hh m t
    exact ⟨k,s,u,w,d,_,hc⟩

/-- Mixed-radix identity used to transport a rational approximation by dilation. -/
theorem dilation_row (n m k : ℕ) :
    (n % (m*k) : ℕ) = n%m + m*((n/m)%k) := Nat.mod_mul

end Reading

end ResidueSpace
