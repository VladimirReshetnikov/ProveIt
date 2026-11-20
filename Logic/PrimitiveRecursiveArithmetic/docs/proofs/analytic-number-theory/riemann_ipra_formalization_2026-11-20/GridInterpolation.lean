import DivisorMatrices
import DiscreteForms
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Finite arithmetic for sparse samples of a one-sided dyadic discrepancy. -/
namespace RiemannIPRA.GridInterpolation

def root : Nat → Nat
  | 0 => 10
  | n+1 => root n + (1+(n+1).log2)

def grid (j : Nat) := (root j)^2

private theorem logMono {a b : Nat} (h : a ≤ b) : a.log2 ≤ b.log2 := by
  cases a with
  | zero => simp
  | succ a =>
    exact (Nat.le_log2 (by omega)).2 ((Nat.log2_self_le (Nat.succ_ne_zero a)).trans h)

theorem root_mono : Monotone root := by
  apply monotone_nat_of_le_succ
  intro n
  simp [root]

theorem root_span (j h : Nat) :
    root (j+h) ≤ root j + h*(1+(j+h).log2) := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hl : (j+h).log2 ≤ (j+h+1).log2 := logMono (by omega)
    have hm := Nat.mul_le_mul_left h (Nat.add_le_add_left hl 1)
    rw [Nat.add_succ, root, Nat.succ_mul]
    simp only [Nat.succ_eq_add_one] at *
    omega

theorem square_span (j h : Nat) :
    grid (j+h) ≤ grid j + 2*root (j+h)*(h*(1+(j+h).log2)) := by
  have he := root_span j h
  have hle : root j ≤ root (j+h) := root_mono (by omega)
  have hgap : root (j+h) - root j ≤ h*(1+(j+h).log2) := by omega
  have hfactor : root (j+h) + root j ≤ 2*root (j+h) := by omega
  have hd := Nat.mul_le_mul hgap hfactor
  have hsum : root (j+h) - root j + root j = root (j+h) := Nat.sub_add_cancel hle
  unfold grid
  nlinarith only [hd, hsum, congrArg (fun a => a * (root (j+h) + root j)) hsum]

/-- Packed four-prime clock; the return argument is the sample index plus one. -/
def mass (a b c d : Nat) := 2^a*3^b*5^c*7^d
def returnTime (a b c d h : Nat) := mass a b c d*(1+210*h)
def decode (n : Nat) : Nat × Nat × Nat × Nat :=
  (n.factorization 2, n.factorization 3, n.factorization 5, n.factorization 7)

theorem spaced (a b c d h : Nat) :
    returnTime a b c d (h+1) = returnTime a b c d h + 210*mass a b c d := by
  unfold returnTime
  ring

private theorem unitFactor (p h : Nat) (hp : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7) :
    (1+210*h).factorization p = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  rcases hp with rfl | rfl | rfl | rfl <;> omega

theorem decode_return (a b c d h : Nat) : decode (returnTime a b c d h) = (a,b,c,d) := by
  have p2 : Nat.Prime 2 := by decide
  have p3 : Nat.Prime 3 := by decide
  have p5 : Nat.Prime 5 := by decide
  have p7 : Nat.Prime 7 := by decide
  have h2 : 2^a≠0 := pow_ne_zero _ (by decide)
  have h3 : 3^b≠0 := pow_ne_zero _ (by decide)
  have h5 : 5^c≠0 := pow_ne_zero _ (by decide)
  have h7 : 7^d≠0 := pow_ne_zero _ (by decide)
  have hu : 1+210*h≠0 := by omega
  unfold decode returnTime mass
  simp only [Nat.factorization_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h3) h5) h7) hu,
    Nat.factorization_mul (mul_ne_zero (mul_ne_zero h2 h3) h5) h7,
    Nat.factorization_mul (mul_ne_zero h2 h3) h5, Nat.factorization_mul h2 h3, Finsupp.add_apply,
    Nat.Prime.factorization_pow p2, Nat.Prime.factorization_pow p3, Nat.Prime.factorization_pow p5,
    Nat.Prime.factorization_pow p7, Finsupp.single_apply, unitFactor 2 h (by decide),
    unitFactor 3 h (by decide), unitFactor 5 h (by decide), unitFactor 7 h (by decide)]
  norm_num

open LeanProofs.ConciseIPRA PacketLanguage Discrete

private theorem denLe {ctx} (a b : E ctx) (e) :
    denote (leB a b) e = (if denote a e ≤ denote b e then 1 else 0) := by
  change value isZeroR _ = _
  rw [value_isZeroR]
  change (if denote (a-b) e = 0 then 1 else 0) = _
  simp [Discrete.minus, Nat.sub_eq_zero_iff_le]

private theorem denEq {ctx} (a b : E ctx) (e) :
    denote (eqB a b) e = (if denote a e = denote b e then 1 else 0) := by
  simp only [eqB,Discrete.times,denLe]
  split <;> split <;> split <;> first | rfl | omega

private theorem scan (t n : Nat) :
    overRange 0 (fun j a => max a (if j ≤ t then j else 0)) (n+1) = min n t := by
  induction n with
  | zero => simp [overRange]
  | succ n ih =>
    change max (overRange 0 (fun j a => max a (if j ≤ t then j else 0)) (n+1))
      (if n+1 ≤ t then n+1 else 0) = _
    rw [ih]
    split <;> omega

private theorem denMax {ctx} (s : String) (n : E ctx) (g : E (s::ctx)) (e) :
    denote (maxTo s n g) e =
      overRange 0 (fun i a => max a (denote g (Fin.cases i e))) (denote n e) := rfl

theorem valuation_reading (p n : Nat) (hp : Nat.Prime p) (hn : n ≠ 0) :
    value DivisorMatrices.valuation (Fin.cases p (fun _ => n)) = n.factorization p := by
  unfold DivisorMatrices.valuation
  rw [value_program]
  simp only [denMax,Discrete.plus,Discrete.times,denEq,denote_modE,Discrete.power]
  change overRange 0 (fun j a => max a (j * (if n % p^j = 0 then 1 else 0))) (n+1) = _
  have he : (fun j : Nat => j * (if n % p^j = 0 then 1 else 0)) =
      (fun j => if j ≤ n.factorization p then j else 0) := by
    funext j
    have iff := (Nat.dvd_iff_mod_eq_zero (n := n) (m := p^j)).symm.trans
      (hp.pow_dvd_iff_le_factorization hn)
    by_cases hj : j ≤ n.factorization p
    · simp [hj,iff.mpr hj]
    · have hnmod : n % p^j ≠ 0 := fun H => hj (iff.mp H)
      simp [hj,hnmod]
  simp_rw [congrFun he]
  rw [scan,Nat.min_eq_right]
  rw [n.factorization_def hp]
  exact Nat.padicValNat_le_self n

def clock (n : Nat) : Nat × Nat × Nat × Nat :=
  let v := fun p => value DivisorMatrices.valuation (Fin.cases p (fun _ => n))
  (v 2, v 3, v 5, v 7)

theorem clock_return (a b c d h : Nat) : clock (returnTime a b c d h) = (a,b,c,d) := by
  have hn : returnTime a b c d h ≠ 0 := by unfold returnTime mass; positivity
  unfold clock
  simp only [valuation_reading 2 _ (by decide) hn, valuation_reading 3 _ (by decide) hn,
    valuation_reading 5 _ (by decide) hn, valuation_reading 7 _ (by decide) hn]
  exact decode_return _ _ _ _ _

theorem increment_span (B : Nat → ℤ) (i h : Nat) (K : ℤ)
    (step : ∀ j < h, B (i+j+1)-B (i+j) ≤ K) : B (i+h)-B i ≤ (h:ℤ)*K := by
  induction h with
  | zero => simp
  | succ h ih =>
    have a := step h (by omega)
    have b := ih (fun j hj => step j (by omega))
    rw [Nat.add_succ]
    push_cast
    linarith

/-- For n ≤ x=n+h, the upper comparison only needs a jump bound at 2n
and monotonicity of B. All differences in this theorem are signed. -/
theorem interpolate_upper (B : Nat → ℤ) (n h : Nat) (K : ℤ)
    (mono : B n ≤ B (n+h)) (bound : ∀ j < 2*h, B (2*n+j+1)-B (2*n+j) ≤ K) :
    B (2*(n+h))-2*B (n+h) ≤ B (2*n)-2*B n+(2*(h:ℤ))*K := by
  have hb := increment_span B (2*n) (2*h) K bound
  rw [Nat.mul_add]
  push_cast at hb
  linarith

end RiemannIPRA.GridInterpolation
