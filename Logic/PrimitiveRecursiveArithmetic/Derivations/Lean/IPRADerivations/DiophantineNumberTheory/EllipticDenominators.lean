import IPRADerivations.DiophantineNumberTheory.SignedLine

/-!
# Square and cube denominators on an elliptic curve

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Theorem `thm:denominators` ("Square and cube
denominators"): "Every rational affine point on `E_{A,B}` has a unique expression `x = a/d²`, `y = b/d³`, `d > 0`,
`gcd(a, d) = gcd(b, d) = 1` ... Write `x = a/q` and `y = c/e` in reduced form ... `T = a³ + A a q² + B q³`. Then
`y² = T/q³`. Since `T ≡ a³ (mod q)` and `gcd(a, q) = 1`, we have `gcd(T, q) = 1`, hence `gcd(T, q³) = 1` ...
Uniqueness of reduced fractions therefore gives `e² = q³`, `c² = T` ... constructs `d > 0` with `q = d²`, `e = d³`."

The arithmetic core, with `a`, `c` the absolute values of the numerators and the congruence `T ≡ a³ (mod q)`
given as `T + u q = a³ + w q`:

* `gcd_zero_right`, `coprime_symm`: `gcd(a, 0) = a`, and coprimality is symmetric;
* `coprime_T`: `T ≡ a³ (mod q)` and `gcd(a, q) = 1` give `gcd(q, T) = 1`;
* `coprime_pow`: `gcd(q, T) = 1` gives `gcd(q³, T) = 1`, and `gcd(c, e) = 1` gives `gcd(e², c²) = 1`;
* `sq_cube`: `e² = q³` with `q ≥ 1` gives `q = d²`, `e = d³` for `d = ⌊e/q⌋`;
* `denominators`: `c² q³ = T e²` (i.e. `y² = T/q³`) gives `c² = T`, `q = d²`, `e = d³`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.EllipticDenominators

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' dvd_of_eq' dvd_sub' dvd_add' dvd_mul' gcd_dvd'
  gcd_greatest' eq_one_of_dvd_one gcd_comm_one coprime_mul dvd_of_sq_dvd_sq dvd_self' pos_of_eq_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.ProjectiveNormalize (norm_unique)
open LeanProofs.IPRA.DiophantineNumberTheory.SignedLine (one_of_gcd_zero)
open LeanProofs.IPRA.DiophantineNumberTheory.GcdNormalize (congrGcd)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem gcd_zero_right (a : PTm k) : Γ ⊢[PRAAx] gcd a zero ≐ a :=
  (Prf.andE₁ (e_step_zero (ey_zero (Γ := Γ) a (zero : PTm k)))).eqTrans (ex_zero a zero)

theorem one_pos : Γ ⊢[PRAAx] (one : PTm k) ≐ succ (pred one) := congrSucc (pred_succ _).eqSymm

/-- Coprimality is symmetric (for a positive first argument). -/
theorem coprime_symm {a b : PTm k} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (h : Γ ⊢[PRAAx] gcd a b ≐ one) :
    Γ ⊢[PRAAx] gcd b a ≐ one := by
  refine .orE (zero_or_succ b) ?_ (gcd_comm_one Prf.hyp0 h.wk)
  have hb : ((b ≐ zero) :: Γ) ⊢[PRAAx] b ≐ zero := Prf.hyp0
  have a1 : ((b ≐ zero) :: Γ) ⊢[PRAAx] a ≐ one :=
    (gcd_zero_right a).eqSymm.eqTrans ((congrGcd (.eqRefl _) hb.eqSymm).eqTrans h.wk)
  have g : ((b ≐ zero) :: Γ) ⊢[PRAAx] gcd b a ≐ gcd zero one := congrGcd hb a1
  have gp := LeanProofs.IPRA.AnalyticNumberTheory.Order.gcd_pos_right (Γ := (b ≐ zero) :: Γ) (a := zero)
    (one_pos (Γ := (b ≐ zero) :: Γ))
  have gd := Prf.andE₂ (gcd_dvd_at gp)
  exact g.eqTrans (eq_one_of_dvd_one gp gd)

/-- `T ≡ a³ (mod q)` and `gcd(a, q) = 1` give `gcd(q, T) = 1`. -/
theorem coprime_T {a q T u w : PTm k} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (haq : Γ ⊢[PRAAx] gcd a q ≐ one)
    (hT : Γ ⊢[PRAAx] T + u * q ≐ a * a * a + w * q) : Γ ⊢[PRAAx] gcd q T ≐ one := by
  have hqa := gcd_comm_one hq haq
  have c2 := coprime_mul hq hqa hqa
  have c3 := coprime_mul hq c2 hqa
  have hg := gcd_pos (B := T) hq
  have gd := gcd_dvd' (b := T) hq
  have d1 : Γ ⊢[PRAAx] dvd (gcd q T) (T + u * q) :=
    dvd_add' hg (Prf.andE₂ gd) (dvd_congr (mul_comm _ _) (dvd_mul' hg u (Prf.andE₁ gd)))
  have d2 : Γ ⊢[PRAAx] dvd (gcd q T) (a * a * a + w * q) := dvd_congr hT d1
  have d3 := dvd_sub' hg d2 (dvd_congr (mul_comm _ _) (dvd_mul' hg w (Prf.andE₁ gd)))
  exact eq_one_of_dvd_one hg (dvd_congr c3 (gcd_greatest' hg (Prf.andE₁ gd) d3))

/-- `gcd(q, T) = 1` gives `gcd(q³, T) = 1`. -/
theorem coprime_cube {q T : PTm k} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (h : Γ ⊢[PRAAx] gcd q T ≐ one) :
    Γ ⊢[PRAAx] gcd (q * q * q) T ≐ one := by
  refine .orE (zero_or_succ T) ?_ ?_
  · have hT : ((T ≐ zero) :: Γ) ⊢[PRAAx] T ≐ zero := Prf.hyp0
    have q1 : ((T ≐ zero) :: Γ) ⊢[PRAAx] q ≐ one :=
      (gcd_zero_right q).eqSymm.eqTrans ((congrGcd (.eqRefl _) hT.eqSymm).eqTrans h.wk)
    have e := natEq q1
    have q3 : ((T ≐ zero) :: Γ) ⊢[PRAAx] q * q * q ≐ one := by
      apply deriveNat; ipra_simps; linear_combination (𝔞 q * 𝔞 q + 𝔞 q + 1) * e
    exact (congrGcd q3 hT).eqTrans (gcd_zero_right one)
  · have hT : ((T ≐ succ (pred T)) :: Γ) ⊢[PRAAx] T ≐ succ (pred T) := Prf.hyp0
    have tq := gcd_comm_one hT h.wk
    have t2 := coprime_mul hT tq tq
    have t3 := coprime_mul hT t2 tq
    exact gcd_comm_one (pos_mul (pos_mul hq.wk hq.wk) hq.wk) t3

/-- `gcd(c, e) = 1` gives `gcd(e², c²) = 1`. -/
theorem coprime_sq {c e : PTm k} (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) (h : Γ ⊢[PRAAx] gcd c e ≐ one) :
    Γ ⊢[PRAAx] gcd (e * e) (c * c) ≐ one := by
  have ec := gcd_comm_one he h
  refine .orE (zero_or_succ c) ?_ ?_
  · have hc : ((c ≐ zero) :: Γ) ⊢[PRAAx] c ≐ zero := Prf.hyp0
    have e1 : ((c ≐ zero) :: Γ) ⊢[PRAAx] e ≐ one :=
      one_of_gcd_zero ((congrGcd hc.eqSymm (.eqRefl _)).eqTrans h.wk)
    have x1 := natEq e1; have x0 := natEq hc
    have ee : ((c ≐ zero) :: Γ) ⊢[PRAAx] e * e ≐ one := by
      apply deriveNat; ipra_simps; linear_combination (𝔞 e + 1) * x1
    have cc : ((c ≐ zero) :: Γ) ⊢[PRAAx] c * c ≐ zero := by
      apply deriveNat; ipra_simps; linear_combination 𝔞 c * x0
    exact (congrGcd ee cc).eqTrans (gcd_zero_right one)
  · have hc : ((c ≐ succ (pred c)) :: Γ) ⊢[PRAAx] c ≐ succ (pred c) := Prf.hyp0
    have e2 := coprime_mul (he.wk : ((c ≐ succ (pred c)) :: Γ) ⊢[PRAAx] _) ec.wk ec.wk
    have hcc := pos_mul hc hc
    have c1 := gcd_comm_one hcc e2
    have c2 := coprime_mul hcc c1 c1
    exact gcd_comm_one (pos_mul he.wk he.wk) c2

/-- `e² = q³` with `q ≥ 1` gives `q = d²` and `e = d³` for `d = ⌊e/q⌋`. -/
theorem sq_cube {q e : PTm k} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (h : Γ ⊢[PRAAx] e * e ≐ q * q * q) :
    Γ ⊢[PRAAx] (q ≐ quo e q * quo e q) ⋏ (e ≐ quo e q * quo e q * quo e q) := by
  have hq3 := pos_mul (pos_mul hq hq) hq
  have he : Γ ⊢[PRAAx] e ≐ succ (pred e) := by
    refine .orE (zero_or_succ e) ?_ Prf.hyp0
    have e0 := natEq (Prf.hyp0 : ((e ≐ zero) :: Γ) ⊢[PRAAx] e ≐ zero)
    have hh := natEq (h.wk : ((e ≐ zero) :: Γ) ⊢[PRAAx] _)
    have z : ((e ≐ zero) :: Γ) ⊢[PRAAx] q * q * q ≐ zero := by
      apply deriveNat; ipra_simps; linear_combination -hh + 𝔞 e * e0
    exact succ_ne_zero' _ (hq3.wk.eqSymm.eqTrans z)
  have hqq := pos_mul hq hq
  have dq : Γ ⊢[PRAAx] dvd (q * q) (e * e) := dvd_of_eq' hqq (w := q) h
  have dqe := dvd_of_sq_dvd_sq hq he dq
  have ee := eq_of_dvd' hq dqe
  have x := natEq ee; have hh := natEq h
  have dd : Γ ⊢[PRAAx] quo e q * quo e q ≐ q := by
    refine mul_cancel hqq ?_
    apply deriveNat; ipra_simps
    linear_combination hh - (𝔞 e + 𝔞 q * 𝔞 (quo e q)) * x
  have y := natEq dd
  refine .andI dd.eqSymm ?_
  apply deriveNat; ipra_simps
  linear_combination x - 𝔞 (quo e q) * y

/-- `thm:denominators`, the arithmetic core: `y² = T/q³` in lowest terms (`c² q³ = T e²`, `gcd(c, e) = 1`),
with `T ≡ a³ (mod q)` and `gcd(a, q) = 1`, gives `c² = T`, `q = d²`, `e = d³` for `d = ⌊e/q⌋`. -/
theorem denominators {a q T u w c e : PTm k} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (he : Γ ⊢[PRAAx] e ≐ succ (pred e))
    (haq : Γ ⊢[PRAAx] gcd a q ≐ one) (hT : Γ ⊢[PRAAx] T + u * q ≐ a * a * a + w * q)
    (hce : Γ ⊢[PRAAx] gcd c e ≐ one) (hy : Γ ⊢[PRAAx] c * c * (q * q * q) ≐ T * (e * e)) :
    Γ ⊢[PRAAx] (c * c ≐ T) ⋏ ((q ≐ quo e q * quo e q) ⋏ (e ≐ quo e q * quo e q * quo e q)) := by
  have g1 := coprime_sq he hce
  have g2 := coprime_cube hq (coprime_T hq haq hT)
  have x := natEq hy
  have u1 := norm_unique (pos_mul he he) (pos_mul (pos_mul hq hq) hq) g1 g2
    (by apply deriveNat; ipra_simps; linear_combination -x)
  exact .andI (Prf.andE₂ u1) (sq_cube hq (Prf.andE₁ u1))

end LeanProofs.IPRA.DiophantineNumberTheory.EllipticDenominators
