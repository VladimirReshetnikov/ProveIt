import IPRADerivations.Foundations.MasterCertificate
import IPRADerivations.Foundations.QuantitativeIdentities
import IPRADerivations.Foundations.TraceInvariant
import IPRADerivations.Core.IntOrder
import IPRADerivations.Core.IntCancel
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# Actual dyadic bisection for a fixed-degree rational polynomial

Packet `foundations/fiber_ipra_2026-11-16`, Section 7.7, certified bisection.
The degree is an external fixed natural number; every signed coefficient and
every initial bracket parameter is internal data. Coefficients are decoded
from an actual finite sequence code. Their common rational denominator `C`
is positive. At a sample `a/D`, the exact polynomial value is represented by
the homogeneous signed numerator over `C * D^degree`.

The dyadic update evaluates the actual midpoint polynomial numerator and
uses its reflected exact sign. A zero midpoint takes the nonpositive branch.
Neither a correct trace nor a preservation theorem is an input.

The public endpoints give exact finite rational brackets, arbitrary internal
window nesting and rational-zero uniqueness under a positive computed factor.
Completed-name existence/uniqueness and uniform interval-guard production are
further interface adapters. A supplied finite coefficient list connects to
`coefficient` through the actual in-range sequence decoding theorem.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.PolynomialBisection

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.QuantitativeIdentities (zpow toZ_zpow)
open LeanProofs.IPRA.Foundations.BoundedReflection
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

namespace RingModel

variable {R : Type*} [CommRing R]

def H : ℕ → (ℕ → R) → R → R → R
  | 0, c, _, _ => c 0
  | k + 1, c, a, D => D * H k c a D + c (k + 1) * a ^ (k + 1)

private theorem homogeneous (k : ℕ) (c : ℕ → R) (t a D : R) :
    H k c (t * a) (t * D) = t ^ k * H k c a D := by
  induction k with
  | zero => simp [H]
  | succ k ih =>
    simp only [H, ih, mul_pow, pow_succ]
    ring

def G : ℕ → R → R → R
  | 0, _, _ => 0
  | k + 1, u, v => u ^ k + v * G k u v

private theorem power_difference (k : ℕ) (u v : R) :
    (u - v) * G k u v = u ^ k - v ^ k := by
  induction k with
  | zero => simp [G]
  | succ k ih =>
    simp only [G, pow_succ]
    linear_combination v * ih

def Q : ℕ → (ℕ → R) → R → R → R → R → R
  | 0, _, _, _, _, _ => 0
  | k + 1, c, a, da, b, db =>
      da * db * Q k c a da b db + c (k + 1) * G (k + 1) (b * da) (a * db)

private theorem polynomial_difference (k : ℕ) (c : ℕ → R) (a da b db : R) :
    da ^ k * H k c b db - db ^ k * H k c a da =
      (b * da - a * db) * Q k c a da b db := by
  induction k with
  | zero => simp [H, Q]
  | succ k ih =>
    have powers := power_difference (R := R) (k + 1) (b * da) (a * db)
    simp only [H, Q, mul_pow, pow_succ] at powers ⊢
    linear_combination (da * db) * ih - c (k + 1) * powers

end RingModel

/-- Signed numerator of coefficient `i`, decoded from the internal coefficient code. -/
def coefficient (code : PTm n) (i : ℕ) : ZT n :=
  ⟨fstT (entry code (num i)), sndT (entry code (num i))⟩

/-- A fixed-degree power is itself a fixed primitive recursive term. -/
def naturalPower (a : PTm n) : ℕ → PTm n
  | 0 => one
  | k + 1 => naturalPower a k * a

/-- Exact numerator for `Σ c_i (a/D)^i`, with denominator `C * D^degree`. -/
def evaluate : ℕ → PTm n → ZT n → PTm n → ZT n
  | 0, code, _, _ => coefficient code 0
  | k + 1, code, a, D =>
      ZT.ofNat D * evaluate k code a D + coefficient code (k + 1) * zpow a (k + 1)

@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (code : PTm n) (i : ℕ) :
    (coefficient code i).subst σ = coefficient (Syn.subst σ code) i := by
  simp [coefficient, ZT.subst]

@[simp] theorem subst_naturalPower {m : ℕ} (σ : Fin n → PTm m) (a : PTm n) (k : ℕ) :
    Syn.subst σ (naturalPower a k) = naturalPower (Syn.subst σ a) k := by
  induction k with
  | zero => simp [naturalPower, one]
  | succ k ih => simp only [naturalPower, PTm.subst_mul, ih]

@[simp] private theorem subst_zpow {m : ℕ} (σ : Fin n → PTm m) (a : ZT n) (k : ℕ) :
    (zpow a k).subst σ = zpow (a.subst σ) k := by
  induction k with
  | zero => simp [zpow]
  | succ k ih => simp only [zpow, ZT.subst_mul, ih]

@[simp] theorem subst_evaluate {m : ℕ} (σ : Fin n → PTm m)
    (degree : ℕ) (code : PTm n) (a : ZT n) (D : PTm n) :
    (evaluate degree code a D).subst σ =
      evaluate degree (Syn.subst σ code) (a.subst σ) (Syn.subst σ D) := by
  induction degree with
  | zero => simp only [evaluate, subst_coefficient]
  | succ k ih => simp only [evaluate, ZT.subst_add, ZT.subst_mul, ZT.subst_ofNat,
      subst_coefficient, subst_zpow, ih]

@[simp] private theorem toZ_naturalPower (a : PTm n) (k : ℕ) :
    Groth.ι (Q.mk Γ (naturalPower a k)) = Groth.ι (Q.mk Γ a) ^ k := by
  induction k with
  | zero => simp [naturalPower, Q.mk_one]
  | succ k ih => simp only [naturalPower, Q.mk_mul, map_mul, ih, pow_succ]

private theorem toZ_evaluate (degree : ℕ) (code : PTm n) (a : ZT n) (D : PTm n) :
    ZT.toZ Γ (evaluate degree code a D) =
      RingModel.H degree (fun i => ZT.toZ Γ (coefficient code i))
        (ZT.toZ Γ a) (Groth.ι (Q.mk Γ D)) := by
  induction degree with
  | zero => rfl
  | succ k ih => simp only [evaluate, RingModel.H, ZT.toZ_add, ZT.toZ_mul,
      ZT.toZ_ofNat, toZ_zpow, ih]

/-- Exact homogeneous scaling, as an ordinary object identity. -/
theorem evaluate_scale (degree : ℕ) (code : PTm n) (a : ZT n) (D t : PTm n) :
    Γ ⊢[PRAAx] ZT.eq
      (evaluate degree code (ZT.ofNat t * a) (t * D))
      (ZT.ofNat (naturalPower t degree) * evaluate degree code a D) := by
  apply ZT.derive
  simp only [toZ_evaluate, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul, toZ_naturalPower]
  exact RingModel.homogeneous degree _ _ _ _

theorem naturalPower_positive (a : PTm n) (degree : ℕ) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] le one (naturalPower a degree) := by
  induction degree with
  | zero => exact le_refl one
  | succ k ih => exact le_congr (one_mul one) (.eqRefl _) (le_mul_mono ih ha)

/-- Encode a signed value as an actual natural-number pair. -/
def pack (a : ZT n) : PTm n := pairT a.pos a.neg
def unpack (code : PTm n) : ZT n := ⟨fstT code, sndT code⟩

/-- Bracket state contains two signed numerators and their common denominator. -/
def state (L R : ZT n) (D : PTm n) : PTm n := pairT (pack L) (pairT (pack R) D)
def left (s : PTm n) : ZT n := unpack (fstT s)
def right (s : PTm n) : ZT n := unpack (fstT (sndT s))
def denominator (s : PTm n) : PTm n := sndT (sndT s)

@[simp] theorem subst_pack {m : ℕ} (σ : Fin n → PTm m) (a : ZT n) :
    Syn.subst σ (pack a) = pack (a.subst σ) := by simp [pack, ZT.subst]

@[simp] theorem subst_unpack {m : ℕ} (σ : Fin n → PTm m) (s : PTm n) :
    (unpack s).subst σ = unpack (Syn.subst σ s) := by simp [unpack, ZT.subst]

@[simp] theorem subst_state {m : ℕ} (σ : Fin n → PTm m) (L R : ZT n) (D : PTm n) :
    Syn.subst σ (state L R D) = state (L.subst σ) (R.subst σ) (Syn.subst σ D) := by
  simp only [state, subst_pairT, subst_pack]

@[simp] theorem subst_left {m : ℕ} (σ : Fin n → PTm m) (s : PTm n) :
    (left s).subst σ = left (Syn.subst σ s) := by simp only [left, subst_unpack, subst_fstT]

@[simp] theorem subst_right {m : ℕ} (σ : Fin n → PTm m) (s : PTm n) :
    (right s).subst σ = right (Syn.subst σ s) := by
  simp only [right, subst_unpack, subst_fstT, subst_sndT]

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (s : PTm n) :
    Syn.subst σ (denominator s) = denominator (Syn.subst σ s) := by
  simp only [denominator, subst_sndT]

private theorem unpack_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    ZT.toZ Γ (unpack a) = ZT.toZ Γ (unpack b) := by
  simp only [unpack, ZT.toZ]
  rw [natEq (congrFst h), natEq (congrSnd h)]

private theorem unpack_pack (a : ZT n) : ZT.toZ Γ (unpack (pack a)) = ZT.toZ Γ a := by
  simp only [pack, unpack, ZT.toZ]
  rw [natEq (fst_pair (Γ := Γ) a.pos a.neg), natEq (snd_pair (Γ := Γ) a.pos a.neg)]

private theorem left_state_value (L R : ZT n) (D : PTm n) :
    ZT.toZ Γ (left (state L R D)) = ZT.toZ Γ L :=
  (unpack_congr (fst_pair (pack L) (pairT (pack R) D))).trans (unpack_pack L)

private theorem right_state_value (L R : ZT n) (D : PTm n) :
    ZT.toZ Γ (right (state L R D)) = ZT.toZ Γ R :=
  (unpack_congr ((congrFst (snd_pair (pack L) (pairT (pack R) D))).eqTrans
    (fst_pair (pack R) D))).trans (unpack_pack R)

theorem denominator_state (L R : ZT n) (D : PTm n) :
    Γ ⊢[PRAAx] denominator (state L R D) ≐ D :=
  (congrSnd (snd_pair (pack L) (pairT (pack R) D))).eqTrans (snd_pair (pack R) D)

theorem left_state (L R : ZT n) (D : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (left (state L R D)) L := ZT.derive (left_state_value L R D)

theorem right_state (L R : ZT n) (D : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (right (state L R D)) R := ZT.derive (right_state_value L R D)

def slack (u v : ZT n) : PTm n :=
  monus (v.pos + u.neg) (u.pos + v.neg)

theorem zle_congr {u u' v v' : ZT n}
    (hu : ZT.toZ Γ u = ZT.toZ Γ u') (hv : ZT.toZ Γ v = ZT.toZ Γ v')
    (h : Γ ⊢[PRAAx] zle u v) : Γ ⊢[PRAAx] zle u' v' := by
  apply zle_of_toZ (slack u v)
  rw [← hu, ← hv]
  exact zle_toZ h

theorem zle_scale (c : PTm n) {u v : ZT n} (h : Γ ⊢[PRAAx] zle u v) :
    Γ ⊢[PRAAx] zle (ZT.ofNat c * u) (ZT.ofNat c * v) := by
  have H := zle_toZ h
  apply zle_of_toZ (c * slack u v)
  simp only [slack, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul]
  linear_combination Groth.ι (Q.mk Γ c) * H

theorem zle_total (u v : ZT n) : Γ ⊢[PRAAx] zle u v ⋎ zle v u :=
  le_total _ _

theorem zle_antisym {u v : ZT n} (h : Γ ⊢[PRAAx] zle u v)
    (h' : Γ ⊢[PRAAx] zle v u) : Γ ⊢[PRAAx] ZT.eq u v :=
  le_antisymm h h'

theorem zle_trans {u v w : ZT n} (h : Γ ⊢[PRAAx] zle u v)
    (h' : Γ ⊢[PRAAx] zle v w) : Γ ⊢[PRAAx] zle u w := by
  have H := zle_toZ h
  have H' := zle_toZ h'
  apply zle_of_toZ (slack u v + slack v w)
  simp only [slack, Q.mk_add, map_add]
  linear_combination H + H'

theorem zle_refl (u : ZT n) : Γ ⊢[PRAAx] zle u u := le_refl _

theorem zle_add {u v u' v' : ZT n} (h : Γ ⊢[PRAAx] zle u v)
    (h' : Γ ⊢[PRAAx] zle u' v') : Γ ⊢[PRAAx] zle (u + u') (v + v') := by
  have H := zle_toZ h
  have H' := zle_toZ h'
  apply zle_of_toZ (slack u v + slack u' v')
  simp only [slack, ZT.toZ_add, Q.mk_add, map_add]
  linear_combination H + H'

private alias cancel_positive := Common.mul_cancel_le

theorem zle_scale_cancel {c : PTm n} {u v : ZT n}
    (hc : Γ ⊢[PRAAx] le one c)
    (h : Γ ⊢[PRAAx] zle (ZT.ofNat c * u) (ZT.ofNat c * v)) :
    Γ ⊢[PRAAx] zle u v := by
  change Γ ⊢[PRAAx] le
    ((c * u.pos + zero * u.neg) + (c * v.neg + zero * v.pos))
    ((c * v.pos + zero * v.neg) + (c * u.neg + zero * u.pos)) at h
  have scaled : Γ ⊢[PRAAx] le (c * (u.pos + v.neg)) (c * (v.pos + u.neg)) :=
    le_congr (by ipra_ring) (by ipra_ring) h
  exact cancel_positive hc scaled

/-- Bit one means that the signed integer is nonpositive. -/
def selector (u : ZT n) : PTm n := eqb (monus u.pos u.neg) zero

theorem selector_cases (u : ZT n) :
    Γ ⊢[PRAAx] selector u ≐ zero ⋎ selector u ≐ one := eqb_cases _ _

theorem selector_one {u : ZT n} (h : Γ ⊢[PRAAx] selector u ≐ one) :
    Γ ⊢[PRAAx] zle u (ZT.natLit 0) := by
  have bound : Γ ⊢[PRAAx] le u.pos u.neg := eq_of_eqb h
  exact le_congr (LeanProofs.IPRA.add_zero u.pos).eqSymm
    (LeanProofs.IPRA.zero_add u.neg).eqSymm bound

theorem selector_zero {u : ZT n} (h : Γ ⊢[PRAAx] selector u ≐ zero) :
    Γ ⊢[PRAAx] zle (ZT.natLit 0) u := by
  refine .orE (le_total u.pos u.neg) ?_ ?_
  · have one : (le u.pos u.neg :: Γ) ⊢[PRAAx] selector u ≐ one := eqb_of_eq Prf.hyp0
    exact one_ne_zero _ (one.eqSymm.eqTrans h.wk)
  · exact le_congr (LeanProofs.IPRA.zero_add u.neg).eqSymm
      (LeanProofs.IPRA.add_zero u.pos).eqSymm Prf.hyp0

theorem nonzero_of_one_le {u : ZT n} (h : Γ ⊢[PRAAx] zle (ZT.ofNat one) u) :
    Γ ⊢[PRAAx] neg (ZT.eq u (ZT.natLit 0)) := by
  refine .impI ?_
  have bound : (ZT.eq u (ZT.natLit 0) :: Γ) ⊢[PRAAx]
      le (one + u.neg) (zero + u.neg) :=
    le_congr (.eqRefl _) Prf.hyp0 h.wk
  exact not_succ_le_self zero _ (le_of_add_le_add_right bound)

theorem positive_factor_cancel {Q K : ZT n}
    (hQ : Γ ⊢[PRAAx] zle (ZT.ofNat one) Q)
    (h : Γ ⊢[PRAAx] ZT.eq (Q * K) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq K (ZT.natLit 0) :=
  zt_mul_cancel_left (nonzero_of_one_le hQ) h

theorem unique_of_factor (x y fx fy Q : ZT n)
    (hFactor : Γ ⊢[PRAAx] ZT.eq (fy - fx) ((y - x) * Q))
    (hx : Γ ⊢[PRAAx] ZT.eq fx (ZT.natLit 0))
    (hy : Γ ⊢[PRAAx] ZT.eq fy (ZT.natLit 0))
    (hQ : Γ ⊢[PRAAx] zle (ZT.ofNat one) Q) :
    Γ ⊢[PRAAx] ZT.eq y x := by
  have product : Γ ⊢[PRAAx] ZT.eq (Q * (y - x)) (ZT.natLit 0) := by
    ipra_lc -ZT.toZ_eq hFactor + ZT.toZ_eq hy - ZT.toZ_eq hx
  have difference := positive_factor_cancel hQ product
  ipra_lc ZT.toZ_eq difference

/-- Division-free numerator of `(u^k-v^k)/(u-v)`, including the zero power. -/
def powerFactor : ℕ → ZT n → ZT n → ZT n
  | 0, _, _ => ZT.natLit 0
  | k + 1, u, v => zpow u k + v * powerFactor k u v

/-- The actual polynomial divided-difference numerator for rational samples. -/
def polynomialFactor : ℕ → PTm n → ZT n → PTm n → ZT n → PTm n → ZT n
  | 0, _, _, _, _, _ => ZT.natLit 0
  | k + 1, code, a, da, b, db =>
      ZT.ofNat (da * db) * polynomialFactor k code a da b db +
        coefficient code (k + 1) * powerFactor (k + 1) (b * ZT.ofNat da) (a * ZT.ofNat db)

private theorem toZ_powerFactor (degree : ℕ) (u v : ZT n) :
    ZT.toZ Γ (powerFactor degree u v) = RingModel.G degree (ZT.toZ Γ u) (ZT.toZ Γ v) := by
  induction degree with
  | zero => simp [powerFactor, RingModel.G]
  | succ k ih => simp only [powerFactor, RingModel.G, ZT.toZ_add, ZT.toZ_mul, toZ_zpow, ih]

private theorem toZ_polynomialFactor (degree : ℕ) (code : PTm n)
    (a : ZT n) (da : PTm n) (b : ZT n) (db : PTm n) :
    ZT.toZ Γ (polynomialFactor degree code a da b db) =
      RingModel.Q degree (fun i => ZT.toZ Γ (coefficient code i))
        (ZT.toZ Γ a) (Groth.ι (Q.mk Γ da)) (ZT.toZ Γ b) (Groth.ι (Q.mk Γ db)) := by
  induction degree with
  | zero => simp [polynomialFactor, RingModel.Q]
  | succ k ih => simp only [polynomialFactor, RingModel.Q, ZT.toZ_add, ZT.toZ_mul,
      ZT.toZ_ofNat, Q.mk_mul, map_mul, toZ_powerFactor, ih]

/-- The exact rational polynomial factor identity is proved, rather than supplied. -/
theorem factor_identity (degree : ℕ) (code : PTm n)
    (a : ZT n) (da : PTm n) (b : ZT n) (db : PTm n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.ofNat (naturalPower da degree) * evaluate degree code b db -
        ZT.ofNat (naturalPower db degree) * evaluate degree code a da)
      ((b * ZT.ofNat da - a * ZT.ofNat db) * polynomialFactor degree code a da b db) := by
  apply ZT.derive
  simp only [ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat, toZ_naturalPower,
    toZ_evaluate, toZ_polynomialFactor]
  exact RingModel.polynomial_difference degree _ _ _ _ _

/-- A positive divided-difference certificate makes rational zeros unique.
Both zeros and the positive factor refer to the actual fixed polynomial. -/
theorem unique_rational_zeros (degree : ℕ) (code : PTm n)
    (a : ZT n) (da : PTm n) (b : ZT n) (db : PTm n)
    (ha : Γ ⊢[PRAAx] ZT.eq (evaluate degree code a da) (ZT.natLit 0))
    (hb : Γ ⊢[PRAAx] ZT.eq (evaluate degree code b db) (ZT.natLit 0))
    (hq : Γ ⊢[PRAAx] zle (ZT.ofNat one) (polynomialFactor degree code a da b db)) :
    Γ ⊢[PRAAx] ZT.eq (b * ZT.ofNat da) (a * ZT.ofNat db) := by
  have ha' : Γ ⊢[PRAAx] ZT.eq
      (ZT.ofNat (naturalPower db degree) * evaluate degree code a da) (ZT.natLit 0) := by
    apply ZT.derive
    have H := ZT.toZ_eq ha
    simp only [ZT.toZ_mul, ZT.toZ_ofNat, ZT.toZ_natLit] at H ⊢
    rw [H]; ring
  have hb' : Γ ⊢[PRAAx] ZT.eq
      (ZT.ofNat (naturalPower da degree) * evaluate degree code b db) (ZT.natLit 0) := by
    apply ZT.derive
    have H := ZT.toZ_eq hb
    simp only [ZT.toZ_mul, ZT.toZ_ofNat, ZT.toZ_natLit] at H ⊢
    rw [H]; ring
  exact unique_of_factor (a * ZT.ofNat db) (b * ZT.ofNat da)
    (ZT.ofNat (naturalPower db degree) * evaluate degree code a da)
    (ZT.ofNat (naturalPower da degree) * evaluate degree code b db)
    (polynomialFactor degree code a da b db) (factor_identity degree code a da b db) ha' hb' hq

/-- Internal variables are the coefficient code, its positive common denominator,
the signed numerator/denominator of the first point, and those of the second. -/
def uniquenessFormula (degree : ℕ) : Fm PTm 8 :=
  let a : ZT 8 := ⟨var 2, var 3⟩
  let b : ZT 8 := ⟨var 5, var 6⟩
  le one (var 1) ⟶ le one (var 4) ⟶ le one (var 7) ⟶
    ZT.eq (evaluate degree (var 0) a (var 4)) (ZT.natLit 0) ⟶
    ZT.eq (evaluate degree (var 0) b (var 7)) (ZT.natLit 0) ⟶
    zle (ZT.ofNat one) (polynomialFactor degree (var 0) a (var 4) b (var 7)) ⟶
    ZT.eq (b * ZT.ofNat (var 4)) (a * ZT.ofNat (var 7))

theorem uniqueness (degree : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8 (uniquenessFormula degree) := by
  refine closeUniv 8 (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  exact unique_rational_zeros degree (var 0) ⟨var 2, var 3⟩ (var 4) ⟨var 5, var 6⟩ (var 7)
    Prf.hyp1.wk Prf.hyp1 Prf.hyp0

#print axioms evaluate_scale
#print axioms factor_identity
#print axioms uniqueness

def mix (b : PTm n) (u v : ZT n) : ZT n :=
  ZT.ofNat b * u + ZT.ofNat (monus one b) * v

def chooseL (b : PTm n) (L R : ZT n) : ZT n :=
  mix b (L + R) (ZT.ofNat two * L)

def chooseR (b : PTm n) (L R : ZT n) : ZT n :=
  mix b (ZT.ofNat two * R) (L + R)

theorem mix_zero {b : PTm n} (u v : ZT n) (hb : Γ ⊢[PRAAx] b ≐ zero) :
    Γ ⊢[PRAAx] ZT.eq (mix b u v) v := by
  apply ZT.derive
  have B := natEq hb
  have C := natEq ((congrMonus (.eqRefl one) hb).eqTrans (monus_zero one))
  simp only [mix, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat]
  rw [B, C]
  simp

theorem mix_one {b : PTm n} (u v : ZT n) (hb : Γ ⊢[PRAAx] b ≐ one) :
    Γ ⊢[PRAAx] ZT.eq (mix b u v) u := by
  apply ZT.derive
  have B := natEq hb
  have C := natEq ((congrMonus (.eqRefl one) hb).eqTrans (monus_self one))
  simp only [mix, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat]
  rw [B, C]
  simp

theorem chooseL_zero {b : PTm n} (L R : ZT n) (hb : Γ ⊢[PRAAx] b ≐ zero) :
    Γ ⊢[PRAAx] ZT.eq (chooseL b L R) (ZT.ofNat two * L) := mix_zero _ _ hb

theorem chooseR_zero {b : PTm n} (L R : ZT n) (hb : Γ ⊢[PRAAx] b ≐ zero) :
    Γ ⊢[PRAAx] ZT.eq (chooseR b L R) (L + R) := mix_zero _ _ hb

theorem chooseL_one {b : PTm n} (L R : ZT n) (hb : Γ ⊢[PRAAx] b ≐ one) :
    Γ ⊢[PRAAx] ZT.eq (chooseL b L R) (L + R) := mix_one _ _ hb

theorem chooseR_one {b : PTm n} (L R : ZT n) (hb : Γ ⊢[PRAAx] b ≐ one) :
    Γ ⊢[PRAAx] ZT.eq (chooseR b L R) (ZT.ofNat two * R) := mix_one _ _ hb

/-- The difference of the new numerators is the old numerator width. -/
theorem width_update {b : PTm n} (L R : ZT n)
    (hb : Γ ⊢[PRAAx] b ≐ zero ⋎ b ≐ one) :
    Γ ⊢[PRAAx] ZT.eq (chooseR b L R - chooseL b L R) (R - L) := by
  refine .orE hb ?_ ?_
  · have left := ZT.toZ_eq (chooseL_zero (Γ := (b ≐ zero) :: Γ) (b := b) L R Prf.hyp0)
    have right := ZT.toZ_eq (chooseR_zero (Γ := (b ≐ zero) :: Γ) (b := b) L R Prf.hyp0)
    apply ZT.derive
    ipra_simps
    linear_combination right - left
  · have left := ZT.toZ_eq (chooseL_one (Γ := (b ≐ one) :: Γ) (b := b) L R Prf.hyp0)
    have right := ZT.toZ_eq (chooseR_one (Γ := (b ≐ one) :: Γ) (b := b) L R Prf.hyp0)
    apply ZT.derive
    ipra_simps
    linear_combination right - left

theorem lower_midpoint {L R : ZT n} (h : Γ ⊢[PRAAx] zle L R) :
    Γ ⊢[PRAAx] zle (ZT.ofNat two * L) (L + R) := by
  have H := zle_toZ h
  apply zle_of_toZ (slack L R)
  dsimp only [slack]
  ipra_simps
  linear_combination H

theorem upper_midpoint {L R : ZT n} (h : Γ ⊢[PRAAx] zle L R) :
    Γ ⊢[PRAAx] zle (L + R) (ZT.ofNat two * R) := by
  have H := zle_toZ h
  apply zle_of_toZ (slack L R)
  dsimp only [slack]
  ipra_simps
  linear_combination H

/-- The scaled new interval is ordered and nested inside the scaled old one. -/
theorem bounds_update {b : PTm n} (L R : ZT n)
    (hb : Γ ⊢[PRAAx] b ≐ zero ⋎ b ≐ one) (hLR : Γ ⊢[PRAAx] zle L R) :
    Γ ⊢[PRAAx]
      zle (ZT.ofNat two * L) (chooseL b L R) ⋏
      zle (chooseL b L R) (chooseR b L R) ⋏
      zle (chooseR b L R) (ZT.ofNat two * R) := by
  refine .orE hb ?_ ?_
  · have left := ZT.toZ_eq (chooseL_zero (Γ := (b ≐ zero) :: Γ) (b := b) L R Prf.hyp0)
    have right := ZT.toZ_eq (chooseR_zero (Γ := (b ≐ zero) :: Γ) (b := b) L R Prf.hyp0)
    exact .andI (zle_congr rfl left.symm (zle_refl _))
      (.andI (zle_congr left.symm right.symm (lower_midpoint hLR.wk))
        (zle_congr right.symm rfl (upper_midpoint hLR.wk)))
  · have left := ZT.toZ_eq (chooseL_one (Γ := (b ≐ one) :: Γ) (b := b) L R Prf.hyp0)
    have right := ZT.toZ_eq (chooseR_one (Γ := (b ≐ one) :: Γ) (b := b) L R Prf.hyp0)
    exact .andI (zle_congr rfl left.symm (lower_midpoint hLR.wk))
      (.andI (zle_congr left.symm right.symm (upper_midpoint hLR.wk))
        (zle_congr right.symm rfl (zle_refl _)))

theorem left_nested {b : PTm n} (L R : ZT n)
    (hb : Γ ⊢[PRAAx] b ≐ zero ⋎ b ≐ one) (hLR : Γ ⊢[PRAAx] zle L R) :
    Γ ⊢[PRAAx] zle (ZT.ofNat two * L) (chooseL b L R) :=
  Prf.andE₁ (bounds_update L R hb hLR)

theorem new_order {b : PTm n} (L R : ZT n)
    (hb : Γ ⊢[PRAAx] b ≐ zero ⋎ b ≐ one) (hLR : Γ ⊢[PRAAx] zle L R) :
    Γ ⊢[PRAAx] zle (chooseL b L R) (chooseR b L R) :=
  Prf.andE₁ (Prf.andE₂ (bounds_update L R hb hLR))

theorem right_nested {b : PTm n} (L R : ZT n)
    (hb : Γ ⊢[PRAAx] b ≐ zero ⋎ b ≐ one) (hLR : Γ ⊢[PRAAx] zle L R) :
    Γ ⊢[PRAAx] zle (chooseR b L R) (ZT.ofNat two * R) :=
  Prf.andE₂ (Prf.andE₂ (bounds_update L R hb hLR))

private theorem evaluate_congr_value (degree : ℕ) (code : PTm n)
    {a b : ZT n} {D E : PTm n} (ha : ZT.toZ Γ a = ZT.toZ Γ b)
    (hD : Γ ⊢[PRAAx] D ≐ E) :
    ZT.toZ Γ (evaluate degree code a D) = ZT.toZ Γ (evaluate degree code b E) := by
  rw [toZ_evaluate, toZ_evaluate, ha, natEq hD]

/-- The actual denominator of the represented rational polynomial value. -/
def evaluationDenominator (degree : ℕ) (C D : PTm n) : PTm n := C * naturalPower D degree

theorem evaluationDenominator_positive (degree : ℕ) (C D : PTm n)
    (hC : Γ ⊢[PRAAx] le one C) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] le one (evaluationDenominator degree C D) :=
  le_congr (one_mul one) (.eqRefl _) (le_mul_mono hC (naturalPower_positive D degree hD))

theorem evaluate_double_nonpos (degree : ℕ) (code : PTm n) (a : ZT n) (D : PTm n)
    (h : Γ ⊢[PRAAx] zle (evaluate degree code a D) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] zle (evaluate degree code (ZT.ofNat two * a) (two * D)) (ZT.natLit 0) := by
  have scaling := ZT.toZ_eq (evaluate_scale (Γ := Γ) degree code a D two)
  apply zle_congr scaling.symm _ (zle_scale (naturalPower two degree) h)
  simp only [ZT.toZ_mul, ZT.toZ_natLit]
  ring

theorem evaluate_double_nonneg (degree : ℕ) (code : PTm n) (a : ZT n) (D : PTm n)
    (h : Γ ⊢[PRAAx] zle (ZT.natLit 0) (evaluate degree code a D)) :
    Γ ⊢[PRAAx] zle (ZT.natLit 0) (evaluate degree code (ZT.ofNat two * a) (two * D)) := by
  have scaling := ZT.toZ_eq (evaluate_scale (Γ := Γ) degree code a D two)
  apply zle_congr _ scaling.symm (zle_scale (naturalPower two degree) h)
  simp only [ZT.toZ_mul, ZT.toZ_natLit]
  ring

/-- Zero midpoint values always choose the nonpositive (left-moving) branch. -/
theorem selector_at_zero {u : ZT n} (h : Γ ⊢[PRAAx] ZT.eq u (ZT.natLit 0)) :
    Γ ⊢[PRAAx] selector u ≐ one := by
  have hn : Γ ⊢[PRAAx] u.pos ≐ u.neg :=
    (add_zero u.pos).eqSymm.eqTrans (h.eqTrans (zero_add u.neg))
  exact eqb_of_eq ((congrMonus hn (.eqRefl _)).eqTrans (monus_self _))

/-- The exact sign bit of the actual homogeneous midpoint polynomial value. -/
def midpointBit (degree : ℕ) (code s : PTm n) : PTm n :=
  selector (evaluate degree code (left s + right s) (two * denominator s))

/-- Actual branch update. Its two output numerators share twice the old denominator. -/
def advance (degree : ℕ) (code s : PTm n) : PTm n :=
  state (chooseL (midpointBit degree code s) (left s) (right s))
    (chooseR (midpointBit degree code s) (left s) (right s)) (two * denominator s)

theorem advance_denominator (degree : ℕ) (code s : PTm n) :
    Γ ⊢[PRAAx] denominator (advance degree code s) ≐ two * denominator s :=
  denominator_state _ _ _

private theorem advance_left_value (degree : ℕ) (code s : PTm n) :
    ZT.toZ Γ (left (advance degree code s)) =
      ZT.toZ Γ (chooseL (midpointBit degree code s) (left s) (right s)) :=
  left_state_value _ _ _

private theorem advance_right_value (degree : ℕ) (code s : PTm n) :
    ZT.toZ Γ (right (advance degree code s)) =
      ZT.toZ Γ (chooseR (midpointBit degree code s) (left s) (right s)) :=
  right_state_value _ _ _

/-- The exact rational bracket invariant, including denominator positivity. -/
def bracket (degree : ℕ) (code s : PTm n) : Fm PTm n :=
  le one (denominator s) ⋏ zle (left s) (right s) ⋏
    zle (evaluate degree code (left s) (denominator s)) (ZT.natLit 0) ⋏
    zle (ZT.natLit 0) (evaluate degree code (right s) (denominator s))

theorem bracket_QF (degree : ℕ) (code s : PTm n) : (bracket degree code s).QF :=
  ⟨trivial, trivial, trivial, trivial⟩

/-- The actual midpoint decision preserves both endpoint signs. -/
theorem advance_signs (degree : ℕ) (code s : PTm n)
    (hl : Γ ⊢[PRAAx] zle (evaluate degree code (left s) (denominator s)) (ZT.natLit 0))
    (hr : Γ ⊢[PRAAx] zle (ZT.natLit 0) (evaluate degree code (right s) (denominator s))) :
    Γ ⊢[PRAAx]
      zle (evaluate degree code (left (advance degree code s)) (denominator (advance degree code s))) (ZT.natLit 0) ⋏
      zle (ZT.natLit 0) (evaluate degree code (right (advance degree code s)) (denominator (advance degree code s))) := by
  let L := left s
  let R := right s
  let D := denominator s
  let b := midpointBit degree code s
  have signs : Γ ⊢[PRAAx]
      zle (evaluate degree code (chooseL b L R) (two * D)) (ZT.natLit 0) ⋏
      zle (ZT.natLit 0) (evaluate degree code (chooseR b L R) (two * D)) := by
    refine .orE (selector_cases (evaluate degree code (L + R) (two * D))) ?_ ?_
    · let Δ := (b ≐ zero) :: Γ
      have lb := ZT.toZ_eq (chooseL_zero (Γ := Δ) (b := b) L R Prf.hyp0)
      have rb := ZT.toZ_eq (chooseR_zero (Γ := Δ) (b := b) L R Prf.hyp0)
      exact .andI
        (zle_congr (evaluate_congr_value degree code lb (.eqRefl _)).symm rfl
          (evaluate_double_nonpos degree code L D hl.wk))
        (zle_congr rfl (evaluate_congr_value degree code rb (.eqRefl _)).symm
          (selector_zero (u := evaluate degree code (L + R) (two * D)) Prf.hyp0))
    · let Δ := (b ≐ one) :: Γ
      have lb := ZT.toZ_eq (chooseL_one (Γ := Δ) (b := b) L R Prf.hyp0)
      have rb := ZT.toZ_eq (chooseR_one (Γ := Δ) (b := b) L R Prf.hyp0)
      exact .andI
        (zle_congr (evaluate_congr_value degree code lb (.eqRefl _)).symm rfl
          (selector_one (u := evaluate degree code (L + R) (two * D)) Prf.hyp0))
        (zle_congr rfl (evaluate_congr_value degree code rb (.eqRefl _)).symm
          (evaluate_double_nonneg degree code R D hr.wk))
  have leftEq := evaluate_congr_value degree code (advance_left_value (Γ := Γ) degree code s)
    (advance_denominator degree code s)
  have rightEq := evaluate_congr_value degree code (advance_right_value (Γ := Γ) degree code s)
    (advance_denominator degree code s)
  exact .andI (zle_congr leftEq.symm rfl (Prf.andE₁ signs))
    (zle_congr rfl rightEq.symm (Prf.andE₂ signs))

/-- This preservation theorem is derived from evaluation and exact sign reflection. -/
theorem advance_bracket (degree : ℕ) (code s : PTm n)
    (h : Γ ⊢[PRAAx] bracket degree code s) :
    Γ ⊢[PRAAx] bracket degree code (advance degree code s) := by
  have hd := Prf.andE₁ h
  have hLR := Prf.andE₁ (Prf.andE₂ h)
  have hp := advance_signs degree code s (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h)))
    (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  refine .andI ?_ (.andI ?_ hp)
  · exact le_congr (one_mul one) (advance_denominator degree code s).eqSymm
      (le_mul_mono (le_succ_self one) hd)
  · exact zle_congr (advance_left_value degree code s).symm (advance_right_value degree code s).symm
      (new_order (left s) (right s)
        (selector_cases (evaluate degree code (left s + right s) (two * denominator s))) hLR)

theorem advance_width (degree : ℕ) (code s : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (right (advance degree code s) - left (advance degree code s)) (right s - left s) := by
  apply ZT.derive
  have old := ZT.toZ_eq (width_update (Γ := Γ) (left s) (right s)
    (selector_cases (evaluate degree code (left s + right s) (two * denominator s))))
  simp only [ZT.toZ_sub, advance_left_value, advance_right_value] at old ⊢
  exact old

/-- Both new endpoints lie inside the old interval after clearing the factor two. -/
theorem advance_nested (degree : ℕ) (code s : PTm n) (h : Γ ⊢[PRAAx] zle (left s) (right s)) :
    Γ ⊢[PRAAx] zle (ZT.ofNat two * left s) (left (advance degree code s)) ⋏
      zle (right (advance degree code s)) (ZT.ofNat two * right s) := by
  have hb := selector_cases (Γ := Γ) (evaluate degree code (left s + right s) (two * denominator s))
  exact .andI
    (zle_congr rfl (advance_left_value degree code s).symm (left_nested (left s) (right s) hb h))
    (zle_congr (advance_right_value degree code s).symm rfl (right_nested (left s) (right s) hb h))

#print axioms advance_signs
#print axioms advance_bracket
#print axioms advance_width
#print axioms advance_nested

@[simp] private theorem subst_zle {m : ℕ} (σ : Fin n → PTm m) (u v : ZT n) :
    (zle u v).subst σ = zle (u.subst σ) (v.subst σ) := by
  simp [zle, ZT.subst]

@[simp] private theorem subst_one {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (one : PTm n) = one := by
  simp only [one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

@[simp] private theorem subst_two {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (two : PTm n) = two := by
  simp only [two, one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

@[simp] theorem subst_selector {m : ℕ} (σ : Fin n → PTm m) (u : ZT n) :
    Syn.subst σ (selector u) = selector (u.subst σ) := by
  simp only [selector, subst_eqb, PTm.subst_monus, ConciseIPRA.PTm.subst_zero, ZT.subst]

@[simp] theorem subst_mix {m : ℕ} (σ : Fin n → PTm m) (b : PTm n) (u v : ZT n) :
    (mix b u v).subst σ = mix (Syn.subst σ b) (u.subst σ) (v.subst σ) := by
  simp only [mix, ZT.subst_add, ZT.subst_mul, ZT.subst_ofNat, PTm.subst_monus, subst_one]

@[simp] theorem subst_chooseL {m : ℕ} (σ : Fin n → PTm m) (b : PTm n) (L R : ZT n) :
    (chooseL b L R).subst σ = chooseL (Syn.subst σ b) (L.subst σ) (R.subst σ) := by
  simp only [chooseL, subst_mix, ZT.subst_add, ZT.subst_mul, ZT.subst_ofNat, subst_two]

@[simp] theorem subst_chooseR {m : ℕ} (σ : Fin n → PTm m) (b : PTm n) (L R : ZT n) :
    (chooseR b L R).subst σ = chooseR (Syn.subst σ b) (L.subst σ) (R.subst σ) := by
  simp only [chooseR, subst_mix, ZT.subst_add, ZT.subst_mul, ZT.subst_ofNat, subst_two]

@[simp] theorem subst_midpointBit {m : ℕ} (σ : Fin n → PTm m) (degree : ℕ) (code s : PTm n) :
    Syn.subst σ (midpointBit degree code s) =
      midpointBit degree (Syn.subst σ code) (Syn.subst σ s) := by
  simp only [midpointBit, subst_selector, subst_evaluate, ZT.subst_add, subst_left,
    subst_right, PTm.subst_mul, subst_two, subst_denominator]

@[simp] theorem subst_advance {m : ℕ} (σ : Fin n → PTm m) (degree : ℕ) (code s : PTm n) :
    Syn.subst σ (advance degree code s) = advance degree (Syn.subst σ code) (Syn.subst σ s) := by
  simp only [advance, subst_state, subst_chooseL, subst_chooseR, subst_midpointBit,
    subst_left, subst_right, PTm.subst_mul, subst_two, subst_denominator]

@[simp] theorem subst_bracket {m : ℕ} (σ : Fin n → PTm m) (degree : ℕ) (code s : PTm n) :
    (bracket degree code s).subst σ = bracket degree (Syn.subst σ code) (Syn.subst σ s) := by
  simp only [bracket, Fm.subst_and, subst_zle, subst_evaluate, subst_left, subst_right,
    ZT.subst_natLit, subst_denominator]
  simp only [subst_le, subst_one, subst_denominator]

theorem bracket_congr (degree : ℕ) (code : PTm n) {s t : PTm n}
    (hst : Γ ⊢[PRAAx] s ≐ t) (h : Γ ⊢[PRAAx] bracket degree code s) :
    Γ ⊢[PRAAx] bracket degree code t := by
  have source : Γ ⊢[PRAAx] (bracket degree (var 0) (var 1) : Fm PTm 2).subst ![code, s] := by
    simpa only [subst_bracket, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  have target := Prf.eqSubst (bracket degree (var 0) (var 1) : Fm PTm 2)
    ![code, s] ![code, t] (fun i => by fin_cases i; exact .eqRefl _; exact hst) source
  simpa only [subst_bracket, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using target

/-- The fixed update program, with state and coefficient data as its two inputs. -/
def updateTerm (degree : ℕ) : PTm 2 := advance degree (var 1) (var 0)

/-- Actual primitive recursive execution, using the checked generic PR iterator. -/
def run (degree : ℕ) (k code initial : PTm n) : PTm n :=
  Foundations.TraceInvariant.run (updateTerm degree) k initial code

@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (degree : ℕ) (k code initial : PTm n) :
    Syn.subst σ (run degree k code initial) =
      run degree (Syn.subst σ k) (Syn.subst σ code) (Syn.subst σ initial) := by
  simp only [run, Foundations.TraceInvariant.run, subst_ap2, subst_pairT]

theorem run_zero (degree : ℕ) (code initial : PTm n) :
    Γ ⊢[PRAAx] run degree zero code initial ≐ initial :=
  Foundations.TraceInvariant.run_zero (updateTerm degree) initial code

theorem run_succ (degree : ℕ) (k code initial : PTm n) :
    Γ ⊢[PRAAx] run degree (succ k) code initial ≐ advance degree code (run degree k code initial) := by
  simpa only [run, updateTerm, inst2, subst_advance, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one] using
      Foundations.TraceInvariant.run_succ (Γ := Γ) (updateTerm degree) k initial code

theorem run_add (degree : ℕ) (N r code initial : PTm n) :
    Γ ⊢[PRAAx] run degree (N + r) code initial ≐ run degree r code (run degree N code initial) :=
  Foundations.TraceInvariant.run_add (updateTerm degree) N r initial code

/-- Every state of the actual bisection run is a valid sign bracket. -/
theorem run_bracket (degree : ℕ) (k code initial : PTm n)
    (h : Γ ⊢[PRAAx] bracket degree code initial) :
    Γ ⊢[PRAAx] bracket degree code (run degree k code initial) := by
  have hall : Γ ⊢[PRAAx] .all
      (bracket degree (Syn.shift code) (run degree (var 0) (Syn.shift code) (Syn.shift initial))) := by
    refine PRA.qfInd _ (bracket_QF _ _ _) ?_ ?_
    · simp only [subst_bracket, subst_run, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero]
      exact bracket_congr degree code (run_zero degree code initial).eqSymm h
    · simp only [subst_bracket, subst_run, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact bracket_congr degree (Syn.shift code) (run_succ degree _ _ _).eqSymm
        (advance_bracket degree _ _ Prf.hyp0)
  simpa only [subst_bracket, subst_run, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE k hall

private theorem left_congr_value {s t : PTm n} (h : Γ ⊢[PRAAx] s ≐ t) :
    ZT.toZ Γ (left s) = ZT.toZ Γ (left t) := unpack_congr (congrFst h)

private theorem right_congr_value {s t : PTm n} (h : Γ ⊢[PRAAx] s ≐ t) :
    ZT.toZ Γ (right s) = ZT.toZ Γ (right t) := unpack_congr (congrFst (congrSnd h))

private theorem denominator_congr {s t : PTm n} (h : Γ ⊢[PRAAx] s ≐ t) :
    Γ ⊢[PRAAx] denominator s ≐ denominator t := congrSnd (congrSnd h)

/-- The numerator width is exactly constant, including a zero-width initial bracket. -/
theorem run_width (degree : ℕ) (k code initial : PTm n) :
    Γ ⊢[PRAAx] ZT.eq
      (right (run degree k code initial) - left (run degree k code initial)) (right initial - left initial) := by
  have hall : Γ ⊢[PRAAx] .all (ZT.eq
      (right (run degree (var 0) (Syn.shift code) (Syn.shift initial)) -
        left (run degree (var 0) (Syn.shift code) (Syn.shift initial)))
      (right (Syn.shift initial) - left (Syn.shift initial))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [ZT.subst_eq, ZT.subst_sub, subst_right, subst_left, subst_run,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      apply ZT.derive
      simp only [ZT.toZ_sub, left_congr_value (run_zero (Γ := Γ) degree code initial),
        right_congr_value (run_zero (Γ := Γ) degree code initial)]
    · simp only [ZT.subst_eq, ZT.subst_sub, subst_right, subst_left, subst_run,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      apply ZT.derive
      let Δ := ZT.eq
        (right (run degree (var 0) (Syn.shift code) (Syn.shift initial)) -
          left (run degree (var 0) (Syn.shift code) (Syn.shift initial)))
        (right (Syn.shift initial) - left (Syn.shift initial)) :: Γ.map Fm.shift
      have step := ZT.toZ_eq (advance_width (Γ := Δ) degree (Syn.shift code)
        (run degree (var 0) (Syn.shift code) (Syn.shift initial)))
      have ih := ZT.toZ_eq (Prf.hyp0 (Ax := PRAAx) (φ := ZT.eq
        (right (run degree (var 0) (Syn.shift code) (Syn.shift initial)) -
          left (run degree (var 0) (Syn.shift code) (Syn.shift initial)))
        (right (Syn.shift initial) - left (Syn.shift initial))) (Γ := Γ.map Fm.shift))
      simp only [ZT.toZ_sub] at step ih ⊢
      rw [left_congr_value (run_succ degree _ _ _), right_congr_value (run_succ degree _ _ _)]
      exact step.trans ih
  simpa only [ZT.subst_eq, ZT.subst_sub, subst_right, subst_left, subst_run,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE k hall

/-- The actual run denominator is `D₀ * 2^k`, so its rational width halves. -/
theorem run_denominator (degree : ℕ) (k code initial : PTm n) :
    Γ ⊢[PRAAx] denominator (run degree k code initial) ≐ denominator initial * pw two k := by
  have hall : Γ ⊢[PRAAx] .all (denominator
      (run degree (var 0) (Syn.shift code) (Syn.shift initial)) ≐
      denominator (Syn.shift initial) * pw two (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_denominator, subst_run, PTm.subst_mul,
        subst_ap2, subst_two, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero]
      exact (denominator_congr (run_zero degree code initial)).eqTrans
        ((by ipra_ring : Γ ⊢[PRAAx] denominator initial ≐ denominator initial * one).eqTrans
          (congrMul (.eqRefl _) (pw_zero two).eqSymm))
    · simp only [Fm.subst_eq, subst_denominator, subst_run, PTm.subst_mul,
        subst_ap2, subst_two, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ := (denominator (run degree (var 0) (Syn.shift code) (Syn.shift initial)) ≐
        denominator (Syn.shift initial) * pw two (var 0)) :: Γ.map Fm.shift
      have final : Δ ⊢[PRAAx] two * (denominator (Syn.shift initial) * pw two (var 0)) ≐
          denominator (Syn.shift initial) * pw two (succ (var 0)) := by
        have hp := natEq (pw_succ (Γ := Δ) two (var 0))
        apply deriveNat
        ipra_simps
        rw [hp]
        ring
      exact (denominator_congr (run_succ degree _ _ _)).eqTrans
        ((advance_denominator degree _ _).eqTrans
          ((congrMul (.eqRefl two) Prf.hyp0).eqTrans final))
  simpa only [Fm.subst_eq, subst_denominator, subst_run, PTm.subst_mul,
    subst_ap2, subst_two, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE k hall

#print axioms run_bracket
#print axioms run_width
#print axioms run_denominator

private theorem scale_pow_zero (u : ZT n) :
    ZT.toZ Γ (ZT.ofNat (pw two zero) * u) = ZT.toZ Γ u := by
  simp only [ZT.toZ_mul, ZT.toZ_ofNat, natEq (pw_zero (Γ := Γ) two), Q.mk_one, map_one]
  ring

private theorem scale_pow_succ (u : ZT n) (k : PTm n) :
    ZT.toZ Γ (ZT.ofNat two * (ZT.ofNat (pw two k) * u)) =
      ZT.toZ Γ (ZT.ofNat (pw two (succ k)) * u) := by
  simp only [ZT.toZ_mul, ZT.toZ_ofNat, natEq (pw_succ (Γ := Γ) two k), Q.mk_mul, map_mul]
  ring

/-- Inclusion in the starting rational interval after clearing dyadic denominators. -/
def nestedBound (degree : ℕ) (code initial k : PTm n) : Fm PTm n :=
  zle (ZT.ofNat (pw two k) * left initial) (left (run degree k code initial)) ⋏
    zle (right (run degree k code initial)) (ZT.ofNat (pw two k) * right initial)

@[simp] theorem subst_nestedBound {m : ℕ} (σ : Fin n → PTm m) (degree : ℕ)
    (code initial k : PTm n) :
    (nestedBound degree code initial k).subst σ =
      nestedBound degree (Syn.subst σ code) (Syn.subst σ initial) (Syn.subst σ k) := by
  simp only [nestedBound, Fm.subst_and, subst_zle, ZT.subst_mul, ZT.subst_ofNat,
    subst_ap2, subst_two, subst_left, subst_right, subst_run]

/-- The actual PR intervals are nested; no nesting or trace-correctness premise is used. -/
theorem run_nested (degree : ℕ) (k code initial : PTm n)
    (h : Γ ⊢[PRAAx] bracket degree code initial) :
    Γ ⊢[PRAAx] nestedBound degree code initial k := by
  have hall : Γ ⊢[PRAAx] .all
      (nestedBound degree (Syn.shift code) (Syn.shift initial) (var 0)) := by
    refine PRA.qfInd _ ⟨trivial, trivial⟩ ?_ ?_
    · simp only [subst_nestedBound, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact .andI
        (zle_congr (scale_pow_zero (Γ := Γ) (left initial)).symm
          (left_congr_value (run_zero degree code initial)).symm (zle_refl _))
        (zle_congr (right_congr_value (run_zero degree code initial)).symm
          (scale_pow_zero (Γ := Γ) (right initial)).symm (zle_refl _))
    · simp only [subst_nestedBound, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ := nestedBound degree (Syn.shift code) (Syn.shift initial) (var 0) :: Γ.map Fm.shift
      have shifted : Γ.map Fm.shift ⊢[PRAAx] bracket degree (Syn.shift code) (Syn.shift initial) := by
        simpa only [Fm.shift, subst_bracket, Syn.shift] using h.shift
      have current := run_bracket (Γ := Δ) degree (var 0) (Syn.shift code) (Syn.shift initial) shifted.wk
      have adjacent := advance_nested degree (Syn.shift code)
        (run degree (var 0) (Syn.shift code) (Syn.shift initial)) (Prf.andE₁ (Prf.andE₂ current))
      have next := run_succ (Γ := Δ) degree (var 0) (Syn.shift code) (Syn.shift initial)
      refine .andI ?_ ?_
      · have lower := zle_trans (zle_scale two (Prf.andE₁ (Prf.hyp0 (Γ := Γ.map Fm.shift)
            (φ := nestedBound degree (Syn.shift code) (Syn.shift initial) (var 0)))))
          (Prf.andE₁ adjacent)
        exact zle_congr (scale_pow_succ (Γ := Δ) (left (Syn.shift initial)) (var 0))
          (left_congr_value next).symm lower
      · have upper := zle_trans (Prf.andE₂ adjacent)
          (zle_scale two (Prf.andE₂ (Prf.hyp0 (Γ := Γ.map Fm.shift)
            (φ := nestedBound degree (Syn.shift code) (Syn.shift initial) (var 0)))))
        exact zle_congr (right_congr_value next).symm
          (scale_pow_succ (Γ := Δ) (right (Syn.shift initial)) (var 0)) upper
  simpa only [subst_nestedBound, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE k hall

/-- Arbitrary finite windows are nested, using the proved composition of the actual PR run. -/
theorem nested_window (degree : ℕ) (N r code initial : PTm n)
    (h : Γ ⊢[PRAAx] bracket degree code initial) :
    Γ ⊢[PRAAx]
      zle (ZT.ofNat (pw two r) * left (run degree N code initial))
        (left (run degree (N + r) code initial)) ⋏
      zle (right (run degree (N + r) code initial))
        (ZT.ofNat (pw two r) * right (run degree N code initial)) := by
  have later := run_nested degree r code (run degree N code initial) (run_bracket degree N code initial h)
  have same := run_add (Γ := Γ) degree N r code initial
  exact .andI (zle_congr rfl (left_congr_value same).symm (Prf.andE₁ later))
    (zle_congr (right_congr_value same).symm rfl (Prf.andE₂ later))

theorem nested_between (degree : ℕ) (code initial : PTm n) {N M : PTm n}
    (h : Γ ⊢[PRAAx] bracket degree code initial) (order : Γ ⊢[PRAAx] le N M) :
    Γ ⊢[PRAAx]
      zle (ZT.ofNat (pw two (monus M N)) * left (run degree N code initial))
        (left (run degree M code initial)) ⋏
      zle (right (run degree M code initial))
        (ZT.ofNat (pw two (monus M N)) * right (run degree N code initial)) := by
  have index : Γ ⊢[PRAAx] N + monus M N ≐ M := (eq_add_of_le order).eqSymm
  have same : Γ ⊢[PRAAx] run degree (N + monus M N) code initial ≐ run degree M code initial :=
    congrAp2 (Foundations.TraceInvariant.runF (updateTerm degree)) index (.eqRefl _)
  have window := nested_window degree N (monus M N) code initial h
  exact .andI (zle_congr rfl (left_congr_value same) (Prf.andE₁ window))
    (zle_congr (right_congr_value same) rfl (Prf.andE₂ window))

/-- Variables `0=k`, `1=coefficient code`, `2=coefficient denominator`,
`3=initial encoded bracket`. The sole analytic input is its initial endpoint
signs; the entire finite trace is produced by the actual PR algorithm. -/
def bisectionFormula (degree : ℕ) : Fm PTm 4 :=
  let s := run degree (var 0) (var 1) (var 3)
  le one (var 2) ⟶ bracket degree (var 1) (var 3) ⟶
    (bracket degree (var 1) s ⋏
      le one (evaluationDenominator degree (var 2) (denominator s)) ⋏
      (denominator s ≐ denominator (var 3) * pw two (var 0)) ⋏
      ZT.eq (right s - left s) (right (var 3) - left (var 3)) ⋏
      nestedBound degree (var 1) (var 3) (var 0))

/-- Universally closed correctness of the actual fixed-degree polynomial bisection. -/
theorem bisection (degree : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (bisectionFormula degree) := by
  refine closeUniv 4 (.impI (.impI ?_))
  have hb := run_bracket (n := 4) degree (var 0) (var 1) (var 3)
    (Prf.hyp0 (Γ := [le one (var 2)]) (φ := bracket degree (var 1) (var 3)))
  exact .andI hb (.andI
    (evaluationDenominator_positive degree (var 2) _ Prf.hyp1 (Prf.andE₁ hb))
    (.andI (run_denominator degree _ _ _) (.andI (run_width degree _ _ _)
      (run_nested degree _ _ _ Prf.hyp0))))

/-- Variables `0=N`, `1=M`, `2=coefficient code`, `3=coefficient denominator`,
`4=initial bracket code`. All endpoint indices remain internal. -/
def nestedFormula (degree : ℕ) : Fm PTm 5 :=
  le one (var 3) ⟶ bracket degree (var 2) (var 4) ⟶ le (var 0) (var 1) ⟶
    (zle (ZT.ofNat (pw two (monus (var 1) (var 0))) * left (run degree (var 0) (var 2) (var 4)))
      (left (run degree (var 1) (var 2) (var 4))) ⋏
     zle (right (run degree (var 1) (var 2) (var 4)))
      (ZT.ofNat (pw two (monus (var 1) (var 0))) * right (run degree (var 0) (var 2) (var 4))))

theorem bisection_nested (degree : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 (nestedFormula degree) :=
  closeUniv 5 (.impI (.impI (.impI (nested_between degree (var 2) (var 4) Prf.hyp1 Prf.hyp0))))

#print axioms run_nested
#print axioms nested_between
#print axioms bisection
#print axioms bisection_nested
#print axioms selector_at_zero
#print axioms run_succ
#print axioms run_add

end LeanProofs.IPRA.Analysis.PolynomialBisection
