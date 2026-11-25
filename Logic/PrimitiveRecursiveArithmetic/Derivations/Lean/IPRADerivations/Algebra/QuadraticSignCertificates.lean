import IPRADerivations.Algebra.QuadraticExtension
import IPRADerivations.Core.IntCertificates
import IPRADerivations.Foundations.GuardedTotalization
import IPRADerivations.AnalyticNumberTheory.Totatives
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual positive quadratic sign certificates over coded integers

This is the single integer ground stage of isoperimetric_ipra,
lem:orderedextension, equations (2.4)--(2.5). For a positive numerical
radicand d the actual finite program constructs a cone multiplier and a
three-way sign certificate. Redundant square radicands are permitted.
The d=0 projection, iterated rational radical towers and the ordered
quotient laws are separate obligations.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticSignCertificates

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def code (a : ZT n) : PTm n := pairT a.pos a.neg
def decode (q : PTm n) : ZT n := ⟨fstT q,sndT q⟩
def first (x : PTm n) : ZT n := decode (fstT x)
def second (x : PTm n) : ZT n := decode (sndT x)
def encode (a b : ZT n) : PTm n := pairT (code a) (code b)
def zeroCode : PTm n := encode (ZT.ofNat zero) (ZT.ofNat zero)
def oneCode : PTm n := encode (ZT.ofNat one) (ZT.ofNat zero)
def naturalPair (a b : PTm n) : PTm n := encode (ZT.ofNat a) (ZT.ofNat b)
def add (x y : PTm n) : PTm n := encode (first x+first y) (second x+second y)
def negative (x : PTm n) : PTm n := encode (-first x) (-second x)
def multiply (d x y : PTm n) : PTm n := encode
  (first x*first y+ZT.ofNat d*(second x*second y))
  (first x*second y+second x*first y)
def equal (x y : PTm n) : Fm PTm n := ZT.eq (first x) (first y) ⋏ ZT.eq (second x) (second y)
def cone (x : PTm n) : Fm PTm n := zle (ZT.ofNat zero) (first x) ⋏
  (zle (ZT.ofNat zero) (second x) ⋏ zle (ZT.ofNat one) (first x+second x))
def positivePart (a : ZT n) : PTm n := monus a.pos a.neg
def negativePart (a : ZT n) : PTm n := monus a.neg a.pos
def magnitude (a : ZT n) : PTm n := positivePart a+negativePart a
def mass (x : PTm n) : PTm n := magnitude (first x)+magnitude (second x)
def multiplier (x : PTm n) : PTm n := Foundations.GuardedTotalization.sel (eqb (mass x) zero)
  oneCode (naturalPair (magnitude (first x)) (magnitude (second x)))
def product (d x : PTm n) : PTm n := multiply d (multiplier x) x
def scalar (d x : PTm n) : ZT n := first (product d x)+second (product d x)
def positiveBit (d x : PTm n) : PTm n := Signum.sg (positivePart (scalar d x))
def negativeBit (d x : PTm n) : PTm n := Signum.sg (negativePart (scalar d x))
def sign (d x : PTm n) : PTm n := positiveBit d x+two*negativeBit d x

@[simp] theorem subst_code {l : ℕ} (σ : Fin n → PTm l) (a : ZT n) : Syn.subst σ (code a) = code (a.subst σ) := by simp [code,ZT.subst]
@[simp] theorem subst_decode {l : ℕ} (σ : Fin n → PTm l) (q : PTm n) : (decode q).subst σ = decode (Syn.subst σ q) := by simp [decode,ZT.subst]
@[simp] theorem subst_first {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) : (first x).subst σ = first (Syn.subst σ x) := by simp [first]
@[simp] theorem subst_second {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) : (second x).subst σ = second (Syn.subst σ x) := by simp [second]
@[simp] theorem subst_encode {l : ℕ} (σ : Fin n → PTm l) (a b : ZT n) : Syn.subst σ (encode a b) = encode (a.subst σ) (b.subst σ) := by simp [encode]
@[simp] theorem subst_zeroCode {l : ℕ} (σ : Fin n → PTm l) : Syn.subst σ (zeroCode : PTm n) = (zeroCode : PTm l) := by simp [zeroCode]
@[simp] theorem subst_oneCode {l : ℕ} (σ : Fin n → PTm l) : Syn.subst σ (oneCode : PTm n) = (oneCode : PTm l) := by simp [oneCode,one]
@[simp] theorem subst_naturalPair {l : ℕ} (σ : Fin n → PTm l) (a b : PTm n) : Syn.subst σ (naturalPair a b) = naturalPair (Syn.subst σ a) (Syn.subst σ b) := by simp [naturalPair]
@[simp] theorem subst_add {l : ℕ} (σ : Fin n → PTm l) (x y : PTm n) : Syn.subst σ (add x y) = add (Syn.subst σ x) (Syn.subst σ y) := by simp [add]
@[simp] theorem subst_negative {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) : Syn.subst σ (negative x) = negative (Syn.subst σ x) := by simp [negative]
@[simp] theorem subst_multiply {l : ℕ} (σ : Fin n → PTm l) (d x y : PTm n) : Syn.subst σ (multiply d x y) = multiply (Syn.subst σ d) (Syn.subst σ x) (Syn.subst σ y) := by simp [multiply]
@[simp] theorem subst_equal {l : ℕ} (σ : Fin n → PTm l) (x y : PTm n) : (equal x y).subst σ = equal (Syn.subst σ x) (Syn.subst σ y) := by simp [equal]
@[simp] theorem subst_zle {l : ℕ} (σ : Fin n → PTm l) (a b : ZT n) :
    (zle a b).subst σ = zle (a.subst σ) (b.subst σ) := by simp [zle,ZT.subst]
@[simp] theorem subst_cone {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) : (cone x).subst σ = cone (Syn.subst σ x) := by simp only [cone,Fm.subst_and,subst_zle,ZT.subst_ofNat,ZT.subst_add,subst_first,subst_second,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ]
@[simp] theorem subst_positivePart {l : ℕ} (σ : Fin n → PTm l) (a : ZT n) : Syn.subst σ (positivePart a) = positivePart (a.subst σ) := by simp [positivePart,ZT.subst]
@[simp] theorem subst_negativePart {l : ℕ} (σ : Fin n → PTm l) (a : ZT n) : Syn.subst σ (negativePart a) = negativePart (a.subst σ) := by simp [negativePart,ZT.subst]
@[simp] theorem subst_magnitude {l : ℕ} (σ : Fin n → PTm l) (a : ZT n) : Syn.subst σ (magnitude a) = magnitude (a.subst σ) := by simp [magnitude]
@[simp] theorem subst_mass {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) : Syn.subst σ (mass x) = mass (Syn.subst σ x) := by simp [mass]
@[simp] theorem subst_multiplier {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) : Syn.subst σ (multiplier x) = multiplier (Syn.subst σ x) := by simp [multiplier]
@[simp] theorem subst_product {l : ℕ} (σ : Fin n → PTm l) (d x : PTm n) : Syn.subst σ (product d x) = product (Syn.subst σ d) (Syn.subst σ x) := by simp [product]
@[simp] theorem subst_scalar {l : ℕ} (σ : Fin n → PTm l) (d x : PTm n) : (scalar d x).subst σ = scalar (Syn.subst σ d) (Syn.subst σ x) := by simp [scalar]
@[simp] theorem subst_positiveBit {l : ℕ} (σ : Fin n → PTm l) (d x : PTm n) : Syn.subst σ (positiveBit d x) = positiveBit (Syn.subst σ d) (Syn.subst σ x) := by simp [positiveBit,Signum.sg]
@[simp] theorem subst_negativeBit {l : ℕ} (σ : Fin n → PTm l) (d x : PTm n) : Syn.subst σ (negativeBit d x) = negativeBit (Syn.subst σ d) (Syn.subst σ x) := by simp [negativeBit,Signum.sg]
@[simp] theorem subst_sign {l : ℕ} (σ : Fin n → PTm l) (d x : PTm n) : Syn.subst σ (sign d x) = sign (Syn.subst σ d) (Syn.subst σ x) := by simp [sign]

theorem first_encode (a b : ZT n) : Γ ⊢[PRAAx] ZT.eq (first (encode a b)) a := by
  have hp : Γ ⊢[PRAAx] fstT (fstT (encode a b)) ≐ a.pos :=
    (congrFst (fst_pair (code a) (code b))).eqTrans (fst_pair a.pos a.neg)
  have hn : Γ ⊢[PRAAx] sndT (fstT (encode a b)) ≐ a.neg :=
    (congrSnd (fst_pair (code a) (code b))).eqTrans (snd_pair a.pos a.neg)
  apply ZT.derive
  simp only [first,decode,ZT.toZ]
  rw [natEq hp,natEq hn]
theorem second_encode (a b : ZT n) : Γ ⊢[PRAAx] ZT.eq (second (encode a b)) b := by
  have hp : Γ ⊢[PRAAx] fstT (sndT (encode a b)) ≐ b.pos :=
    (congrFst (snd_pair (code a) (code b))).eqTrans (fst_pair b.pos b.neg)
  have hn : Γ ⊢[PRAAx] sndT (sndT (encode a b)) ≐ b.neg :=
    (congrSnd (snd_pair (code a) (code b))).eqTrans (snd_pair b.pos b.neg)
  apply ZT.derive
  simp only [second,decode,ZT.toZ]
  rw [natEq hp,natEq hn]

theorem first_value (a b : ZT n) : ZT.toZ Γ (first (encode a b)) = ZT.toZ Γ a := ZT.toZ_eq (first_encode a b)
theorem second_value (a b : ZT n) : ZT.toZ Γ (second (encode a b)) = ZT.toZ Γ b := ZT.toZ_eq (second_encode a b)

theorem parts_value (a : ZT n) : ZT.toZ Γ a = 𝔞(positivePart a)-𝔞(negativePart a) := by
  have h := natEq (monus_max (Γ := Γ) a.pos a.neg)
  simp only [ZT.toZ,positivePart,negativePart]
  ipra_simps
  linear_combination -h
theorem parts_disjoint (a : ZT n) : Γ ⊢[PRAAx] (positivePart a ≐ zero) ⋎ (negativePart a ≐ zero) := by
  refine .orE (le_total a.pos a.neg) (.orI₁ Prf.hyp0) (.orI₂ Prf.hyp0)
theorem parts_product (a : ZT n) : Γ ⊢[PRAAx] positivePart a*negativePart a ≐ zero := monus_mul _ _

theorem multiply_first (d x y : PTm n) : ZT.toZ Γ (first (multiply d x y)) =
    ZT.toZ Γ (first x)*ZT.toZ Γ (first y)+𝔞(d)*(ZT.toZ Γ (second x)*ZT.toZ Γ (second y)) := by
  simp only [multiply,first_value,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
theorem multiply_second (d x y : PTm n) : ZT.toZ Γ (second (multiply d x y)) =
    ZT.toZ Γ (first x)*ZT.toZ Γ (second y)+ZT.toZ Γ (second x)*ZT.toZ Γ (first y) := by
  rw [multiply,second_value,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_mul]
theorem negative_first (x : PTm n) : ZT.toZ Γ (first (negative x)) = -ZT.toZ Γ (first x) := by rw [negative,first_value,ZT.toZ_neg]
theorem negative_second (x : PTm n) : ZT.toZ Γ (second (negative x)) = -ZT.toZ Γ (second x) := by rw [negative,second_value,ZT.toZ_neg]

theorem multiplier_zero (x : PTm n) (h : Γ ⊢[PRAAx] mass x ≐ zero) : Γ ⊢[PRAAx] multiplier x ≐ oneCode :=
  Foundations.GuardedTotalization.sel_one (eqb_of_eq h)
theorem multiplier_nonzero (x : PTm n) (h : Γ ⊢[PRAAx] le one (mass x)) : Γ ⊢[PRAAx]
    multiplier x ≐ naturalPair (magnitude (first x)) (magnitude (second x)) :=
  Foundations.GuardedTotalization.sel_zero (eqb_of_ne (by
    refine .impI ?_
    exact succ_ne_zero' _ ((monus_zero one).eqSymm.eqTrans (le_congr (.eqRefl _) Prf.hyp0 h.wk))))

theorem cone_of_values (x a b : PTm n) (ha : ZT.toZ Γ (first x) = 𝔞(a))
    (hb : ZT.toZ Γ (second x) = 𝔞(b)) (h : Γ ⊢[PRAAx] le one (a+b)) : Γ ⊢[PRAAx] cone x := by
  refine .andI ?_ (.andI ?_ ?_)
  · exact zle_of_comb (𝔞(a)) (by rw [ha,ZT.toZ_ofNat]; ipra_simps; ring) (nn_term a)
  · exact zle_of_comb (𝔞(b)) (by rw [hb,ZT.toZ_ofNat]; ipra_simps; ring) (nn_term b)
  · apply zle_of_comb (𝔞(a+b)-1) _ (by simpa only [sl_def,Q.mk_one,map_one] using nn_sl h)
    rw [ZT.toZ_add,ha,hb,ZT.toZ_ofNat]
    ipra_simps
    ring

theorem cone_natural (a b : PTm n) (h : Γ ⊢[PRAAx] le one (a+b)) : Γ ⊢[PRAAx] cone (naturalPair a b) :=
  cone_of_values _ a b (by rw [naturalPair,first_value,ZT.toZ_ofNat]) (by rw [naturalPair,second_value,ZT.toZ_ofNat]) h
theorem cone_code_congr {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ y) (hx : Γ ⊢[PRAAx] cone x) : Γ ⊢[PRAAx] cone y := by
  simpa only [subst_cone,Syn.subst_var,Matrix.cons_val_zero] using
    Prf.eqSubst (cone (var 0) : Fm PTm 1) ![x] ![y] (fun i => by fin_cases i; exact h)
      (by simpa only [subst_cone,Syn.subst_var,Matrix.cons_val_zero] using hx)

theorem multiplier_cone (x : PTm n) : Γ ⊢[PRAAx] cone (multiplier x) := by
  refine .orE (zero_or_succ (mass x)) ?_ ?_
  · have e := multiplier_zero (Γ := (mass x ≐ zero)::Γ) x Prf.hyp0
    have h : (mass x ≐ zero)::Γ ⊢[PRAAx] cone oneCode := cone_natural one zero (le_congr (.eqRefl _) (add_zero _).eqSymm (le_refl _))
    exact cone_code_congr e.eqSymm h
  · let Δ := (mass x ≐ succ (PTm.pred (mass x))) :: Γ
    have positive : Δ ⊢[PRAAx] le one (mass x) := le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    have h := cone_natural (magnitude (first x)) (magnitude (second x)) positive
    have e := multiplier_nonzero x positive
    exact cone_code_congr e.eqSymm h


theorem first_code_value {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ y) : ZT.toZ Γ (first x) = ZT.toZ Γ (first y) := by
  simp only [first,decode,ZT.toZ]
  rw [natEq (congrFst (congrFst h)),natEq (congrSnd (congrFst h))]
theorem second_code_value {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ y) : ZT.toZ Γ (second x) = ZT.toZ Γ (second y) := by
  simp only [second,decode,ZT.toZ]
  rw [natEq (congrFst (congrSnd h)),natEq (congrSnd (congrSnd h))]

def aligned (x : PTm n) : Fm PTm n :=
  (zle (ZT.ofNat zero) (first x) ⋏ zle (ZT.ofNat zero) (second x)) ⋎
    (zle (first x) (ZT.ofNat zero) ⋏ zle (second x) (ZT.ofNat zero))
@[simp] theorem subst_aligned {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) :
    (aligned x).subst σ = aligned (Syn.subst σ x) := by simp [aligned]

theorem nonnegative_of_value (a : ZT n) (h : Nonneg Γ (ZT.toZ Γ a)) : Γ ⊢[PRAAx] zle (ZT.ofNat zero) a :=
  zle_of_comb (ZT.toZ Γ a) (by simp only [ZT.toZ_ofNat,Q.mk_zero,map_zero,_root_.sub_zero]) h
theorem nonpositive_of_value (a : ZT n) (h : Nonneg Γ (-ZT.toZ Γ a)) : Γ ⊢[PRAAx] zle a (ZT.ofNat zero) :=
  zle_of_comb (-ZT.toZ Γ a) (by simp only [ZT.toZ_ofNat,Q.mk_zero,map_zero,_root_.zero_sub]) h
theorem integer_sign_cases (a : ZT n) : Γ ⊢[PRAAx] zle (ZT.ofNat zero) a ⋎ zle a (ZT.ofNat zero) := by
  refine .orE (le_total a.neg a.pos) (.orI₁ ?_) (.orI₂ ?_)
  · exact le_congr (zero_add _).eqSymm (add_zero _).eqSymm Prf.hyp0
  · exact le_congr (add_zero _).eqSymm (zero_add _).eqSymm Prf.hyp0

theorem aligned_scalar (x : PTm n) (h : ZT.toZ Γ (second x) = 0) : Γ ⊢[PRAAx] aligned x := by
  have hp : Γ ⊢[PRAAx] zle (ZT.ofNat zero) (second x) := nonnegative_of_value _ (h.symm ▸ nn_zero)
  have hn : Γ ⊢[PRAAx] zle (second x) (ZT.ofNat zero) := nonpositive_of_value _ (by rw [h]; exact nn_zero)
  exact .orE (integer_sign_cases (first x)) (.orI₁ (.andI Prf.hyp0 hp.wk)) (.orI₂ (.andI Prf.hyp0 hn.wk))

theorem absolute_product_aligned (d x : PTm n) : Γ ⊢[PRAAx]
    aligned (multiply d (naturalPair (magnitude (first x)) (magnitude (second x))) x) := by
  refine .orE (parts_disjoint (first x)) ?_ ?_
  · refine .orE (parts_disjoint (second x)) ?_ ?_
    · let Δ := (positivePart (second x) ≐ zero) :: (positivePart (first x) ≐ zero) :: Γ
      have f : ZT.toZ Δ (first (multiply d (naturalPair (magnitude (first x)) (magnitude (second x))) x)) =
          -Groth.ι (Q.mk Δ (negativePart (first x)*negativePart (first x)+d*(negativePart (second x)*negativePart (second x)))) := by
        rw [multiply_first]
        simp only [naturalPair,first_value,second_value,ZT.toZ_ofNat]
        rw [parts_value (first x),parts_value (second x)]
        unfold magnitude
        ipra_simps
        rw [natEq (Prf.hyp1 : Δ ⊢[PRAAx] _),natEq (Prf.hyp0 : Δ ⊢[PRAAx] _)]
        ipra_simps
        ring
      have g : ZT.toZ Δ (second (multiply d (naturalPair (magnitude (first x)) (magnitude (second x))) x)) =
          -Groth.ι (Q.mk Δ (two*negativePart (first x)*negativePart (second x))) := by
        rw [multiply_second]
        simp only [naturalPair,first_value,second_value,ZT.toZ_ofNat]
        rw [parts_value (first x),parts_value (second x)]
        unfold magnitude
        ipra_simps
        rw [natEq (Prf.hyp1 : Δ ⊢[PRAAx] _),natEq (Prf.hyp0 : Δ ⊢[PRAAx] _)]
        ipra_simps
        ring
      exact .orI₂ (.andI (nonpositive_of_value _ (by rw [f,_root_.neg_neg]; exact nn_term _))
        (nonpositive_of_value _ (by rw [g,_root_.neg_neg]; exact nn_term _)))
    · let Δ := (negativePart (second x) ≐ zero) :: (positivePart (first x) ≐ zero) :: Γ
      apply aligned_scalar
      rw [multiply_second]
      simp only [naturalPair,first_value,second_value,ZT.toZ_ofNat]
      rw [parts_value (first x),parts_value (second x)]
      unfold magnitude
      ipra_simps
      rw [natEq (Prf.hyp1 : Δ ⊢[PRAAx] _),natEq (Prf.hyp0 : Δ ⊢[PRAAx] _)]
      ipra_simps
      ring
  · refine .orE (parts_disjoint (second x)) ?_ ?_
    · let Δ := (positivePart (second x) ≐ zero) :: (negativePart (first x) ≐ zero) :: Γ
      apply aligned_scalar
      rw [multiply_second]
      simp only [naturalPair,first_value,second_value,ZT.toZ_ofNat]
      rw [parts_value (first x),parts_value (second x)]
      unfold magnitude
      ipra_simps
      rw [natEq (Prf.hyp1 : Δ ⊢[PRAAx] _),natEq (Prf.hyp0 : Δ ⊢[PRAAx] _)]
      ipra_simps
      ring
    · let Δ := (negativePart (second x) ≐ zero) :: (negativePart (first x) ≐ zero) :: Γ
      have f : ZT.toZ Δ (first (multiply d (naturalPair (magnitude (first x)) (magnitude (second x))) x)) =
          Groth.ι (Q.mk Δ (positivePart (first x)*positivePart (first x)+d*(positivePart (second x)*positivePart (second x)))) := by
        rw [multiply_first]
        simp only [naturalPair,first_value,second_value,ZT.toZ_ofNat]
        rw [parts_value (first x),parts_value (second x)]
        unfold magnitude
        ipra_simps
        rw [natEq (Prf.hyp1 : Δ ⊢[PRAAx] _),natEq (Prf.hyp0 : Δ ⊢[PRAAx] _)]
        ipra_simps
        ring
      have g : ZT.toZ Δ (second (multiply d (naturalPair (magnitude (first x)) (magnitude (second x))) x)) =
          Groth.ι (Q.mk Δ (two*positivePart (first x)*positivePart (second x))) := by
        rw [multiply_second]
        simp only [naturalPair,first_value,second_value,ZT.toZ_ofNat]
        rw [parts_value (first x),parts_value (second x)]
        unfold magnitude
        ipra_simps
        rw [natEq (Prf.hyp1 : Δ ⊢[PRAAx] _),natEq (Prf.hyp0 : Δ ⊢[PRAAx] _)]
        ipra_simps
        ring
      exact .orI₁ (.andI (nonnegative_of_value _ (f.symm ▸ nn_term _)) (nonnegative_of_value _ (g.symm ▸ nn_term _)))


theorem multiply_code_congr {d e x y z w : PTm n} (hd : Γ ⊢[PRAAx] d ≐ e)
    (hx : Γ ⊢[PRAAx] x ≐ y) (hz : Γ ⊢[PRAAx] z ≐ w) : Γ ⊢[PRAAx] multiply d x z ≐ multiply e y w := by
  ipra_congr (multiply (var 0) (var 1) (var 2) : PTm 3) with [hd, hx, hz]
theorem aligned_code_congr {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ y) (hx : Γ ⊢[PRAAx] aligned x) : Γ ⊢[PRAAx] aligned y := by
  simpa only [subst_aligned,Syn.subst_var,Matrix.cons_val_zero] using
    Prf.eqSubst (aligned (var 0) : Fm PTm 1) ![x] ![y] (fun i => by fin_cases i; exact h)
      (by simpa only [subst_aligned,Syn.subst_var,Matrix.cons_val_zero] using hx)
theorem zero_of_bounded_mass (x a : PTm n) (h : Γ ⊢[PRAAx] mass x ≐ zero) (ha : Γ ⊢[PRAAx] le a (mass x)) : Γ ⊢[PRAAx] a ≐ zero :=
  le_antisymm (le_congr (.eqRefl _) h ha) (zero_le _)
theorem mass_zero_values (x : PTm n) (h : Γ ⊢[PRAAx] mass x ≐ zero) :
    ZT.toZ Γ (first x) = 0 ∧ ZT.toZ Γ (second x) = 0 := by
  have ap := natEq (zero_of_bounded_mass x (positivePart (first x)) h (le_trans (le_add_right _ _) (le_add_right _ _)))
  have am := natEq (zero_of_bounded_mass x (negativePart (first x)) h (le_trans (le_add_left _ _) (le_add_right _ _)))
  have bp := natEq (zero_of_bounded_mass x (positivePart (second x)) h (le_trans (le_add_right _ _) (le_add_left _ _)))
  have bm := natEq (zero_of_bounded_mass x (negativePart (second x)) h (le_trans (le_add_left _ _) (le_add_left _ _)))
  constructor
  · rw [parts_value,ap,am]; ipra_simps; ring
  · rw [parts_value,bp,bm]; ipra_simps; ring

theorem product_aligned (d x : PTm n) : Γ ⊢[PRAAx] aligned (product d x) := by
  refine .orE (zero_or_succ (mass x)) ?_ ?_
  · let Δ := (mass x ≐ zero)::Γ
    have v := mass_zero_values (Γ := Δ) x Prf.hyp0
    apply aligned_scalar
    rw [product,multiply_second,v.1,v.2]
    ring
  · let Δ := (mass x ≐ succ (PTm.pred (mass x)))::Γ
    have pos : Δ ⊢[PRAAx] le one (mass x) := le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    exact aligned_code_congr (multiply_code_congr (.eqRefl _) (multiplier_nonzero x pos) (.eqRefl _)).eqSymm
      (absolute_product_aligned d x)

theorem negative_part_zero (a : ZT n) (h : Γ ⊢[PRAAx] zle (ZT.ofNat zero) a) : Γ ⊢[PRAAx] negativePart a ≐ zero :=
  le_congr (zero_add _) (add_zero _) h
theorem positive_part_zero (a : ZT n) (h : Γ ⊢[PRAAx] zle a (ZT.ofNat zero)) : Γ ⊢[PRAAx] positivePart a ≐ zero :=
  le_congr (add_zero _) (zero_add _) h
theorem nonnegative_sum (a b : ZT n) (ha : Γ ⊢[PRAAx] zle (ZT.ofNat zero) a)
    (hb : Γ ⊢[PRAAx] zle (ZT.ofNat zero) b) : Γ ⊢[PRAAx] zle (ZT.ofNat zero) (a+b) :=
  nonnegative_of_value _ (by rw [ZT.toZ_add]; exact nn_add (nn_zle0 ha) (nn_zle0 hb))
theorem nonpositive_sum (a b : ZT n) (ha : Γ ⊢[PRAAx] zle a (ZT.ofNat zero))
    (hb : Γ ⊢[PRAAx] zle b (ZT.ofNat zero)) : Γ ⊢[PRAAx] zle (a+b) (ZT.ofNat zero) := by
  have na : Nonneg Γ (-ZT.toZ Γ a) := by simpa only [zsl_def,ZT.toZ_ofNat,Q.mk_zero,map_zero,_root_.zero_sub] using nn_zsl ha
  have nb : Nonneg Γ (-ZT.toZ Γ b) := by simpa only [zsl_def,ZT.toZ_ofNat,Q.mk_zero,map_zero,_root_.zero_sub] using nn_zsl hb
  exact nonpositive_of_value _ (by rw [ZT.toZ_add,_root_.neg_add]; exact nn_add na nb)

theorem parts_zero_value (a : ZT n) (hp : Γ ⊢[PRAAx] positivePart a ≐ zero)
    (hn : Γ ⊢[PRAAx] negativePart a ≐ zero) : ZT.toZ Γ a = 0 := by
  rw [parts_value,natEq hp,natEq hn]; ipra_simps; ring

theorem nonnegative_pair_zero (x : PTm n) (ha : Γ ⊢[PRAAx] zle (ZT.ofNat zero) (first x))
    (hb : Γ ⊢[PRAAx] zle (ZT.ofNat zero) (second x))
    (h : ZT.toZ Γ (first x+second x) = 0) : Γ ⊢[PRAAx] equal x zeroCode := by
  obtain ⟨a,ea⟩ := nn_zle0 ha
  obtain ⟨b,eb⟩ := nn_zle0 hb
  have sum : Γ ⊢[PRAAx] a+b ≐ zero := by
    apply deriveNat
    ipra_simps
    rw [← ea,← eb]
    exact h
  have az : Γ ⊢[PRAAx] a ≐ zero := le_antisymm (le_congr (.eqRefl _) sum (le_add_right _ _)) (zero_le _)
  have bz : Γ ⊢[PRAAx] b ≐ zero := le_antisymm (le_congr (.eqRefl _) sum (le_add_left _ _)) (zero_le _)
  refine .andI (ZT.derive ?_) (ZT.derive ?_)
  · rw [zeroCode,first_value,ZT.toZ_ofNat,ea,natEq az]
  · rw [zeroCode,second_value,ZT.toZ_ofNat,eb,natEq bz]


theorem nonpositive_pair_zero (x : PTm n) (ha : Γ ⊢[PRAAx] zle (first x) (ZT.ofNat zero))
    (hb : Γ ⊢[PRAAx] zle (second x) (ZT.ofNat zero))
    (h : ZT.toZ Γ (first x+second x) = 0) : Γ ⊢[PRAAx] equal x zeroCode := by
  have na : Nonneg Γ (-ZT.toZ Γ (first x)) := by simpa only [zsl_def,ZT.toZ_ofNat,Q.mk_zero,map_zero,_root_.zero_sub] using nn_zsl ha
  have nb : Nonneg Γ (-ZT.toZ Γ (second x)) := by simpa only [zsl_def,ZT.toZ_ofNat,Q.mk_zero,map_zero,_root_.zero_sub] using nn_zsl hb
  obtain ⟨a,ea⟩ := na
  obtain ⟨b,eb⟩ := nb
  have sum : Γ ⊢[PRAAx] a+b ≐ zero := by
    apply deriveNat
    ipra_simps
    rw [← ea,← eb]
    linear_combination -h
  have az : Γ ⊢[PRAAx] a ≐ zero := le_antisymm (le_congr (.eqRefl _) sum (le_add_right _ _)) (zero_le _)
  have bz : Γ ⊢[PRAAx] b ≐ zero := le_antisymm (le_congr (.eqRefl _) sum (le_add_left _ _)) (zero_le _)
  refine .andI (ZT.derive ?_) (ZT.derive ?_)
  · rw [zeroCode,first_value,ZT.toZ_ofNat]
    have h := ea.trans (natEq az)
    ipra_simps
    linear_combination -h
  · rw [zeroCode,second_value,ZT.toZ_ofNat]
    have h := eb.trans (natEq bz)
    ipra_simps
    linear_combination -h

def tag (a : ZT n) : PTm n := Signum.sg (positivePart a)+two*Signum.sg (negativePart a)
def classification (x : PTm n) : Fm PTm n :=
  ((tag (first x+second x) ≐ one) ⋏ cone x) ⋎
    (((tag (first x+second x) ≐ two) ⋏ cone (negative x)) ⋎
      ((tag (first x+second x) ≐ zero) ⋏ equal x zeroCode))
@[simp] theorem subst_tag {l : ℕ} (σ : Fin n → PTm l) (a : ZT n) :
    Syn.subst σ (tag a) = tag (a.subst σ) := by simp [tag,Signum.sg]
@[simp] theorem subst_classification {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) :
    (classification x).subst σ = classification (Syn.subst σ x) := by simp [classification]

theorem tag_positive (a : ZT n) (hp : Γ ⊢[PRAAx] positivePart a ≐ succ (PTm.pred (positivePart a)))
    (hn : Γ ⊢[PRAAx] negativePart a ≐ zero) : Γ ⊢[PRAAx] tag a ≐ one := by
  have p := natEq ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hp)).eqTrans (Signum.sg_succ _))
  have q := natEq ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hn)).eqTrans Signum.sg_zero)
  apply deriveNat
  unfold tag
  ipra_simps
  rw [p,q]
  ring

theorem tag_negative (a : ZT n) (hp : Γ ⊢[PRAAx] positivePart a ≐ zero)
    (hn : Γ ⊢[PRAAx] negativePart a ≐ succ (PTm.pred (negativePart a))) : Γ ⊢[PRAAx] tag a ≐ two := by
  have p := natEq ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hp)).eqTrans Signum.sg_zero)
  have q := natEq ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hn)).eqTrans (Signum.sg_succ _))
  apply deriveNat
  unfold tag
  ipra_simps
  rw [p,q]
  ring

theorem tag_zero (a : ZT n) (hp : Γ ⊢[PRAAx] positivePart a ≐ zero)
    (hn : Γ ⊢[PRAAx] negativePart a ≐ zero) : Γ ⊢[PRAAx] tag a ≐ zero := by
  have p := natEq ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hp)).eqTrans Signum.sg_zero)
  have q := natEq ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hn)).eqTrans Signum.sg_zero)
  apply deriveNat
  unfold tag
  ipra_simps
  rw [p,q]
  ring

theorem cone_positive (x : PTm n) (ha : Γ ⊢[PRAAx] zle (ZT.ofNat zero) (first x))
    (hb : Γ ⊢[PRAAx] zle (ZT.ofNat zero) (second x))
    (hp : Γ ⊢[PRAAx] le one (positivePart (first x+second x))) : Γ ⊢[PRAAx] cone x := by
  refine .andI ha (.andI hb ?_)
  have hn := natEq (negative_part_zero _ (nonnegative_sum (first x) (second x) ha hb))
  apply zle_of_comb (𝔞(positivePart (first x+second x))-1) _
    (by simpa only [sl_def,Q.mk_one,map_one] using nn_sl hp)
  rw [ZT.toZ_ofNat,parts_value]
  rw [hn]
  ipra_simps
  ring

theorem cone_negative (x : PTm n) (ha : Γ ⊢[PRAAx] zle (first x) (ZT.ofNat zero))
    (hb : Γ ⊢[PRAAx] zle (second x) (ZT.ofNat zero))
    (hn : Γ ⊢[PRAAx] le one (negativePart (first x+second x))) : Γ ⊢[PRAAx] cone (negative x) := by
  have na : Nonneg Γ (-ZT.toZ Γ (first x)) := by simpa only [zsl_def,ZT.toZ_ofNat,Q.mk_zero,map_zero,_root_.zero_sub] using nn_zsl ha
  have nb : Nonneg Γ (-ZT.toZ Γ (second x)) := by simpa only [zsl_def,ZT.toZ_ofNat,Q.mk_zero,map_zero,_root_.zero_sub] using nn_zsl hb
  refine .andI (nonnegative_of_value _ (by rw [negative_first]; exact na))
    (.andI (nonnegative_of_value _ (by rw [negative_second]; exact nb)) ?_)
  have hp := natEq (positive_part_zero _ (nonpositive_sum (first x) (second x) ha hb))
  apply zle_of_comb (𝔞(negativePart (first x+second x))-1) _
    (by simpa only [sl_def,Q.mk_one,map_one] using nn_sl hn)
  rw [ZT.toZ_add,negative_first,negative_second,ZT.toZ_ofNat]
  have sum := parts_value (Γ := Γ) (first x+second x)
  rw [ZT.toZ_add,hp] at sum
  ipra_simps
  linear_combination -sum

theorem aligned_classification (x : PTm n) (h : Γ ⊢[PRAAx] aligned x) : Γ ⊢[PRAAx] classification x := by
  refine .orE (zero_or_succ (positivePart (first x+second x))) ?_ ?_
  · refine .orE (zero_or_succ (negativePart (first x+second x))) ?_ ?_
    · let Δ := (negativePart (first x+second x) ≐ zero) :: (positivePart (first x+second x) ≐ zero) :: Γ
      have zero := parts_zero_value (Γ := Δ) (first x+second x) Prf.hyp1 Prf.hyp0
      have ze : Δ ⊢[PRAAx] ZT.eq (first x+second x) (ZT.ofNat PTm.zero) := by
        apply ZT.derive
        simpa only [ZT.toZ_ofNat,Q.mk_zero,map_zero] using zero
      have eq : Δ ⊢[PRAAx] equal x zeroCode := .orE h.wk.wk
        (nonnegative_pair_zero x (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0) (by simpa only [ZT.toZ_ofNat,Q.mk_zero,map_zero] using ZT.toZ_eq ze.wk))
        (nonpositive_pair_zero x (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0) (by simpa only [ZT.toZ_ofNat,Q.mk_zero,map_zero] using ZT.toZ_eq ze.wk))
      exact .orI₂ (.orI₂ (.andI (tag_zero _ Prf.hyp1 Prf.hyp0) eq))
    · let Δ := (negativePart (first x+second x) ≐ succ (PTm.pred (negativePart (first x+second x)))) ::
          (positivePart (first x+second x) ≐ zero) :: Γ
      refine .orE h.wk.wk ?_ ?_
      · have z := negative_part_zero _ (nonnegative_sum (first x) (second x) (.andE₁ (Prf.hyp0 (Γ := Δ))) (.andE₂ Prf.hyp0))
        exact succ_ne_zero' _ (Prf.hyp1.eqSymm.eqTrans z)
      · have hn : (zle (first x) (ZT.ofNat zero) ⋏ zle (second x) (ZT.ofNat zero))::Δ ⊢[PRAAx] le one (negativePart (first x+second x)) := le_congr (.eqRefl _) Prf.hyp1.eqSymm (zero_lt_succ _)
        exact .orI₂ (.orI₁ (.andI (tag_negative _ Prf.hyp0.wk.wk Prf.hyp1)
          (cone_negative x (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0) hn)))
  · let Δ := (positivePart (first x+second x) ≐ succ (PTm.pred (positivePart (first x+second x)))) :: Γ
    refine .orE h.wk ?_ ?_
    · have hn := negative_part_zero _ (nonnegative_sum (first x) (second x) (.andE₁ (Prf.hyp0 (Γ := Δ))) (.andE₂ Prf.hyp0))
      have hp : (zle (ZT.ofNat zero) (first x) ⋏ zle (ZT.ofNat zero) (second x))::Δ ⊢[PRAAx] le one (positivePart (first x+second x)) := le_congr (.eqRefl _) Prf.hyp1.eqSymm (zero_lt_succ _)
      exact .orI₁ (.andI (tag_positive _ Prf.hyp1 hn) (cone_positive x (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0) hp))
    · have z := positive_part_zero _ (nonpositive_sum (first x) (second x) (.andE₁ (Prf.hyp0 (Γ := Δ))) (.andE₂ Prf.hyp0))
      exact succ_ne_zero' _ (Prf.hyp1.eqSymm.eqTrans z)

theorem sign_certificate (d x : PTm n) : Γ ⊢[PRAAx] cone (multiplier x) ⋏ classification (product d x) :=
  .andI (multiplier_cone x) (aligned_classification _ (product_aligned d x))


def certificate (d x : PTm n) : Fm PTm n := cone (multiplier x) ⋏
  (((sign d x ≐ one) ⋏ cone (product d x)) ⋎
    (((sign d x ≐ two) ⋏ cone (negative (product d x))) ⋎
      ((sign d x ≐ zero) ⋏ equal (product d x) zeroCode)))
@[simp] theorem subst_certificate {l : ℕ} (σ : Fin n → PTm l) (d x : PTm n) :
    (certificate d x).subst σ = certificate (Syn.subst σ d) (Syn.subst σ x) := by simp [certificate]
theorem actual_certificate (d x : PTm n) : Γ ⊢[PRAAx] certificate d x := sign_certificate d x

theorem zero_first_value : ZT.toZ Γ (first (zeroCode : PTm n)) = 0 := by
  change ZT.toZ Γ (first (encode (ZT.ofNat zero) (ZT.ofNat zero))) = 0
  rw [first_value,ZT.toZ_ofNat]
  ipra_simps
theorem zero_second_value : ZT.toZ Γ (second (zeroCode : PTm n)) = 0 := by
  change ZT.toZ Γ (second (encode (ZT.ofNat zero) (ZT.ofNat zero))) = 0
  rw [second_value,ZT.toZ_ofNat]
  ipra_simps

theorem cone_not_zero (x : PTm n) (h : Γ ⊢[PRAAx] cone x) : Γ ⊢[PRAAx] neg (equal x zeroCode) := by
  refine .impI ?_
  let Δ := equal x zeroCode :: Γ
  have ea : ZT.toZ Δ (first x) = 0 := (ZT.toZ_eq (.andE₁ (Prf.hyp0 : Δ ⊢[PRAAx] equal x zeroCode))).trans zero_first_value
  have eb : ZT.toZ Δ (second x) = 0 := (ZT.toZ_eq (.andE₂ (Prf.hyp0 : Δ ⊢[PRAAx] equal x zeroCode))).trans zero_second_value
  have hc : Δ ⊢[PRAAx] cone x := h.wk
  have bad : Nonneg Δ (-1) := by
    have pos := nn_zsl (.andE₂ (.andE₂ hc))
    rw [zsl_def,ZT.toZ_add,ea,eb,ZT.toZ_ofNat] at pos
    simpa only [Q.mk_one,map_one,_root_.zero_add,_root_.zero_sub] using pos
  exact false_of_comb (-1) rfl bad _


def norm (d x : PTm n) : ZT n := first x*first x-ZT.ofNat d*(second x*second x)
@[simp] theorem subst_norm {l : ℕ} (σ : Fin n → PTm l) (d x : PTm n) :
    (norm d x).subst σ = norm (Syn.subst σ d) (Syn.subst σ x) := by simp [norm]
theorem magnitude_nonnegative (a : ZT n) (h : Γ ⊢[PRAAx] zle (ZT.ofNat zero) a) : 𝔞(magnitude a) = ZT.toZ Γ a := by
  rw [parts_value]
  unfold magnitude
  ipra_simps
  rw [natEq (negative_part_zero a h)]
  ipra_simps
  ring
theorem magnitude_nonpositive (a : ZT n) (h : Γ ⊢[PRAAx] zle a (ZT.ofNat zero)) : 𝔞(magnitude a) = -ZT.toZ Γ a := by
  rw [parts_value]
  unfold magnitude
  ipra_simps
  rw [natEq (positive_part_zero a h)]
  ipra_simps
  ring

theorem positive_opposite_conjugation (d x : PTm n) (ha : Γ ⊢[PRAAx] zle (ZT.ofNat zero) (first x))
    (hb : Γ ⊢[PRAAx] zle (second x) (ZT.ofNat zero)) : Γ ⊢[PRAAx]
    equal (multiply d (naturalPair (magnitude (first x)) (magnitude (second x))) x) (encode (norm d x) (ZT.ofNat zero)) := by
  refine .andI (ZT.derive ?_) (ZT.derive ?_)
  · rw [multiply_first,first_value]
    simp only [naturalPair,first_value,second_value,ZT.toZ_ofNat,norm,ZT.toZ_sub,ZT.toZ_mul]
    rw [magnitude_nonnegative _ ha,magnitude_nonpositive _ hb]
    ring
  · rw [multiply_second,second_value]
    simp only [naturalPair,first_value,second_value,ZT.toZ_ofNat]
    rw [magnitude_nonnegative _ ha,magnitude_nonpositive _ hb]
    ipra_simps
    ring

theorem negative_opposite_conjugation (d x : PTm n) (ha : Γ ⊢[PRAAx] zle (first x) (ZT.ofNat zero))
    (hb : Γ ⊢[PRAAx] zle (ZT.ofNat zero) (second x)) : Γ ⊢[PRAAx]
    equal (multiply d (naturalPair (magnitude (first x)) (magnitude (second x))) x) (encode (-norm d x) (ZT.ofNat zero)) := by
  refine .andI (ZT.derive ?_) (ZT.derive ?_)
  · rw [multiply_first,first_value]
    simp only [naturalPair,first_value,second_value,ZT.toZ_ofNat,norm,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_neg]
    rw [magnitude_nonpositive _ ha,magnitude_nonnegative _ hb]
    ring
  · rw [multiply_second,second_value]
    simp only [naturalPair,first_value,second_value,ZT.toZ_ofNat]
    rw [magnitude_nonpositive _ ha,magnitude_nonnegative _ hb]
    ipra_simps
    ring

def output (d x : PTm n) : PTm n := pairT (multiplier x) (pairT (sign d x) (product d x))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (d x : PTm n) : PTm n := ap2 outputF d x
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (d x : PTm n) :
    Syn.subst σ (output d x) = output (Syn.subst σ d) (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (d x : PTm n) :
    Syn.subst σ (run d x) = run (Syn.subst σ d) (Syn.subst σ x) := by simp [run]
theorem program_at (d x : PTm n) : Γ ⊢[PRAAx] run d x ≐ output d x := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![d,x]
theorem returned_multiplier (d x : PTm n) : Γ ⊢[PRAAx] fstT (run d x) ≐ multiplier x :=
  (congrFst (program_at d x)).eqTrans (fst_pair _ _)
theorem returned_sign (d x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run d x)) ≐ sign d x :=
  (congrFst (congrSnd (program_at d x))).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
theorem returned_product (d x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run d x)) ≐ product d x :=
  (congrSnd (congrSnd (program_at d x))).eqTrans ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))

theorem actual_integer_quadratic_sign_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (certificate (var 0) (var 1)) := closeUniv 2 (actual_certificate _ _)
theorem positive_quadratic_stage_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ certificate (var 0) (var 1)) := closeUniv 2 (.impI (actual_certificate _ _))
theorem actual_cone_multiplier_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (cone (multiplier (var 0))) := closeUniv 1 (multiplier_cone _)
theorem actual_quadratic_product_alignment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (aligned (product (var 0) (var 1))) := closeUniv 2 (product_aligned _ _)
theorem positive_cone_excludes_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (cone (var 0) ⟶ neg (equal (var 0) zeroCode)) := closeUniv 1 (.impI (cone_not_zero _ Prf.hyp0))
theorem actual_quadratic_sign_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem actual_returned_quadratic_fields_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((fstT (run (var 0) (var 1)) ≐ multiplier (var 1)) ⋏
      ((fstT (sndT (run (var 0) (var 1))) ≐ sign (var 0) (var 1)) ⋏
        (sndT (sndT (run (var 0) (var 1))) ≐ multiply (var 0) (multiplier (var 1)) (var 1)))) :=
  closeUniv 2 (.andI (returned_multiplier _ _) (.andI (returned_sign _ _) (returned_product _ _)))


theorem positive_opposite_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (zle (ZT.ofNat zero) (first (var 1)) ⟶ zle (second (var 1)) (ZT.ofNat zero) ⟶
      equal (multiply (var 0) (naturalPair (magnitude (first (var 1))) (magnitude (second (var 1)))) (var 1))
        (encode (norm (var 0) (var 1)) (ZT.ofNat zero))) := closeUniv 2 (.impI (.impI (positive_opposite_conjugation _ _ Prf.hyp1 Prf.hyp0)))
theorem negative_opposite_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (zle (first (var 1)) (ZT.ofNat zero) ⟶ zle (ZT.ofNat zero) (second (var 1)) ⟶
      equal (multiply (var 0) (naturalPair (magnitude (first (var 1))) (magnitude (second (var 1)))) (var 1))
        (encode (-norm (var 0) (var 1)) (ZT.ofNat zero))) := closeUniv 2 (.impI (.impI (negative_opposite_conjugation _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Algebra.QuadraticSignCertificates
