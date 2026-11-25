import IPRADerivations.Core.MultiSums
import IPRADerivations.Core.Pairing
import IPRADerivations.Geometry.Distinct.AnalyticGeometryPolynomialCertificates
import IPRADerivations.Core.LinearCombination

/-!
# Actual coded affine pullback of a binary conic

Source: the analytic geometry packet of 22 November, `con:covariance`
and `con:invariants`. Six signed coefficient pairs and six signed affine
parameters are stored in actual numerical records. The fixed PR pullback
returns the six transformed coefficients. Its decoded evaluation is the
original conic evaluated at the actual affine image, and its discriminant
is multiplied by the square of the actual linear determinant.

This proves the integer coefficient and integer coordinate stage, including
all singular and zero cases. Rational normalization, inverse-coordinate
existence and full conic classification remain separate obligations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Geometry.Distinct.AnalyticConicAffine

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def encode (z : ZT n) : PTm n := pairT z.pos z.neg
def decode (c : PTm n) : ZT n := ⟨fstT c,sndT c⟩
def pack (xs : List (ZT n)) : PTm n := xs.foldr (fun z tail => pairT (encode z) tail) zero
def read : ℕ → PTm n → ZT n
  | 0,c => decode (fstT c)
  | k+1,c => read k (sndT c)
def pack6 (a b c d e f : ZT n) : PTm n := pack [a,b,c,d,e,f]

@[simp] theorem subst_encode {m : ℕ} (σ : Fin n → PTm m) (z : ZT n) :
    Syn.subst σ (encode z) = encode (z.subst σ) := by simp [encode,ZT.subst]
@[simp] theorem subst_decode {m : ℕ} (σ : Fin n → PTm m) (c : PTm n) :
    (decode c).subst σ = decode (Syn.subst σ c) := by simp [decode,ZT.subst]
@[simp] theorem subst_read {m : ℕ} (σ : Fin n → PTm m) (k : ℕ) (c : PTm n) :
    (read k c).subst σ = read k (Syn.subst σ c) := by
  induction k generalizing c with
  | zero => simp [read]
  | succ k ih => simp [read,ih]
@[simp] theorem subst_pack6 {m : ℕ} (σ : Fin n → PTm m) (a b c d e f : ZT n) :
    Syn.subst σ (pack6 a b c d e f) = pack6 (a.subst σ) (b.subst σ) (c.subst σ) (d.subst σ) (e.subst σ) (f.subst σ) := by
  simp [pack6,pack]

theorem decode_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    ZT.toZ Γ (decode a) = ZT.toZ Γ (decode b) := by
  simp only [decode,ZT.toZ]
  rw [natEq (congrFst h),natEq (congrSnd h)]
theorem decode_encode (z : ZT n) : ZT.toZ Γ (decode (encode z)) = ZT.toZ Γ z := by
  simp only [decode,encode,ZT.toZ]
  rw [natEq (fst_pair _ _),natEq (snd_pair _ _)]
theorem read_congr (k : ℕ) {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    ZT.toZ Γ (read k a) = ZT.toZ Γ (read k b) := by
  induction k generalizing a b with
  | zero => exact decode_congr (congrFst h)
  | succ k ih => exact ih (congrSnd h)

theorem read_pack (xs : List (ZT n)) (k : ℕ) (h : k < xs.length) :
    ZT.toZ Γ (read k (pack xs)) = ZT.toZ Γ xs[k] := by
  induction xs generalizing k with
  | nil => simp at h
  | cons z xs ih =>
    cases k with
    | zero => exact (decode_congr (fst_pair (encode z) (pack xs))).trans (decode_encode z)
    | succ k => exact (read_congr k (snd_pair (encode z) (pack xs))).trans (ih k (by simpa using h))

@[simp] theorem read_pack6_0 (a b c d e f : ZT n) :
    ZT.toZ Γ (read 0 (pack6 a b c d e f)) = ZT.toZ Γ a := by
  exact read_pack [a,b,c,d,e,f] 0 (by simp)

@[simp] theorem read_pack6_1 (a b c d e f : ZT n) :
    ZT.toZ Γ (read 1 (pack6 a b c d e f)) = ZT.toZ Γ b := by
  exact read_pack [a,b,c,d,e,f] 1 (by simp)

@[simp] theorem read_pack6_2 (a b c d e f : ZT n) :
    ZT.toZ Γ (read 2 (pack6 a b c d e f)) = ZT.toZ Γ c := by
  exact read_pack [a,b,c,d,e,f] 2 (by simp)

@[simp] theorem read_pack6_3 (a b c d e f : ZT n) :
    ZT.toZ Γ (read 3 (pack6 a b c d e f)) = ZT.toZ Γ d := by
  exact read_pack [a,b,c,d,e,f] 3 (by simp)

@[simp] theorem read_pack6_4 (a b c d e f : ZT n) :
    ZT.toZ Γ (read 4 (pack6 a b c d e f)) = ZT.toZ Γ e := by
  exact read_pack [a,b,c,d,e,f] 4 (by simp)

@[simp] theorem read_pack6_5 (a b c d e f : ZT n) :
    ZT.toZ Γ (read 5 (pack6 a b c d e f)) = ZT.toZ Γ f := by
  exact read_pack [a,b,c,d,e,f] 5 (by simp)

def evaluate (c : PTm n) (x y : ZT n) : ZT n :=
  read 0 c*x*x+read 1 c*x*y+read 2 c*y*y+read 3 c*x+read 4 c*y+read 5 c
def imageX (m : PTm n) (x y : ZT n) : ZT n := read 0 m*x+read 1 m*y+read 4 m
def imageY (m : PTm n) (x y : ZT n) : ZT n := read 2 m*x+read 3 m*y+read 5 m
def determinant (m : PTm n) : ZT n := read 0 m*read 3 m-read 1 m*read 2 m
def discriminant (c : PTm n) : ZT n := (read 1 c).sq-ZT.natLit 4*read 0 c*read 2 c

/-- Explicitly computed coefficients of q(Mu+t). -/
def pullback (c m : PTm n) : PTm n :=
  let a := read 0 c
  let b := read 1 c
  let cc := read 2 c
  let d := read 3 c
  let e := read 4 c
  let r := read 0 m
  let s := read 1 m
  let u := read 2 m
  let v := read 3 m
  let t := read 4 m
  let w := read 5 m
  pack6 (a*r*r+b*r*u+cc*u*u)
    (ZT.natLit 2*a*r*s+b*(r*v+s*u)+ZT.natLit 2*cc*u*v)
    (a*s*s+b*s*v+cc*v*v)
    (ZT.natLit 2*a*r*t+b*(r*w+u*t)+ZT.natLit 2*cc*u*w+d*r+e*u)
    (ZT.natLit 2*a*s*t+b*(s*w+v*t)+ZT.natLit 2*cc*v*w+d*s+e*v)
    (evaluate c t w)

@[simp] theorem subst_evaluate {m : ℕ} (σ : Fin n → PTm m) (c : PTm n) (x y : ZT n) :
    (evaluate c x y).subst σ = evaluate (Syn.subst σ c) (x.subst σ) (y.subst σ) := by simp [evaluate]
@[simp] theorem subst_imageX {m : ℕ} (σ : Fin n → PTm m) (c : PTm n) (x y : ZT n) :
    (imageX c x y).subst σ = imageX (Syn.subst σ c) (x.subst σ) (y.subst σ) := by simp [imageX]
@[simp] theorem subst_imageY {m : ℕ} (σ : Fin n → PTm m) (c : PTm n) (x y : ZT n) :
    (imageY c x y).subst σ = imageY (Syn.subst σ c) (x.subst σ) (y.subst σ) := by simp [imageY]
@[simp] theorem subst_determinant {m : ℕ} (σ : Fin n → PTm m) (c : PTm n) :
    (determinant c).subst σ = determinant (Syn.subst σ c) := by simp [determinant]
@[simp] theorem subst_discriminant {m : ℕ} (σ : Fin n → PTm m) (c : PTm n) :
    (discriminant c).subst σ = discriminant (Syn.subst σ c) := by simp [discriminant,ZT.sq]
@[simp] theorem subst_pullback {m : ℕ} (σ : Fin n → PTm m) (c p : PTm n) :
    Syn.subst σ (pullback c p) = pullback (Syn.subst σ c) (Syn.subst σ p) := by simp [pullback]

theorem evaluation_covariance (c m : PTm n) (x y : ZT n) : Γ ⊢[PRAAx]
    ZT.eq (evaluate (pullback c m) x y) (evaluate c (imageX m x y) (imageY m x y)) := by
  ipra_lc [evaluate, imageX, imageY, pullback, read_pack6_0, read_pack6_1, read_pack6_2, read_pack6_3, read_pack6_4, read_pack6_5]

theorem discriminant_covariance (c m : PTm n) : Γ ⊢[PRAAx]
    ZT.eq (discriminant (pullback c m)) ((determinant m).sq*discriminant c) := by
  ipra_lc [discriminant, determinant, pullback, read_pack6_0, read_pack6_1, read_pack6_2]

def pullbackF : PR 2 := PTm.toPR (pullback (var 0) (var 1))
def evaluateF : PR 3 := PTm.toPR (encode (evaluate (var 0) (decode (var 1)) (decode (var 2))))

theorem pullback_at (c m : PTm n) : Γ ⊢[PRAAx] ap2 pullbackF c m ≐ pullback c m := by
  simpa only [ap2,pullbackF,subst_pullback,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (pullback (var 0) (var 1) : PTm 2) ![c,m]

theorem evaluate_at (c x y : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluateF c x y ≐ encode (evaluate c (decode x) (decode y)) := by
  simpa only [ap3,evaluateF,subst_encode,subst_evaluate,subst_decode,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (encode (evaluate (var 0) (decode (var 1)) (decode (var 2))) : PTm 3) ![c,x,y]

theorem evaluate_code_congr {c d : PTm n} (h : Γ ⊢[PRAAx] c ≐ d) (x y : ZT n) :
    ZT.toZ Γ (evaluate c x y) = ZT.toZ Γ (evaluate d x y) := by
  simp only [evaluate,ZT.toZ_add,ZT.toZ_mul]
  rw [read_congr 0 h,read_congr 1 h,read_congr 2 h,read_congr 3 h,read_congr 4 h,read_congr 5 h]

theorem evaluated_value (c x y : PTm n) :
    ZT.toZ Γ (decode (ap3 evaluateF c x y)) = ZT.toZ Γ (evaluate c (decode x) (decode y)) :=
  (decode_congr (evaluate_at c x y)).trans (decode_encode _)

def imageF : PR 3 := PTm.toPR (pairT (encode (imageX (var 0) (decode (var 1)) (decode (var 2))))
  (encode (imageY (var 0) (decode (var 1)) (decode (var 2)))))

theorem image_at (m x y : PTm n) : Γ ⊢[PRAAx] ap3 imageF m x y ≐
    pairT (encode (imageX m (decode x) (decode y))) (encode (imageY m (decode x) (decode y))) := by
  simpa only [ap3,imageF,subst_pairT,subst_encode,subst_imageX,subst_imageY,subst_decode,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (pairT (encode (imageX (var 0) (decode (var 1)) (decode (var 2))))
      (encode (imageY (var 0) (decode (var 1)) (decode (var 2)))) : PTm 3) ![m,x,y]

theorem image_x_value (m x y : PTm n) : ZT.toZ Γ (decode (fstT (ap3 imageF m x y))) =
    ZT.toZ Γ (imageX m (decode x) (decode y)) :=
  (decode_congr ((congrFst (image_at m x y)).eqTrans (fst_pair _ _))).trans (decode_encode _)
theorem image_y_value (m x y : PTm n) : ZT.toZ Γ (decode (sndT (ap3 imageF m x y))) =
    ZT.toZ Γ (imageY m (decode x) (decode y)) :=
  (decode_congr ((congrSnd (image_at m x y)).eqTrans (snd_pair _ _))).trans (decode_encode _)

/-- Equality of the two actual returned signed evaluation codes in native
integer value; no raw signed-code eta equality is asserted. -/
theorem actual_evaluation_covariance (c m x y : PTm n) : Γ ⊢[PRAAx]
    ZT.eq (decode (ap3 evaluateF (ap2 pullbackF c m) x y))
      (decode (ap3 evaluateF c (fstT (ap3 imageF m x y)) (sndT (ap3 imageF m x y)))) := by
  apply ZT.derive
  calc
    _ = ZT.toZ Γ (evaluate (ap2 pullbackF c m) (decode x) (decode y)) := evaluated_value _ _ _
    _ = ZT.toZ Γ (evaluate (pullback c m) (decode x) (decode y)) := evaluate_code_congr (pullback_at c m) _ _
    _ = ZT.toZ Γ (evaluate c (imageX m (decode x) (decode y)) (imageY m (decode x) (decode y))) :=
      ZT.toZ_eq (evaluation_covariance c m (decode x) (decode y))
    _ = ZT.toZ Γ (evaluate c (decode (fstT (ap3 imageF m x y))) (decode (sndT (ap3 imageF m x y)))) := by
      simp only [evaluate,ZT.toZ_add,ZT.toZ_mul,image_x_value,image_y_value]
    _ = _ := (evaluated_value _ _ _).symm

theorem actual_discriminant_covariance (c m : PTm n) : Γ ⊢[PRAAx]
    ZT.eq (discriminant (ap2 pullbackF c m)) ((determinant m).sq*discriminant c) := by
  apply ZT.derive
  have old := ZT.toZ_eq (discriminant_covariance (Γ := Γ) c m)
  have code : ZT.toZ Γ (discriminant (ap2 pullbackF c m)) = ZT.toZ Γ (discriminant (pullback c m)) := by
    simp only [discriminant,ZT.toZ_sub,ZT.toZ_sq,ZT.toZ_mul]
    rw [read_congr 0 (pullback_at c m),read_congr 1 (pullback_at c m),read_congr 2 (pullback_at c m)]
  exact code.trans old

theorem actual_zero_locus_iff (c m x y : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (ZT.eq (decode (ap3 evaluateF (ap2 pullbackF c m) x y)) (ZT.natLit 0))
      (ZT.eq (decode (ap3 evaluateF c (fstT (ap3 imageF m x y)) (sndT (ap3 imageF m x y)))) (ZT.natLit 0)) := by
  refine .iffI (.impI ?_) (.impI ?_)
  · apply ZT.derive
    exact (ZT.toZ_eq (actual_evaluation_covariance c m x y)).symm.trans (ZT.toZ_eq Prf.hyp0)
  · apply ZT.derive
    exact (ZT.toZ_eq (actual_evaluation_covariance c m x y)).trans (ZT.toZ_eq Prf.hyp0)

theorem actual_conic_affine_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ZT.eq (decode (ap3 evaluateF (ap2 pullbackF (var 0) (var 1)) (var 2) (var 3)))
      (decode (ap3 evaluateF (var 0) (fstT (ap3 imageF (var 1) (var 2) (var 3)))
        (sndT (ap3 imageF (var 1) (var 2) (var 3)))))) :=
  closeUniv 4 (actual_evaluation_covariance _ _ _ _)

theorem actual_conic_discriminant_covariance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ZT.eq (discriminant (ap2 pullbackF (var 0) (var 1))) ((determinant (var 1)).sq*discriminant (var 0))) :=
  closeUniv 2 (actual_discriminant_covariance _ _)

theorem actual_conic_affine_zero_locus_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Fm.iff (ZT.eq (decode (ap3 evaluateF (ap2 pullbackF (var 0) (var 1)) (var 2) (var 3))) (ZT.natLit 0))
      (ZT.eq (decode (ap3 evaluateF (var 0) (fstT (ap3 imageF (var 1) (var 2) (var 3)))
        (sndT (ap3 imageF (var 1) (var 2) (var 3))))) (ZT.natLit 0))) :=
  closeUniv 4 (actual_zero_locus_iff _ _ _ _)

end LeanProofs.IPRA.Geometry.Distinct.AnalyticConicAffine
