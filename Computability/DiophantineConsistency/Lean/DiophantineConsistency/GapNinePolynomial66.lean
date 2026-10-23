import DiophantineConsistency.GapKernelData66
import DiophantineConsistency.FreeCarrierRatio
import DiophantineConsistency.SplitNinePolynomial59
import DiophantineConsistency.GapNineSource66
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Literal nine-variable polynomial for the H2082 free-carrier recipe

The finite kernel evaluator uses all 6+36+43 delivered coefficient records.
The natural input order is b,g,h,s,w,C,i,j,n, with successors on every
coordinate except the internal absorbed CRT index j.
-/

namespace DiophantineConsistency.GapNinePolynomial66

open GapKernelData66
open scoped BigOperators

set_option maxRecDepth 16000
set_option maxHeartbeats 600000

variable {A B : Type*} [CommRing A] [CommRing B]

def kernel0 (ports : Fin 4 → A) (base : A) : A :=
  ∑ i,coefficients0 ports i*base^positions0 i

def kernel1 (ports : Fin 4 → A) (base : A) : A :=
  ∑ i,coefficients1 ports i*base^positions1 i

def kernel2 (ports : Fin 4 → A) (base : A) : A :=
  ∑ i,coefficients2 ports i*base^positions2 i

def sourceBase (height b : A) : A := 4096*height*b^2

def ell (base : A) : A := ∑ i,base^GapCertificate66.weights i

def targets (base : A) : A := ∑ j,base^GapCertificate66.targets j

def sourceHigh (ports : Fin 4 → A) (base g : A) : A :=
  let u := ell base+g
  2*(kernel2 ports base*u^2+kernel1 ports base*u+kernel0 ports base)+targets base

def sourceS (ports : Fin 4 → A) (base g : A) : A := g+base^117*sourceHigh ports base g

def sourceT (base b : A) : A :=
  base^117-1-(b-1)*ell base+base^117*((base-2)*targets base)

def blockLength (base b : A) : A := b*base^2200

def sourceRank (ports : Fin 4 → A) (base b g : A) : A :=
  blockLength base b*(sourceS ports base g+sourceT base b+1)-sourceS ports base g-1

def threshold (scale base : A) : A := scale*base^1162

def marginScale (base b : A) : A := b*base^116

/-- The actual free-carrier tail; all powers have fixed natural exponents. -/
def ratioValue (R N b g t h s w C i j n : A) : A :=
  let U := N^2*w
  let Y := N^2*s
  let M := R*Y
  let P := 2*M^2*U
  let K := R+1+h*(P-1)
  let a := M*(U+1)
  let B1 := 2*R+1
  let W := b*w
  let J := 4*a-5
  let Q := 3*W*C-2*(W^2-1)
  let D := (a^2-1)*C^2+1
  let E := i*J*D*C^2
  let F := (a^2-1)*E^2+1
  let G := a+F*(C*D+1-a)
  let H := C+F*(B1+j*C)
  let I := (G^2-1)*H^2+1
  let k := i*J*C
  let V0 := P*K
  let V1 := k*(8*D^2-4*D-1)*G*H
  let m := K^2*(4*t-g)-16*t*(C-K*Y)^2
  let omega := J*m
  let theta := J*(n+W^2)+Q-omega*(V0+V1)
  NearSquareFinalizer.norm theta omega ((P^2-1)*K^2+1) 8 (D*F*I)

/-- Coordinates are mixed-domain: eight positive inputs and internal j natural. -/
def mixedValue (ports : Fin 4 → A) (height scale : A) (x : Fin 9 → A) : A :=
  let base := sourceBase height (x 0)
  ratioValue (sourceRank ports base (x 0) (x 1)) (threshold scale base)
    (x 0) (x 1) (marginScale base (x 0)) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)

/-- Bijective all-positive-to-natural translation, with j_plus-1=x7. -/
def successorShift (x : Fin 9 → A) : Fin 9 → A := fun i => if i=7 then x i else x i+1

def value (ports : Fin 4 → A) (height scale : A) (x : Fin 9 → A) : A :=
  mixedValue ports height scale (successorShift x)

-- BEGIN GENERATED COEFFICIENT MAPS
-- H2082 kernel table SHA256 777fa43ca252eae12d375d9152fa7a3019f3936af24c641f8ac0fcae876a2839.
set_option linter.unusedSimpArgs false in
theorem map_coefficients0 (f : A →+* B) (ports : Fin 4 → A) (i : Fin 6) :
    f (coefficients0 ports i)=coefficients0 (fun j => f (ports j)) i := by
  fin_cases i
  · change f (((2) * ports 1))=(((2) * f (ports 1)))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-2))=((-2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-2))=((-2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-6))=((-6))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-2))=((-2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-2))=((-2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]

set_option linter.unusedSimpArgs false in
theorem map_coefficients1 (f : A →+* B) (ports : Fin 4 → A) (i : Fin 36) :
    f (coefficients1 ports i)=coefficients1 (fun j => f (ports j)) i := by
  fin_cases i
  · change f ((-2))=((-2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f (((-2) * ports 1))=(((-2) * f (ports 1)))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-2 + (-2) * ports 1))=((-2 + (-2) * f (ports 1)))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f (((2) * ports 0 + (2) * ports 0 * ports 1))=(((2) * f (ports 0) + (2) * f (ports 0) * f (ports 1)))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-2))=((-2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-8))=((-8))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-2))=((-2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-2))=((-2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f (((-2) * ports 3 + (-2) * ports 2))=(((-2) * f (ports 3) + (-2) * f (ports 2)))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-2))=((-2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-6))=((-6))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f (((-4) * ports 0))=(((-4) * f (ports 0)))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-2))=((-2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-2))=((-2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]

set_option linter.unusedSimpArgs false in
theorem map_coefficients2 (f : A →+* B) (ports : Fin 4 → A) (i : Fin 43) :
    f (coefficients2 ports i)=coefficients2 (fun j => f (ports j)) i := by
  fin_cases i
  · change f (((-(ports 0))))=(((-(f (ports 0)))))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f (((-(ports 0))))=(((-(f (ports 0)))))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-2))=((-2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((1))=((1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-2))=((-2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((1))=((1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-2))=((-2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f (((-(ports 0))))=(((-(f (ports 0)))))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((1))=((1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((1))=((1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f (((-(ports 0))))=(((-(f (ports 0)))))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f (((-2) * ports 0 * ports 3))=(((-2) * f (ports 0) * f (ports 3)))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-2))=((-2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-4))=((-4))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f (((-2) * ports 0 ^ 2))=(((-2) * f (ports 0) ^ 2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-2))=((-2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((2))=((2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-2))=((-2))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f (((-(ports 0))))=(((-(f (ports 0)))))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((1))=((1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((-1))=((-1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
  · change f ((1))=((1))
    simp only [map_neg,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero]
-- END GENERATED COEFFICIENT MAPS

theorem map_kernel0 (f : A →+* B) (ports : Fin 4 → A) (base : A) :
    f (kernel0 ports base)=kernel0 (fun i => f (ports i)) (f base) := by
  simp only [kernel0,map_sum,map_mul,map_pow,map_coefficients0]

theorem map_kernel1 (f : A →+* B) (ports : Fin 4 → A) (base : A) :
    f (kernel1 ports base)=kernel1 (fun i => f (ports i)) (f base) := by
  simp only [kernel1,map_sum,map_mul,map_pow,map_coefficients1]

theorem map_kernel2 (f : A →+* B) (ports : Fin 4 → A) (base : A) :
    f (kernel2 ports base)=kernel2 (fun i => f (ports i)) (f base) := by
  simp only [kernel2,map_sum,map_mul,map_pow,map_coefficients2]

theorem map_sourceRank (f : A →+* B) (ports : Fin 4 → A) (base b g : A) :
    f (sourceRank ports base b g)=sourceRank (fun i => f (ports i)) (f base) (f b) (f g) := by
  simp only [sourceRank,blockLength,sourceS,sourceT,sourceHigh,ell,targets,
    map_kernel0,map_kernel1,map_kernel2,map_sum,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one]

theorem map_ratioValue (f : A →+* B) (R N b g t h s w C i j n : A) :
    f (ratioValue R N b g t h s w C i j n)=
      ratioValue (f R) (f N) (f b) (f g) (f t) (f h) (f s) (f w) (f C) (f i) (f j) (f n) := by
  simp only [ratioValue,NearSquareFinalizer.norm,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one]

theorem map_mixedValue (f : A →+* B) (ports : Fin 4 → A) (height scale : A) (x : Fin 9 → A) :
    f (mixedValue ports height scale x)=mixedValue (fun i => f (ports i))
      (f height) (f scale) (fun i => f (x i)) := by
  simp only [mixedValue,sourceBase,threshold,marginScale,map_ratioValue,map_sourceRank,
    map_mul,map_pow,map_ofNat]

theorem map_value (f : A →+* B) (ports : Fin 4 → A) (height scale : A) (x : Fin 9 → A) :
    f (value ports height scale x)=value (fun i => f (ports i))
      (f height) (f scale) (fun i => f (x i)) := by
  unfold value
  rw [map_mixedValue]
  congr 1
  funext i
  by_cases hi : i=7 <;> simp only [successorShift,hi,if_true,if_false,map_add,map_one]

theorem kernel0_eq_eval (ports : Fin 4 → A) (base : A) :
    kernel0 ports base=(D0 ports).eval base := by
  simp only [kernel0,D0,sparseKernel,SplitKernelData59.sparseKernel,Polynomial.eval_finsetSum,Polynomial.eval_monomial]

theorem kernel1_eq_eval (ports : Fin 4 → A) (base : A) :
    kernel1 ports base=(D1 ports).eval base := by
  simp only [kernel1,D1,sparseKernel,SplitKernelData59.sparseKernel,Polynomial.eval_finsetSum,Polynomial.eval_monomial]

theorem kernel2_eq_eval (ports : Fin 4 → A) (base : A) :
    kernel2 ports base=(D2 ports).eval base := by
  simp only [kernel2,D2,sparseKernel,SplitKernelData59.sparseKernel,Polynomial.eval_finsetSum,Polynomial.eval_monomial]

/-- The free carrier is substituted before the definitions are unfolded. -/
theorem ratioValue_nat (v : FreeCarrierRatio.FreeVars) (R N b g cap t n : ℕ) :
    ratioValue (R:ℤ) N b g t v.h v.s v.w v.C v.i v.j n=v.finalValue R N b g cap t n := by
  rw [← v.base_C R N b g cap]
  rfl

/-- A supplied finite recipe for an ordinary integer polynomial. -/
noncomputable def polynomial (ports : Fin 4 → ℤ) (a : ℕ) : MvPolynomial (Fin 9) ℤ :=
  value (fun i => MvPolynomial.C (ports i)) (MvPolynomial.C ((2:ℤ)^(2*a)))
    (MvPolynomial.C ((2:ℤ)^(15*a+79))) MvPolynomial.X

theorem eval_polynomial (ports : Fin 4 → ℤ) (a : ℕ) (x : Fin 9 → ℤ) :
    MvPolynomial.eval x (polynomial ports a)=value ports ((2:ℤ)^(2*a)) ((2:ℤ)^(15*a+79)) x := by
  unfold polynomial
  rw [map_value]
  simp only [MvPolynomial.eval_C,MvPolynomial.eval_X]

/-- The literal base agrees with the supplied natural source scale. -/
theorem sourceBase_nat (a b : ℕ) :
    sourceBase ((2:ℤ)^(2*a)) (b:ℤ)=(GapNineRatio66.base a b:ℤ) :=
  (GapSourceWords66.scale a b).symm

theorem sourceRank_nat (ports : Fin 4 → ℤ) (a b g : ℕ)
    (hd : GapSourceWords66.Valid (GapNineSource66.parameters ports) a) (hb : 0<b) :
    sourceRank ports (GapNineRatio66.base a b:ℤ) b g =
      (GapNineRatio66.rank a b (GapSourceWords66.word (GapNineSource66.parameters ports) a b g)
        (GapSourceWords66.mask (GapNineSource66.parameters ports) a b):ℤ) := by
  rw [GapSourceWords66.rank_cast hd hb g]
  simp only [sourceRank,blockLength,sourceS,sourceT,sourceHigh,
    kernel0_eq_eval,kernel1_eq_eval,kernel2_eq_eval,
    GapNineSource66.parameters,GapSourceWords66.literalParameters,
    SplitWordBounds.powerSum,SplitWordBounds.sourceValue,SplitWordBounds.packedS,
    SplitWordBounds.packedT,SplitWordBounds.lowMask,ell,targets,
    GapNineRatio66.blockLength,Nat.cast_mul,Nat.cast_pow]

theorem threshold_nat (a b : ℕ) :
    threshold ((2:ℤ)^(15*a+79)) (GapNineRatio66.base a b:ℤ) =
      (GapNineRatio66.threshold a b:ℤ) := by
  simp only [threshold,GapNineRatio66.threshold,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]

theorem marginScale_nat (a b : ℕ) :
    marginScale (GapNineRatio66.base a b:ℤ) b=(GapNineRatio66.marginScale a b:ℤ) := by
  simp only [marginScale,GapNineRatio66.marginScale,Nat.cast_mul,Nat.cast_pow]

def witnessVector (b g : ℕ) (v : FreeCarrierRatio.FreeVars) (n : ℕ) : Fin 9 → ℕ :=
  ![b,g,v.h,v.s,v.w,v.C,v.i,v.j,n]

theorem mixedValue_nat (ports : Fin 4 → ℤ) (a b g : ℕ)
    (hd : GapSourceWords66.Valid (GapNineSource66.parameters ports) a) (hb : 0<b)
    (v : FreeCarrierRatio.FreeVars) (n : ℕ) :
    mixedValue ports ((2:ℤ)^(2*a)) ((2:ℤ)^(15*a+79))
      (fun i => (witnessVector b g v n i:ℤ)) =
      GapSourceExistence66.value (GapNineSource66.parameters ports) a b g v n := by
  change ratioValue (sourceRank ports (sourceBase ((2:ℤ)^(2*a)) b) b g)
    (threshold ((2:ℤ)^(15*a+79)) (sourceBase ((2:ℤ)^(2*a)) b))
    b g (marginScale (sourceBase ((2:ℤ)^(2*a)) b) b) v.h v.s v.w v.C v.i v.j n = _
  rw [sourceBase_nat,sourceRank_nat ports a b g hd hb,threshold_nat,marginScale_nat]
  exact ratioValue_nat v _ _ _ _ _ _ _

theorem successorShift_nat (x : Fin 9 → ℕ) :
    successorShift (fun i => (x i:ℤ)) = fun i =>
      (witnessVector (x 0+1) (x 1+1) (GapSourceExistence66.naturalVars x) (x 8+1) i:ℤ) := by
  funext i
  fin_cases i <;> simp [successorShift,witnessVector,GapSourceExistence66.naturalVars]

theorem value_eq_naturalValue (ports : Fin 4 → ℤ) (a : ℕ)
    (hd : GapSourceWords66.Valid (GapNineSource66.parameters ports) a) (x : Fin 9 → ℕ) :
    value ports ((2:ℤ)^(2*a)) ((2:ℤ)^(15*a+79)) (fun i => (x i:ℤ)) =
      GapNineSource66.naturalValue ports a x := by
  unfold value
  rw [successorShift_nat,mixedValue_nat ports a (x 0+1) (x 1+1) hd (Nat.succ_pos _)]
  rfl

theorem eval_polynomial_nat (ports : Fin 4 → ℤ) (a : ℕ)
    (hd : GapSourceWords66.Valid (GapNineSource66.parameters ports) a) (x : Fin 9 → ℕ) :
    MvPolynomial.eval (fun i => (x i:ℤ)) (polynomial ports a)=
      GapNineSource66.naturalValue ports a x := by
  rw [eval_polynomial,value_eq_naturalValue ports a hd]

/-- Literal polynomial zeros are equivalent to the authoritative shifted
source rows, under the explicit kernel and geometry bounds. -/
theorem exists_natural_zero_iff_source (ports : Fin 4 → ℤ) (a : ℕ)
    (hd : GapSourceWords66.Valid (GapNineSource66.parameters ports) a) :
    (∃ x : Fin 9 → ℕ, MvPolynomial.eval (fun i => (x i:ℤ)) (polynomial ports a)=0) ↔
      ∃ z : Fin 31 → ℕ, ∀ j,
        GapSource66.rows ports (fun i => (z i:ℤ)+1) j=0 := by
  simp_rw [eval_polynomial_nat ports a hd]
  exact GapNineSource66.exists_natural_zero_iff_source ports a hd

theorem exists_natural_zero_iff_source_portBounds (ports : Fin 4 → ℤ) (p q a : ℕ)
    (hp : 1≤p) (hpq : p+4≤q) (ha : p+q+1=2*a)
    (hb : 0≤ports 0 ∧ ports 0<2^p)
    (hk : 0≤ports 1 ∧ ports 1<2^q)
    (hm : 0≤ports 2 ∧ ports 2<2^p)
    (hf : 0≤ports 3 ∧ ports 3<2*2^p) :
    (∃ x : Fin 9 → ℕ, MvPolynomial.eval (fun i => (x i:ℤ)) (polynomial ports a)=0) ↔
      ∃ z : Fin 31 → ℕ, ∀ j,
        GapSource66.rows ports (fun i => (z i:ℤ)+1) j=0 :=
  exists_natural_zero_iff_source ports a
    (GapSourceWords66.literal_valid_pow ports p q a hp hpq ha hb hk hm hf)

theorem exists_natural_zero_iff_source_compact54 (ports : Fin 4 → ℤ)
    (hb : 0≤ports 0 ∧ ports 0<2^429959)
    (hk : 0≤ports 1 ∧ ports 1<2^434054)
    (hm : 0≤ports 2 ∧ ports 2<2^429959)
    (hf : 0≤ports 3 ∧ ports 3<2*2^429959) :
    (∃ x : Fin 9 → ℕ, MvPolynomial.eval (fun i => (x i:ℤ)) (polynomial ports 432007)=0) ↔
      ∃ z : Fin 31 → ℕ, ∀ j,
        GapSource66.rows ports (fun i => (z i:ℤ)+1) j=0 :=
  exists_natural_zero_iff_source_portBounds ports 429959 434054 432007
    (by decide) (by decide) (by decide) hb hk hm hf

theorem no_natural_zero_iff_source (ports : Fin 4 → ℤ) (a : ℕ)
    (hd : GapSourceWords66.Valid (GapNineSource66.parameters ports) a) :
    (∀ x : Fin 9 → ℕ, MvPolynomial.eval (fun i => (x i:ℤ)) (polynomial ports a)≠0) ↔
      ¬∃ z : Fin 31 → ℕ, ∀ j,
        GapSource66.rows ports (fun i => (z i:ℤ)+1) j=0 := by
  simpa only [not_exists] using not_congr (exists_natural_zero_iff_source ports a hd)

/-- The complete compact54 H2082 polynomial and earlier split116 polynomial
have the same natural root existence, through the proved positive affine
source change. This is not a native consistency calibration. -/
theorem compact54_zero_iff_split59 (ports : Fin 4 → ℤ) (hβ : 0<ports 0)
    (hb : 0≤ports 0 ∧ ports 0<2^429959)
    (hk : 0≤ports 1 ∧ ports 1<2^434054)
    (hm : 0≤ports 2 ∧ ports 2<2^429959)
    (hf : 0≤ports 3 ∧ ports 3<2*2^429959) :
    (∃ x : Fin 9 → ℕ, MvPolynomial.eval (fun i => (x i:ℤ)) (polynomial ports 432007)=0) ↔
      ∃ x : Fin 9 → ℕ, MvPolynomial.eval (fun i => (x i:ℤ))
        (SplitNinePolynomial59.polynomial ports 864014)=0 :=
  (exists_natural_zero_iff_source_compact54 ports hb hk hm hf).trans
    ((GapNineSource66.source_successor_zero_iff_old ports hβ).trans
      (SplitNinePolynomial59.exists_natural_zero_iff_source_compact54 ports hb hk hm hf).symm)

end DiophantineConsistency.GapNinePolynomial66
