import DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
import Mathlib.Data.ZMod.Basic
import DiophantineConsistency.NativeAdaptiveGraph
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace AdaptiveModFour
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem exists_residue (x : V) : ∃ n : ℕ, x % 4 = (n : V) := by
  exact eq_nat_of_lt_nat (n:=4) (mod_lt x (by simp))

private def residueNat (x : V) : ℕ := Classical.choose (exists_residue x)
private theorem residueNat_eq (x : V) : (residueNat x : V) = x % 4 :=
  (Classical.choose_spec (exists_residue x)).symm
private theorem residueNat_lt (x : V) : residueNat x < 4 := by
  have h : (residueNat x : V) < 4 := by rw [residueNat_eq]; exact mod_lt x (by simp)
  exact_mod_cast h

def residue (x : V) : ZMod 4 := residueNat x

theorem residue_equal {x y : V} (h : x%4 = y%4) : residue x = residue y := by
  have he : (residueNat x : V) = (residueNat y : V) := by rw [residueNat_eq,residueNat_eq,h]
  have hn : residueNat x = residueNat y := Nat.cast_inj.mp he
  simp only [residue,hn]

theorem cast_mod (n : ℕ) : (((n % 4):ℕ) : V) = (n : V)%4 := by
  have hn : (n : V) = ((n%4:ℕ):V)+4*((n/4:ℕ):V) := by
    have h := Nat.mod_add_div n 4
    exact_mod_cast h.symm
  rw [hn, mod_add_mul' _ _ (by simp : (0:V)<4)]
  symm
  apply mod_eq_self_of_lt
  exact_mod_cast (Nat.mod_lt n (by decide : 0<4))

theorem residue_nat (n : ℕ) : residue (n : V) = (n : ZMod 4) := by
  have he : (residueNat (n:V) : V) = ((n%4:ℕ):V) := by rw [residueNat_eq, cast_mod]
  have hn : residueNat (n:V) = n%4 := Nat.cast_inj.mp he
  simp only [residue,hn,ZMod.natCast_mod]

theorem residue_add (a b : V) : residue (a+b) = residue a + residue b := by
  have h : (a+b)%4 = (((residueNat a + residueNat b):ℕ):V)%4 := by
    rw [mod_add (by simp : (0:V)<4),Nat.cast_add,residueNat_eq,residueNat_eq]
  calc
    residue (a+b) = residue (((residueNat a + residueNat b):ℕ):V) := residue_equal h
    _ = ((residueNat a + residueNat b):ℕ) := residue_nat _
    _ = residue a + residue b := by simp only [residue, Nat.cast_add]

theorem residue_mul (a b : V) : residue (a*b) = residue a * residue b := by
  have h : (a*b)%4 = (((residueNat a * residueNat b):ℕ):V)%4 := by
    rw [mod_mul (by simp : (0:V)<4),Nat.cast_mul,residueNat_eq,residueNat_eq]
  calc
    residue (a*b) = residue (((residueNat a * residueNat b):ℕ):V) := residue_equal h
    _ = ((residueNat a * residueNat b):ℕ) := residue_nat _
    _ = residue a * residue b := by simp only [residue, Nat.cast_mul]
end AdaptiveModFour
namespace AdaptiveModFour
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def pairResidue (p : Pair V) : ZMod 4 := residue p.1 - residue p.2

def syntaxEval {σ : Type*} (v : σ → ZMod 4) : Expr σ → ZMod 4
  | .constant z => (z : ZMod 4)
  | .var i => v i
  | .add p q => syntaxEval v p + syntaxEval v q
  | .sub p q => syntaxEval v p - syntaxEval v q
  | .mul p q => syntaxEval v p * syntaxEval v q

theorem pairEval_residue {σ : Type*} (e : Expr σ) (v : σ → V) :
    pairResidue (pairEval e v) = syntaxEval (fun i => residue (v i)) e := by
  induction e with
  | constant z =>
    change residue ((z.toNat : ℕ):V) - residue (((-z).toNat : ℕ):V) = (z:ZMod 4)
    rw [residue_nat, residue_nat]
    have h := congrArg (fun w : ℤ => (w:ZMod 4)) (Int.toNat_sub_toNat_neg z)
    simpa only [Int.cast_sub,Int.cast_natCast] using h
  | var i =>
    have hz : residue (0:V)=0 := by simpa using residue_nat (V:=V) 0
    simp [pairResidue,pairEval,Expr.splitNatural,NatExpr.evalSemiring,syntaxEval,hz]
  | add p q hp hq =>
    simp only [pairResidue,pairEval,Expr.splitNatural,NatExpr.evalSemiring,residue_add,syntaxEval] at hp hq ⊢
    rw [←hp,←hq]
    ring
  | sub p q hp hq =>
    simp only [pairResidue,pairEval,Expr.splitNatural,NatExpr.evalSemiring,residue_add,syntaxEval] at hp hq ⊢
    rw [←hp,←hq]
    ring
  | mul p q hp hq =>
    simp only [pairResidue,pairEval,Expr.splitNatural,NatExpr.evalSemiring,residue_add,residue_mul,syntaxEval] at hp hq ⊢
    rw [←hp,←hq]
    ring

theorem negative_residue {p : Pair V} (h : p.1 + 1 = p.2) : pairResidue p = -1 := by
  have hh := congrArg residue h
  have ho : residue (1:V)=1 := by simpa using residue_nat (V:=V) 1
  rw [residue_add,ho] at hh
  dsimp [pairResidue]
  rw [←hh]
  ring
end AdaptiveModFour
namespace AdaptiveModFour
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private theorem syntax_add {σ : Type*} (v : σ → ZMod 4) (p q : Expr σ) : syntaxEval v (p+q)=syntaxEval v p+syntaxEval v q := rfl
private theorem syntax_sub {σ : Type*} (v : σ → ZMod 4) (p q : Expr σ) : syntaxEval v (p-q)=syntaxEval v p-syntaxEval v q := rfl
private theorem syntax_mul {σ : Type*} (v : σ → ZMod 4) (p q : Expr σ) : syntaxEval v (p*q)=syntaxEval v p*syntaxEval v q := rfl
private theorem syntax_var {σ : Type*} (v : σ → ZMod 4) (i : σ) : syntaxEval v (.var i)=v i := rfl
private theorem syntax_const {σ : Type*} (v : σ → ZMod 4) (i : ℤ) : syntaxEval v (.constant i)=(i:ZMod 4) := rfl
private theorem syntax_ofNat {σ : Type*} (v : σ → ZMod 4) (n : ℕ) : syntaxEval v (ofNat(n):Expr σ)=(n:ZMod 4) := by
  change ((n:ℤ):ZMod 4)=(n:ZMod 4)
  exact Int.cast_natCast n

private theorem factor0_eval (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    syntaxEval (fun i => residue (v i)) (factors p).1 =
      1+(NativeAdaptiveGraph.core (fun j => (p j : ZMod 4)) (fun i => residue (v i))).A0 := by
  simp only [factors,NativeAdaptiveGraph.core,syntax_add,syntax_sub,syntax_mul,syntax_var,syntax_const,syntax_ofNat,Nat.cast_one,Nat.cast_ofNat]
private theorem factor1_eval (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    syntaxEval (fun i => residue (v i)) (factors p).2.1 =
      1+(NativeAdaptiveGraph.core (fun j => (p j : ZMod 4)) (fun i => residue (v i))).A1 := by
  simp only [factors,NativeAdaptiveGraph.core,syntax_add,syntax_sub,syntax_mul,syntax_var,syntax_const,syntax_ofNat,Nat.cast_one,Nat.cast_ofNat]
private theorem factorAux_eval (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    syntaxEval (fun i => residue (v i)) (factors p).2.2.1 =
      (NativeAdaptiveGraph.core (fun j => (p j : ZMod 4)) (fun i => residue (v i))).Fa := by
  simp only [factors,NativeAdaptiveGraph.core,syntax_add,syntax_sub,syntax_mul,syntax_var,syntax_const,syntax_ofNat,Nat.cast_one,Nat.cast_ofNat]
private theorem factorStrong_eval (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    syntaxEval (fun i => residue (v i)) (factors p).2.2.2 =
      (NativeAdaptiveGraph.core (fun j => (p j : ZMod 4)) (fun i => residue (v i))).Fs := by
  simp only [factors,NativeAdaptiveGraph.core,syntax_add,syntax_sub,syntax_mul,syntax_var,syntax_const,syntax_ofNat,Nat.cast_one,Nat.cast_ofNat]
end AdaptiveModFour
