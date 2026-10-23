import DiophantineConsistency.WeightedExpressionDegree
import DiophantineConsistency.NearSquareFinalizer
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Cancellation-aware degree certificates for the free-carrier finalizer

These theorems accept explicit register-degree bounds. Identifying those
registers with a particular source polynomial is a separate application.
-/

namespace DiophantineConsistency.FreeCarrierDegree

def defectSyntax : Expr (Fin 5) :=
  let k := Expr.var 0
  let D := Expr.var 1
  let F := Expr.var 2
  let G := Expr.var 3
  let H := Expr.var 4
  (k^2*(8*D+1)-64*D)*G^2*H^2+64*D*F*(H^2-1)

def defectWeights : Fin 5 → ℕ := ![18099,36196,144786,180983,153585]

theorem defect_weightedDegree : defectSyntax.weightedDegree defectWeights=741530 := rfl

/-- Inputs are E0, omega, P, K, V1, a1, and the cancelled majorant defect. -/
def innerSyntax : Expr (Fin 7) :=
  let e := Expr.var 0
  let w := Expr.var 1
  let P := Expr.var 2
  let K := Expr.var 3
  let V := Expr.var 4
  let d := Expr.var 6
  e^2-2*e*w*(P*K+V)+w^2*(K^2-1+2*P*K*V+d)

def normSyntax : Expr (Fin 7) :=
  innerSyntax^2-256*(Expr.var 1)^4*((((Expr.var 2)^2-1)*(Expr.var 3)^2)+1)*Expr.var 5

def weights : Fin 7 → ℕ := ![18101,90720,31545,31546,425059,850118,741530]

theorem inner_weightedDegree : innerSyntax.weightedDegree weights=922970 := rfl
theorem norm_weightedDegree : normSyntax.weightedDegree weights=1845940 := rfl

theorem eval_defectSyntax {R : Type*} [CommRing R] (k D F G H : R) :
    defectSyntax.evalRing ![k,D,F,G,H] =
      (k^2*(8*D+1)-64*D)*G^2*H^2+64*D*F*(H^2-1) := by
  simp [defectSyntax,Expr.evalRing,Expr.evalRing_pow]

theorem eval_normSyntax {R : Type*} [CommRing R] (e w P K V A d : R)
    (hd : d=V^2-64*A) :
    normSyntax.evalRing ![e,w,P,K,V,A,d] =
      NearSquareFinalizer.norm (e-w*(P*K+V)) w ((P^2-1)*K^2+1) 8 A := by
  subst d
  simp [normSyntax,innerSyntax,NearSquareFinalizer.norm]
  ring

theorem defect_degree_le {σ : Type*} (k D F G H I : MvPolynomial σ ℤ)
    (hk : k.totalDegree ≤ 18099) (hD : D.totalDegree ≤ 36196)
    (hF : F.totalDegree ≤ 144786) (hG : G.totalDegree ≤ 180983)
    (hH : H.totalDegree ≤ 153585)
    (hDF : D*F=k^2*D^3*(D-1)+D) (hI : I=(G^2-1)*H^2+1) :
    ((k*(8*D^2-4*D-1)*G*H)^2-64*D*F*I).totalDegree ≤ 741530 := by
  have hv : ∀ i, ((![k,D,F,G,H] : Fin 5 → MvPolynomial σ ℤ) i).totalDegree ≤ defectWeights i := by
    intro i
    fin_cases i
    · exact hk
    · exact hD
    · exact hF
    · exact hG
    · exact hH
  have h := Expr.degree_evalRing_le defectSyntax defectWeights ![k,D,F,G,H] hv
  rw [defect_weightedDegree,eval_defectSyntax] at h
  rw [NearSquareFinalizer.full_majorant_defect k D F G H I hDF hI]
  exact h

theorem norm_degree_le {σ : Type*} (e w P K V A d : MvPolynomial σ ℤ)
    (he : e.totalDegree ≤ 18101) (hw : w.totalDegree ≤ 90720)
    (hP : P.totalDegree ≤ 31545) (hK : K.totalDegree ≤ 31546)
    (hV : V.totalDegree ≤ 425059) (hA : A.totalDegree ≤ 850118)
    (hd : d.totalDegree ≤ 741530) (hdef : d=V^2-64*A) :
    (NearSquareFinalizer.norm (e-w*(P*K+V)) w ((P^2-1)*K^2+1) 8 A).totalDegree ≤ 1845940 := by
  have hv : ∀ i, ((![e,w,P,K,V,A,d] : Fin 7 → MvPolynomial σ ℤ) i).totalDegree ≤ weights i := by
    intro i
    fin_cases i
    · exact he
    · exact hw
    · exact hP
    · exact hK
    · exact hV
    · exact hA
    · exact hd
  have h := Expr.degree_evalRing_le normSyntax weights ![e,w,P,K,V,A,d] hv
  rw [norm_weightedDegree,eval_normSyntax e w P K V A d hdef] at h
  exact h

end DiophantineConsistency.FreeCarrierDegree
