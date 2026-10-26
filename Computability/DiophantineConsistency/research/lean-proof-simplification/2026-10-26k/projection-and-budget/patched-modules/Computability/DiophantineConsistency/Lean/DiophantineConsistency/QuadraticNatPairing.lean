import DiophantineConsistency.PairingProjection
import DiophantineConsistency.QuadraticRegisterSystem
import DiophantineConsistency.PairingRepresentation

/-!
# A six-natural-variable quartic for max-square pairing

Three auxiliary naturals are a branch bit, an inequality slack, and the maximum
component. Four quadratic rows certify Mathlib's exact `Nat.pair`. Each inverse
projection adds the missing component as one more auxiliary natural.
-/

namespace DiophantineConsistency.QuadraticNatPairing

open NaturalRegisterProgram NaturalRegisterRelation QuadraticRegisterSystem

attribute [local irreducible] Nat.unpair

def Certificate (z a b t s m : ℕ) : Prop :=
  (t : ℤ) * ((t : ℤ) - 1) = 0 ∧
  (m : ℤ) - ((1 - (t : ℤ)) * b + (t : ℤ) * a) = 0 ∧
  (b : ℤ) + (t : ℤ) * s - a - (1 - (t : ℤ)) * ((s : ℤ) + 1) = 0 ∧
  (z : ℤ) - (m : ℤ) * m - a - (t : ℤ) * b = 0

theorem certificate_sound {z a b t s m : ℕ} (h : Certificate z a b t s m) : z = Nat.pair a b := by
  obtain ⟨ht,hm,hs,hz⟩ := h
  have ht01 : t = 0 ∨ t = 1 := by
    rcases mul_eq_zero.mp ht with h0 | h1
    · exact Or.inl (Int.natCast_eq_zero.mp h0)
    · right
      exact_mod_cast sub_eq_zero.mp h1
  rcases ht01 with rfl | rfl
  · norm_num at hm hs hz
    have hm0 : m = b := by omega
    subst m
    have hab : a < b := by omega
    have hz' : (z : ℤ) = (b : ℤ) * b + a := by nlinarith only [hz]
    have hnat : z = b * b + a := by exact_mod_cast hz'
    simpa only [Nat.pair,if_pos hab] using hnat
  · norm_num at hm hs hz
    have hm1 : m = a := by omega
    subst m
    have hnot : ¬a < b := by omega
    have hz' : (z : ℤ) = (a : ℤ) * a + a + b := by nlinarith only [hz]
    have hnat : z = a * a + a + b := by exact_mod_cast hz'
    simpa only [Nat.pair,if_neg hnot] using hnat

theorem certificate_complete {z a b : ℕ} (h : z = Nat.pair a b) :
    ∃ t s m, Certificate z a b t s m := by
  by_cases hab : a < b
  · have heq : b = a + (b-a-1) + 1 := by omega
    have hz : z = b*b+a := by simpa only [Nat.pair,if_pos hab] using h
    refine ⟨0,b-a-1,b,by norm_num,by norm_num,?_,?_⟩
    · norm_num
      omega
    · have hzi : (z : ℤ) = (b : ℤ) * b + a := by exact_mod_cast hz
      norm_num
      nlinarith only [hzi]
  · have heq : b + (a-b) = a := by omega
    have hz : z = a*a+a+b := by simpa only [Nat.pair,if_neg hab] using h
    refine ⟨1,a-b,a,by norm_num,by norm_num,?_,?_⟩
    · norm_num
      omega
    · have hzi : (z : ℤ) = (a : ℤ) * a + a + b := by exact_mod_cast hz
      norm_num
      nlinarith only [hzi]

theorem exists_certificate_iff (z a b : ℕ) :
    (∃ t s m, Certificate z a b t s m) ↔ z = Nat.pair a b :=
  ⟨by rintro ⟨t,s,m,h⟩; exact certificate_sound h,certificate_complete⟩

def program : Program 6 := .empty

private def input (i : Fin 6) : Expr (Fin 6 ⊕ Fin program.nodes.length) := .var (.inl i)

/-- Input 1 is encoded; 3,4,5 are the bit, slack, and maximum. -/
def rows (a b : Fin 6) : Fin 4 → Expr (Fin 6 ⊕ Fin program.nodes.length) :=
  ![input 3 * (input 3 - 1),
    input 5 - ((1 - input 3) * input b + input 3 * input a),
    input b + input 3 * input 4 - input a - (1 - input 3) * (input 4 + 1),
    input 1 - input 5 * input 5 - input a - input 3 * input b]

def system (a b : Fin 6) : System program := System.ofRows 4 (rows a b) (by
  intro i
  fin_cases i <;> decide +revert)

theorem holds_iff (a b : Fin 6) (x : Fin 6 → ℕ) :
    (system a b).Holds x ↔ Certificate (x 1) (x a) (x b) (x 3) (x 4) (x 5) := by
  simp [System.Holds,system,System.ofRows,rows,input,Expr.eval,natAssignment,Certificate,
    Fin.forall_fin_succ]

/-- Direct supplied graph data for `v1=pair(v0,v2)`. -/
def pairRepresentation : Rep (Fin 3) (fun v => v 1 = Nat.pair (v 0) (v 2)) :=
  (System.scopedRep (a := 3) (k := 3) (system 0 2)).ofIff (by
    intro v
    simp only [holds_iff]
    change (∃ w : Fin 3 → ℕ, Certificate (v 1) (v 0) (v 2) (w 0) (w 1) (w 2)) ↔ _
    constructor
    · rintro ⟨w,hw⟩
      exact certificate_sound hw
    · intro h
      obtain ⟨t,s,m,hc⟩ := certificate_complete h
      exact ⟨![t,s,m],hc⟩)

def leftRepresentation : Rep (Fin 2) (fun v => v 0 = (Nat.unpair (v 1)).1) :=
  (System.scopedRep (a := 2) (k := 4) (system 0 2)).ofIff (by
    intro v
    simp only [holds_iff]
    change (∃ w : Fin 4 → ℕ, Certificate (v 1) (v 0) (w 0) (w 1) (w 2) (w 3)) ↔ _
    simp only [Fin.exists_fin_succ_pi, Fin.exists_fin_zero_pi]
    change (∃ b t s m, Certificate (v 1) (v 0) b t s m) ↔ _
    simp only [exists_certificate_iff]
    exact PairingProjection.exists_right_iff Nat.pairEquiv (v 1) (v 0))

def rightRepresentation : Rep (Fin 2) (fun v => v 0 = (Nat.unpair (v 1)).2) :=
  (System.scopedRep (a := 2) (k := 4) (system 2 0)).ofIff (by
    intro v
    simp only [holds_iff]
    change (∃ w : Fin 4 → ℕ, Certificate (v 1) (w 0) (v 0) (w 1) (w 2) (w 3)) ↔ _
    simp only [Fin.exists_fin_succ_pi, Fin.exists_fin_zero_pi]
    change (∃ b t s m, Certificate (v 1) b (v 0) t s m) ↔ _
    simp only [exists_certificate_iff]
    exact PairingProjection.exists_left_iff Nat.pairEquiv (v 1) (v 0))

private def graphIndex : Fin 2 → Option (Fin 1) := Fin.cases none (fun _ => some 0)

def leftGraph : GraphRep (fun v : Fin 1 → ℕ => (Nat.unpair (v 0)).1) :=
  (leftRepresentation.reindex graphIndex).ofIff (fun _ => Iff.rfl)

def rightGraph : GraphRep (fun v : Fin 1 → ℕ => (Nat.unpair (v 0)).2) :=
  (rightRepresentation.reindex graphIndex).ofIff (fun _ => Iff.rfl)

@[simp] theorem pairRepresentation_witnessCount : pairRepresentation.witnessCount = 3 := rfl
@[simp] theorem leftGraph_witnessCount : leftGraph.witnessCount = 4 := rfl
@[simp] theorem rightGraph_witnessCount : rightGraph.witnessCount = 4 := rfl

theorem leftGraph_binaryOps : leftGraph.expression.binaryOps = 46 := by decide
theorem rightGraph_binaryOps : rightGraph.expression.binaryOps = 46 := by decide

theorem pairRepresentation_degree : pairRepresentation.expression.toPolynomial.totalDegree ≤ 4 :=
  System.scopedRep_degree (a := 3) (k := 3) (system 0 2)

theorem leftGraph_degree : leftGraph.expression.toPolynomial.totalDegree ≤ 4 := by
  simp only [leftGraph,Rep.ofIff,Rep.reindex,NaturalRegisterRelation.rename_toPolynomial]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans (System.scopedRep_degree (a := 2) (k := 4) (system 0 2))

theorem rightGraph_degree : rightGraph.expression.toPolynomial.totalDegree ≤ 4 := by
  simp only [rightGraph,Rep.ofIff,Rep.reindex,NaturalRegisterRelation.rename_toPolynomial]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans (System.scopedRep_degree (a := 2) (k := 4) (system 2 0))

end DiophantineConsistency.QuadraticNatPairing
