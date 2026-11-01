import DiophantineConsistency.AdaptiveGap85BalanceLeast
import BusyBeaver.ZFC.ArithmeticCantor
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ScoreCoding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal AdaptiveGap85BalanceLeast
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def tupleValue : (n : Nat) → (Fin (n+1) → V) → V
  | 0, values => values 0
  | n+1, values => cantor (values 0) (tupleValue n (fun i => values i.succ))

noncomputable def tupleProjection : (n : Nat) → V → Fin (n+1) → V
  | 0, code, _ => code
  | n+1, code, i => Fin.cases (first code) (fun j => tupleProjection n (second code) j) i

theorem tupleProjection_value (n : Nat) (values : Fin (n+1) → V) :
    tupleProjection n (tupleValue n values) = values := by
  induction n with
  | zero => funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [tupleProjection,tupleValue,Fin.cases_zero,first_cantor]
      · simpa only [tupleProjection,tupleValue,Fin.cases_succ,second_cantor] using
          congrFun (ih (fun j => values j.succ)) j

theorem tupleValue_projection (n : Nat) (code : V) :
    tupleValue n (tupleProjection n code) = code := by
  induction n generalizing code with
  | zero => rfl
  | succ n ih =>
      simpa only [tupleValue,tupleProjection,Fin.cases_zero,Fin.cases_succ,ih]
        using cantor_projections code

def projectionDef : (n : Nat) → Fin (n+1) → 𝚺₁.Semisentence 2
  | 0, _ => .mkSigma “out code. out = code”
  | n+1, i => Fin.cases
      (.mkSigma “out code. !ArithmeticCantor.firstDef out code”)
      (fun j => .mkSigma
        “out code. ∃ tail, !ArithmeticCantor.secondDef tail code ∧
          !(projectionDef n j) out tail”) i

instance projection_defined (n : Nat) (i : Fin (n+1)) :
    𝚺₁-Function₁[V] (fun code => tupleProjection n code i) via projectionDef n i := by
  induction n with
  | zero => exact .mk fun e => by simp [projectionDef,tupleProjection]
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact .mk fun e => by simp [projectionDef,tupleProjection]
      · exact .mk fun e => by simp [projectionDef,tupleProjection,(ih j).iff]

theorem eval_defined (e : NatExpr (Fin 13)) :
    𝚺₁-Function₁[V] (fun code => e.evalSemiring (tupleProjection 12 code)) := by
  induction e with
  | constant n =>
    simp only [NatExpr.evalSemiring]
    definability
  | var i =>
    simpa only [NatExpr.evalSemiring] using (projection_defined (V:=V) 12 i).to_definable
  | add a b ha hb =>
    letI := ha
    letI := hb
    simp only [NatExpr.evalSemiring]
    definability
  | mul a b ha hb =>
    letI := ha
    letI := hb
    simp only [NatExpr.evalSemiring]
    definability

local instance projection_definable (i : Fin 13) :
    𝚺₁-Function₁[V] (fun code => tupleProjection 12 code i) :=
  (projection_defined (V:=V) 12 i).to_definable

def positiveAt (i : Fin 13) (code : V) : Prop := 0<tupleProjection 12 code i

def positiveAtDef (i : Fin 13) : 𝚺₁.Semisentence 1 := .mkSigma
  “code. ∃ out, !(projectionDef 12 i) out code ∧ 0<out”

theorem positiveAt_defined (i : Fin 13) :
    𝚺₁-Predicate (positiveAt (V:=V) i) via positiveAtDef i := by
  refine .mk fun e => ?_
  simp [positiveAtDef,positiveAt,(projection_defined (V:=V) 12 i).iff]

local instance positiveAt_definable (i : Fin 13) :
    𝚺₁-Predicate (positiveAt (V:=V) i) := (positiveAt_defined (V:=V) i).to_definable

def tuplePositive (code : V) : Prop :=
  positiveAt 0 code ∧ positiveAt 1 code ∧ positiveAt 2 code ∧
  positiveAt 3 code ∧ positiveAt 4 code ∧ positiveAt 5 code ∧
  positiveAt 6 code ∧ positiveAt 7 code ∧ positiveAt 8 code ∧
  positiveAt 9 code ∧ positiveAt 10 code ∧ positiveAt 11 code ∧ positiveAt 12 code

theorem tuplePositive_iff (code : V) :
    tuplePositive code ↔ ∀ i, 0<tupleProjection 12 code i := by
  unfold tuplePositive positiveAt
  constructor
  · intro h i
    rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩
    fin_cases i <;> assumption
  · intro h
    exact ⟨h 0,h 1,h 2,h 3,h 4,h 5,h 6,h 7,h 8,h 9,h 10,h 11,h 12⟩

def codeZero (p : Fin 4 → ℕ) (code : V) : Prop :=
  InternalZero (expressionAt85 (fun j => (p j:ℤ))) (tupleProjection 12 code)

def codeSum (code : V) : V := tupleProjection 12 code 1+tupleProjection 12 code 2

def codedScore (p : Fin 4 → ℕ) (m : V) : Prop :=
  ∃ code : V, tuplePositive code ∧ codeZero p code ∧ m=codeSum code

theorem codedScore_iff (p : Fin 4 → ℕ) (m : V) :
    codedScore p m ↔ zeroScore p m := by
  constructor
  · rintro ⟨code,hpos,hzero,heq⟩
    exact ⟨tupleProjection 12 code,(tuplePositive_iff code).mp hpos,hzero,heq⟩
  · rintro ⟨v,hpos,hzero,heq⟩
    refine ⟨tupleValue 12 v,?_,?_,?_⟩
    · apply (tuplePositive_iff _).mpr
      simpa only [tupleProjection_value] using hpos
    · simpa only [codeZero,tupleProjection_value] using hzero
    · simpa only [codeSum,tupleProjection_value] using heq

theorem tuplePositive_definable : 𝚺₁-Predicate (tuplePositive (V:=V)) := by
  unfold tuplePositive
  definability

theorem codeZero_definable (p : Fin 4 → ℕ) : 𝚺₁-Predicate (codeZero (V:=V) p) := by
  let e := expressionAt85 (fun j => (p j:ℤ))
  letI : 𝚺₁-Function₁[V] (fun code => e.splitNatural.1.evalSemiring (tupleProjection 12 code)) :=
    eval_defined e.splitNatural.1
  letI : 𝚺₁-Function₁[V] (fun code => e.splitNatural.2.evalSemiring (tupleProjection 12 code)) :=
    eval_defined e.splitNatural.2
  change 𝚺₁-Predicate (fun code : V =>
    e.splitNatural.1.evalSemiring (tupleProjection 12 code) =
      e.splitNatural.2.evalSemiring (tupleProjection 12 code))
  definability

theorem codeSum_definable : 𝚺₁-Function₁[V] (codeSum (V:=V)) := by
  unfold codeSum
  have h := eval_defined (V:=V) (.add (.var (1:Fin 13)) (.var (2:Fin 13)))
  simpa only [NatExpr.evalSemiring] using h

theorem codedScore_definable (p : Fin 4 → ℕ) :
    𝚺₁-Predicate (codedScore (V:=V) p) := by
  letI := tuplePositive_definable (V:=V)
  letI := codeZero_definable (V:=V) p
  letI := codeSum_definable (V:=V)
  unfold codedScore
  definability

theorem zeroScore_definable (p : Fin 4 → ℕ) :
    𝚺₁-Predicate (zeroScore (V:=V) p) := by
  have he : zeroScore (V:=V) p = codedScore p := by
    funext m
    exact propext (codedScore_iff p m).symm
  rw [he]
  exact codedScore_definable p

/-- Every nonempty set of positive-zero scores has a minimizing witness in
an arbitrary IΣ₁ model. -/
theorem exists_minimizing_zero (p : Fin 4 → ℕ)
    (hex : ∃ v : Fin 13 → V, (∀ i,0<v i) ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    ∃ v : Fin 13 → V, (∀ i,0<v i) ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) v ∧
      ∀ w : Fin 13 → V, (∀ i,0<w i) →
        InternalZero (expressionAt85 (fun j => (p j:ℤ))) w → v 1+v 2≤w 1+w 2 := by
  obtain ⟨u,hu,huz⟩ := hex
  have hwit : zeroScore (V:=V) p (u 1+u 2) := ⟨u,hu,huz,rfl⟩
  obtain ⟨m,⟨v,hv,hz,hm⟩,hmin⟩ :=
    InductionOnHierarchy.least_number 𝚺 1 (zeroScore_definable p) hwit
  refine ⟨v,hv,hz,?_⟩
  intro w hwp hwz
  apply le_of_not_gt
  intro hlt
  apply hmin (w 1+w 2)
  · simpa only [hm] using hlt
  · exact ⟨w,hwp,hwz,rfl⟩

/-- The conditional least-number premise is now discharged for the actual
13-coordinate 85 literal. This does not prove that a zero exists. -/
theorem exists_minimal_blocked_unconditional (p : Fin 4 → ℕ)
    (hp : 0<(p 0:V))
    (hex : ∃ v : Fin 13 → V, (∀ i,0<v i) ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    ∃ v : Fin 13 → V, (∀ i,0<v i) ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) v ∧
      (let b := v 0*(p 0:V); let q := 1+b;
       let A := v 6+(p 1:V)*q; let k := v 9+v 10;
       v 2≤q*b ∨ v 8≤q*(A+1)*(b*k+1)) :=
  exists_minimal_blocked p hp (zeroScore_definable p) hex
end DiophantineConsistency.AdaptiveGap85ScoreCoding
