import DiophantineConsistency.PRAExponentialWitnessBound
/-! Bound Foundation expDef by the explicit exponential polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAExpWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] exponentialDef

theorem exp_bound (e n : V) : expDef.val.Evalb ![e,n] →
    (bnd expDef.val).Evalb ![e,n,PRAExponentialWitnessBound.exponentialMajorant e] := by
  intro h
  simp [expDef] at h ⊢
  let ω : Rew ℒₒᵣ Empty 2 Empty 2 := Rew.subst ![#1,#0]
  have hb := PRAExponentialWitnessBound.exponential_bound n e h
  have hn := PRABndRewriting.natural exponentialDef.val ω ![e,n] (PRAExponentialWitnessBound.exponentialMajorant e)
  have hv : (fun j => (ω #j).val ![e,n] Empty.elim) = ![n,e] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs : Fin.snoc ![e,n] (PRAExponentialWitnessBound.exponentialMajorant e) = ![e,n,PRAExponentialWitnessBound.exponentialMajorant e] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs' : Fin.snoc ![n,e] (PRAExponentialWitnessBound.exponentialMajorant e) = ![n,e,PRAExponentialWitnessBound.exponentialMajorant e] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  rw [hv,hs,hs'] at hn
  exact hn.mpr hb
def boundedExp : ArithmeticSemisentence 3 := bnd expDef.val

def expBoundBody : ArithmeticSemisentence 2 :=
  “e n. !expDef e n → !boundedExp e n ((e⁴+1)+(e²+1)+(2*e²+1)+(e⁴+e⁴+2*e+1))”

theorem expBoundBody_model (v : Fin 2 → V) : expBoundBody.Eval v Empty.elim := by
  simp [expBoundBody, boundedExp, Semiformula.eval_substs]
  exact exp_bound (v 0) (v 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def expBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding expBoundBody

theorem candidate_proves_exp_bound : PRA ⊢ expBoundSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, expBoundSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact expBoundBody_model e
end DiophantineConsistency.PRAExpWitnessBound
