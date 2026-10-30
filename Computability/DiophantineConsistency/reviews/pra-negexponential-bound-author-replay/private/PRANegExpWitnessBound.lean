import DiophantineConsistency.PRANegExponentialWitnessBound
/-! Bound the negative Foundation expDef graph by an explicit polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegExpWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] exponentialDef

theorem neg_exp_bound (e n : V) : (∼expDef.val).Evalb ![e,n] →
    (bnd (∼expDef.val)).Evalb ![e,n,PRANegExponentialWitnessBound.negExponentialMajorant e] := by
  intro h
  simp [expDef] at h ⊢
  let ω : Rew ℒₒᵣ Empty 2 Empty 2 := Rew.subst ![#1,#0]
  have h' : (∼exponentialDef.val).Evalb ![n,e] := by simpa using h
  have hb := PRANegExponentialWitnessBound.negExponential_bound n e h'
  have hn := PRABndRewriting.natural (∼exponentialDef.val) ω ![e,n] (PRANegExponentialWitnessBound.negExponentialMajorant e)
  have hv : (fun j => (ω #j).val ![e,n] Empty.elim) = ![n,e] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs : Fin.snoc ![e,n] (PRANegExponentialWitnessBound.negExponentialMajorant e) = ![e,n,PRANegExponentialWitnessBound.negExponentialMajorant e] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs' : Fin.snoc ![n,e] (PRANegExponentialWitnessBound.negExponentialMajorant e) = ![n,e,PRANegExponentialWitnessBound.negExponentialMajorant e] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  rw [hv,hs,hs'] at hn
  have hrew := hn.mpr hb
  have heq : (ω ▹ (∼exponentialDef.val)) = ∼(ω ▹ exponentialDef.val) := by
    exact LogicalConnective.HomClass.map_neg (Semiformula.rew ω) exponentialDef.val
  rw [heq] at hrew
  exact hrew
def negExp : ArithmeticSemisentence 2 := ∼expDef.val

def boundedNegExp : ArithmeticSemisentence 3 := bnd negExp

def negExpBoundBody : ArithmeticSemisentence 2 :=
  “e n. !negExp e n → !boundedNegExp e n ((2*e+1)+(2*e²+1))”

theorem negExpBoundBody_model (v : Fin 2 → V) : negExpBoundBody.Eval v Empty.elim := by
  simp [negExpBoundBody, boundedNegExp, Semiformula.eval_substs]
  exact neg_exp_bound (v 0) (v 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def negExpBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negExpBoundBody

theorem candidate_proves_negExp_bound : PRA ⊢ negExpBoundSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, negExpBoundSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact negExpBoundBody_model e
end DiophantineConsistency.PRANegExpWitnessBound
