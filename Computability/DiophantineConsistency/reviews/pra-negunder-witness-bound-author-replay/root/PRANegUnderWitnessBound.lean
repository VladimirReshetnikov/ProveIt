import DiophantineConsistency.PRANegExpWitnessBound
/-! Explicit negative bound for the actual Foundation underDef graph. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegUnderWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] expDef

theorem neg_under_bound (y x : V) : (∼underDef.val).Evalb ![y,x] →
    (bnd (∼underDef.val)).Evalb ![y,x,PRANegExponentialWitnessBound.negExponentialMajorant (y+1)] := by
  intro h
  simp [underDef] at h ⊢
  let ω : Rew ℒₒᵣ Empty 2 Empty 2 := Rew.subst ![‘#0+1’,#1]
  have h' : (∼expDef.val).Evalb ![y+1,x] := by simpa using h
  have hb := PRANegExpWitnessBound.neg_exp_bound (y+1) x h'
  have hn := PRABndRewriting.natural (∼expDef.val) ω ![y,x] (PRANegExponentialWitnessBound.negExponentialMajorant (y+1))
  have hv : (fun j => (ω #j).val ![y,x] Empty.elim) = ![y+1,x] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs : Fin.snoc ![y,x] (PRANegExponentialWitnessBound.negExponentialMajorant (y+1)) = ![y,x,PRANegExponentialWitnessBound.negExponentialMajorant (y+1)] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs' : Fin.snoc ![y+1,x] (PRANegExponentialWitnessBound.negExponentialMajorant (y+1)) = ![y+1,x,PRANegExponentialWitnessBound.negExponentialMajorant (y+1)] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  rw [hv,hs,hs'] at hn
  have hh := hn.mpr hb
  have heq : (ω ▹ (∼expDef.val)) = ∼(ω ▹ expDef.val) := by
    exact LogicalConnective.HomClass.map_neg (Semiformula.rew ω) expDef.val
  rw [heq] at hh
  exact hh
noncomputable def negUnder : ArithmeticSemisentence 2 := ∼underDef.val
noncomputable def boundedNegUnder : ArithmeticSemisentence 3 := bnd negUnder
noncomputable def negUnderBoundBody : ArithmeticSemisentence 2 :=
  “y x. !negUnder y x → !boundedNegUnder y x ((2*(y+1)+1)+(2*(y+1)²+1))”
theorem negUnderBoundBody_model (e : Fin 2 → V) : negUnderBoundBody.Eval e Empty.elim := by
  simpa [negUnderBoundBody, boundedNegUnder, negUnder, PRANegExponentialWitnessBound.negExponentialMajorant, Semiformula.eval_substs] using neg_under_bound (e 0) (e 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def negUnderBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negUnderBoundBody
theorem candidate_proves_neg_under_bound : PRA ⊢ negUnderBoundSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, negUnderBoundSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact negUnderBoundBody_model e
end DiophantineConsistency.PRANegUnderWitnessBound
