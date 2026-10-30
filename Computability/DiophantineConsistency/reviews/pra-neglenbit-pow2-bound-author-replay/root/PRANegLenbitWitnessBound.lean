import DiophantineConsistency.PRALenbitWitnessBound
/-! A local witness bound for the negated Foundation lenbit graph, used
    inside sppow2Def. This does not bound the complete sppow2Def graph. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegLenbitWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem neg_lenbit_bound (i a : V) :
    (∼lenbitDef.val).Evalb ![i,a] →
      (bnd (∼lenbitDef.val)).Evalb ![i,a,a+1] := by
  intro h
  simp [lenbitDef, divDef, dvd, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    FirstOrder.bexs, bnd, bnd_open, Rew.subst, Rew.q] at h ⊢
  intro x
  by_cases hx : a+1 ≤ x
  · exact Or.inl hx
  · rcases h x with hbig | hdiv | ⟨z,hz,heq⟩
    · exact (hx hbig).elim
    · exact Or.inr (Or.inl hdiv)
    · right
      right
      have hxa : x ≤ a := lt_succ_iff_le.mp (lt_of_not_ge hx)
      refine ⟨z, lt_of_lt_of_le hz (by simpa [add_comm] using add_le_add_right hxa 1), hz, heq⟩

open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
section candidate
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- The exact graph bound in every candidate-PRA model. -/
theorem candidate_neg_lenbit_bound (x p : M) :
    (Semiformula.lMap embedding (∼lenbitDef.val)).Eval ![x,p] Empty.elim →
    (Semiformula.lMap embedding (bnd (∼lenbitDef.val))).Eval ![x,p,p+1] Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  intro h
  rw [Semiformula.eval_lMap] at h ⊢
  rw [reduct_eq_standard] at h ⊢
  exact neg_lenbit_bound x p h
end candidate

def boundBody : Semisentence language 2 :=
  (Semiformula.lMap embedding (∼lenbitDef.val)) 🡒
    (Rew.subst ![#0, #1, applyCode addCode ![#1, applyCode oneCode Fin.elim0]] ▹
      Semiformula.lMap embedding (bnd (∼lenbitDef.val)))

def boundSentence : Sentence language := ∀⁰* boundBody

/-- Candidate PRA proves the universally closed graph-bound sentence. -/
theorem candidate_proves_neg_lenbit_bound : PRA ⊢ boundSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  simp only [models_iff, boundSentence, Semiformula.eval_allClosure]
  intro e
  simp only [boundBody, LogicalConnective.HomClass.map_imply]
  intro he
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  have he' : (Semiformula.lMap embedding (∼lenbitDef.val)).Eval ![e 0,e 1] Empty.elim := by
    have hv : ![e 0,e 1] = e := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      exact Fin.cases rfl (fun j => Fin.elim0 j) j
    rw [hv]
    exact he
  have hb := candidate_neg_lenbit_bound (e 0) (e 1) he'
  simp only [Semiformula.eval_rew]
  have hv : (Semiterm.val e Empty.elim ∘
        (Rew.subst ![#0, #1, applyCode addCode ![#1, applyCode oneCode Fin.elim0]]) ∘ Semiterm.bvar) =
      ![e 0, e 1, e 1+1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    simp [Function.comp_def, Rew.subst, applyCode, Semiterm.val_func]
    congr 1
    funext k
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases ?_ (fun k => Fin.elim0 k) k
    change Structure.func (L := language) oneCode
      (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 2)) =
      Structure.func (L := language) oneCode Fin.elim0
    congr 1
    exact Subsingleton.elim _ _
  have hf : (Semiterm.val e Empty.elim ∘
        (Rew.subst ![#0, #1, applyCode addCode ![#1, applyCode oneCode Fin.elim0]]) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,hf]
  exact hb
end DiophantineConsistency.PRANegLenbitWitnessBound
