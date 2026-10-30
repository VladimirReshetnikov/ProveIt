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
  apply PRASuccBoundCompleteness.proves_succ_bound (∼lenbitDef.val) (bnd (∼lenbitDef.val))
  intro M _ _ x p
  exact neg_lenbit_bound x p
end DiophantineConsistency.PRANegLenbitWitnessBound
