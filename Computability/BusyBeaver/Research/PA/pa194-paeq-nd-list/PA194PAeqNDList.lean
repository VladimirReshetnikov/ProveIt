import PA194PAeqNDSingle
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unnecessarySeqFocus false
namespace PA194PAeq.ND
open LO LO.FirstOrder
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

noncomputable def listTheoryProof {T : Theory language} {A : List (Sentence language)}
    {ψ : Sentence language}
    (d : Proof (A.map (fun φ => (φ : Proposition language))) (ψ : Proposition language))
    (hA : ∀ φ ∈ A, φ ∈ T) : T.Proof ψ := by
  let e := Derivation.toDerivation2 T d
  have h : T ⟹₂ insert (ψ : Proposition language) (∼Sequent.embed A).toFinset := by
    refine Derivation2.cast e ?_
    ext p
    simp [Sequent.embed, Semiformula.neg_eq]
    constructor
    · rintro (rfl | ⟨a,ha,hap⟩)
      · exact Or.inl rfl
      · right; refine ⟨a,ha,?_⟩
        have := congrArg Semiformula.neg hap
        simpa only [Semiformula.neg_neg] using this
    · rintro (rfl | ⟨a,ha,hap⟩)
      · exact Or.inl rfl
      · right; refine ⟨a,ha,?_⟩
        have := congrArg Semiformula.neg hap
        simpa only [Semiformula.neg_neg] using this
  exact Theory.Proof2.toProof (Derivation2.cutManyProof A hA h)

#print axioms listTheoryProof
end PA194PAeq.ND
