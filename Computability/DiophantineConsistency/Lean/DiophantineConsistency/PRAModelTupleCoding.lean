import DiophantineConsistency.PRAModelIOpenPairing
set_option autoImplicit false
namespace DiophantineConsistency.PRAModelTupleCoding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

section generic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem projection_le : ∀ {n : ℕ} (i : Fin n) (t : V), unNpair i t ≤ t := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i t
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [unNpair]
    · simpa [unNpair] using le_trans (ih i (π₂ t)) (pi₂_le_self t)
end generic

open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelTuple (n : ℕ) (v : Fin n → M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    ∀ i, unNpair i (npair v) = v i ∧ v i < npair v + 1 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  intro i
  refine ⟨unNpair_npair i v, ?_⟩
  apply lt_succ_iff_le.mpr
  simpa only [unNpair_npair] using projection_le i (npair v)
theorem tupleGraph_spec {n : ℕ} (i : Fin n) (x t : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    (Semiformula.lMap embedding (unNpairDef i).val).Eval ![x,t] Empty.elim ↔ x = unNpair i t := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [Semiformula.eval_lMap]
  rw [reduct_eq_standard]
  simp [(unNpair_defined i).iff]

/-- Every finite tuple has one code whose bounded projection graphs recover
all entries uniquely. This is an arbitrary-model fact, not a PR-code construction. -/
theorem modelTupleGraph (n : ℕ) (v : Fin n → M) :
    ∃ t : M, ∀ i,
      (Semiformula.lMap embedding (unNpairDef i).val).Eval ![v i,t] Empty.elim ∧
      Structure.rel (L := language) Language.ORing.Rel.lt
        ![v i, Structure.func (L := language) addCode ![t, Structure.func (L := language) oneCode Fin.elim0]] ∧
      ∀ x, (Semiformula.lMap embedding (unNpairDef i).val).Eval ![x,t] Empty.elim → x = v i := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  refine ⟨npair v, fun i => ?_⟩
  refine ⟨(tupleGraph_spec i (v i) _).mpr (unNpair_npair i v).symm, ?_, ?_⟩
  · change v i < npair v + 1
    exact (modelTuple n v i).2
  · intro x h
    exact (tupleGraph_spec i x _).mp h |>.trans (unNpair_npair i v)
end models
end DiophantineConsistency.PRAModelTupleCoding
