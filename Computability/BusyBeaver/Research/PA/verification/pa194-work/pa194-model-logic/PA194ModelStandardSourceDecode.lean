import PA194ModelClosedSepClassifier
import PA194SourceSeparation

set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

/-- Every standard scoped source-term code has a typed source term. -/
theorem standard_sourceTerm_quote_surjective (n t : ℕ)
    (ht : IsSemiterm SourceL n t) :
    ∃ u : SyntacticSemiterm SourceL n, (⌜u⌝ : ℕ) = t := by
  rcases PA194TermShiftModel.term_cases ht.isUTerm with ⟨z,rfl⟩ | ⟨x,rfl⟩
  · have hz : z < n := by simpa only [IsSemiterm.bvar] using ht
    refine ⟨.bvar ⟨z,hz⟩,?_⟩
    simp
  · refine ⟨.fvar x,?_⟩
    simp

theorem source_quote_rel_eq (n : ℕ) (a b : SyntacticSemiterm SourceL n) :
    (⌜(Semiformula.rel M6.PA.RelationalSource.Relation.eq ![a,b] : Semiproposition SourceL n)⌝ : ℕ) =
      ^rel (2 : ℕ) (0 : ℕ) ?[(⌜a⌝ : ℕ),(⌜b⌝ : ℕ)] := by
  simp [Semiformula.quote_rel, PA194SourceSearchCoding.relationEncodable,
    Matrix.vecHead,Matrix.vecTail,Function.comp_def,adjoin_def]
  constructor
  · rfl
  · exact ⟨rfl,rfl⟩

theorem source_quote_rel_mem (n : ℕ) (a b : SyntacticSemiterm SourceL n) :
    (⌜(Semiformula.rel M6.PA.RelationalSource.Relation.mem ![a,b] : Semiproposition SourceL n)⌝ : ℕ) =
      ^rel (2 : ℕ) (1 : ℕ) ?[(⌜a⌝ : ℕ),(⌜b⌝ : ℕ)] := by
  simp [Semiformula.quote_rel, PA194SourceSearchCoding.relationEncodable,
    Matrix.vecHead,Matrix.vecTail,Function.comp_def,adjoin_def]
  constructor
  · change ((1 : ℕ) : ℕ) = 1
    simp
  · exact ⟨rfl,rfl⟩

theorem source_quote_nrel_eq (n : ℕ) (a b : SyntacticSemiterm SourceL n) :
    (⌜(Semiformula.nrel M6.PA.RelationalSource.Relation.eq ![a,b] : Semiproposition SourceL n)⌝ : ℕ) =
      ^nrel (2 : ℕ) (0 : ℕ) ?[(⌜a⌝ : ℕ),(⌜b⌝ : ℕ)] := by
  simp [Semiformula.quote_nrel, PA194SourceSearchCoding.relationEncodable,
    Matrix.vecHead,Matrix.vecTail,Function.comp_def,adjoin_def]
  constructor
  · rfl
  · exact ⟨rfl,rfl⟩

theorem source_quote_nrel_mem (n : ℕ) (a b : SyntacticSemiterm SourceL n) :
    (⌜(Semiformula.nrel M6.PA.RelationalSource.Relation.mem ![a,b] : Semiproposition SourceL n)⌝ : ℕ) =
      ^nrel (2 : ℕ) (1 : ℕ) ?[(⌜a⌝ : ℕ),(⌜b⌝ : ℕ)] := by
  simp [Semiformula.quote_nrel, PA194SourceSearchCoding.relationEncodable,
    Matrix.vecHead,Matrix.vecTail,Function.comp_def,adjoin_def]
  constructor
  · change ((1 : ℕ) : ℕ) = 1
    simp
  · exact ⟨rfl,rfl⟩

theorem standard_sourceRel_quote_surjective (n k r v : ℕ)
    (hr : SourceL.IsRel k r) (hv : IsSemitermVec SourceL k n v) :
    ∃ p : Semiproposition SourceL n, (⌜p⌝ : ℕ) = ^rel k r v := by
  have hrange : r ∈ Set.range (Encodable.encode : SourceL.Rel k → ℕ) := by
    apply (Language.LORDefinable.rel_iff (L := SourceL)).mpr
    exact hr
  obtain ⟨R,rfl⟩ := hrange
  cases R with
  | eq =>
    obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv.isUTerm
    obtain ⟨hsa,hsb⟩ := IsSemitermVec.doubleton.mp hv
    obtain ⟨u,hu⟩ := standard_sourceTerm_quote_surjective n a hsa
    obtain ⟨w,hw⟩ := standard_sourceTerm_quote_surjective n b hsb
    refine ⟨.rel M6.PA.RelationalSource.Relation.eq ![u,w],?_⟩
    change (⌜(Semiformula.rel M6.PA.RelationalSource.Relation.eq ![u,w] : Semiproposition SourceL n)⌝ : ℕ) = ^rel (2 : ℕ) (0 : ℕ) ?[a,b]
    rw [←hu,←hw]
    exact source_quote_rel_eq n u w
  | mem =>
    obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv.isUTerm
    obtain ⟨hsa,hsb⟩ := IsSemitermVec.doubleton.mp hv
    obtain ⟨u,hu⟩ := standard_sourceTerm_quote_surjective n a hsa
    obtain ⟨w,hw⟩ := standard_sourceTerm_quote_surjective n b hsb
    refine ⟨.rel M6.PA.RelationalSource.Relation.mem ![u,w],?_⟩
    change (⌜(Semiformula.rel M6.PA.RelationalSource.Relation.mem ![u,w] : Semiproposition SourceL n)⌝ : ℕ) = ^rel (2 : ℕ) (1 : ℕ) ?[a,b]
    rw [←hu,←hw]
    exact source_quote_rel_mem n u w

theorem standard_sourceNRel_quote_surjective (n k r v : ℕ)
    (hr : SourceL.IsRel k r) (hv : IsSemitermVec SourceL k n v) :
    ∃ p : Semiproposition SourceL n, (⌜p⌝ : ℕ) = ^nrel k r v := by
  have hrange : r ∈ Set.range (Encodable.encode : SourceL.Rel k → ℕ) := by
    apply (Language.LORDefinable.rel_iff (L := SourceL)).mpr
    exact hr
  obtain ⟨R,rfl⟩ := hrange
  cases R with
  | eq =>
    obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv.isUTerm
    obtain ⟨hsa,hsb⟩ := IsSemitermVec.doubleton.mp hv
    obtain ⟨u,hu⟩ := standard_sourceTerm_quote_surjective n a hsa
    obtain ⟨w,hw⟩ := standard_sourceTerm_quote_surjective n b hsb
    refine ⟨.nrel M6.PA.RelationalSource.Relation.eq ![u,w],?_⟩
    change (⌜(Semiformula.nrel M6.PA.RelationalSource.Relation.eq ![u,w] : Semiproposition SourceL n)⌝ : ℕ) = ^nrel (2 : ℕ) (0 : ℕ) ?[a,b]
    rw [←hu,←hw]
    exact source_quote_nrel_eq n u w
  | mem =>
    obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv.isUTerm
    obtain ⟨hsa,hsb⟩ := IsSemitermVec.doubleton.mp hv
    obtain ⟨u,hu⟩ := standard_sourceTerm_quote_surjective n a hsa
    obtain ⟨w,hw⟩ := standard_sourceTerm_quote_surjective n b hsb
    refine ⟨.nrel M6.PA.RelationalSource.Relation.mem ![u,w],?_⟩
    change (⌜(Semiformula.nrel M6.PA.RelationalSource.Relation.mem ![u,w] : Semiproposition SourceL n)⌝ : ℕ) = ^nrel (2 : ℕ) (1 : ℕ) ?[a,b]
    rw [←hu,←hw]
    exact source_quote_nrel_mem n u w

/-- Every standard internally scoped relational source code quotes a typed formula. -/
theorem standard_sourceFormula_quote_surjective (p n : ℕ)
    (hp : IsSemiformula SourceL n p) :
    ∃ φ : Semiproposition SourceL n, (⌜φ⌝ : ℕ) = p := by
  induction p using Nat.strong_induction_on generalizing n with
  | h p ih =>
    rcases IsSemiformula.case_iff.mp hp with
      (⟨k,r,v,hr,hv,rfl⟩ | ⟨k,r,v,hr,hv,rfl⟩ | rfl | rfl |
       ⟨a,b,ha,hb,rfl⟩ | ⟨a,b,ha,hb,rfl⟩ | ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩)
    · exact standard_sourceRel_quote_surjective n k r v hr hv
    · exact standard_sourceNRel_quote_surjective n k r v hr hv
    · exact ⟨⊤, by simp⟩
    · exact ⟨⊥, by simp⟩
    · have hla : a < a ^⋏ b := by simp
      have hlb : b < a ^⋏ b := by simp
      obtain ⟨φ,hφ⟩ := ih a hla n ha
      obtain ⟨ψ,hψ⟩ := ih b hlb n hb
      exact ⟨φ ⋏ ψ, by simp [hφ,hψ]⟩
    · have hla : a < a ^⋎ b := by simp
      have hlb : b < a ^⋎ b := by simp
      obtain ⟨φ,hφ⟩ := ih a hla n ha
      obtain ⟨ψ,hψ⟩ := ih b hlb n hb
      exact ⟨φ ⋎ ψ, by simp [hφ,hψ]⟩
    · have hla : a < ^∀ a := by simp
      obtain ⟨φ,hφ⟩ := ih a hla (n+1) ha
      exact ⟨∀⁰ φ, by simp [hφ]⟩
    · have hla : a < ^∃ a := by simp
      obtain ⟨φ,hφ⟩ := ih a hla (n+1) ha
      exact ⟨∃⁰ φ, by simp [hφ]⟩

#print axioms standard_sourceFormula_quote_surjective
#print axioms standard_sourceRel_quote_surjective
#print axioms standard_sourceNRel_quote_surjective
#print axioms source_quote_rel_eq
#print axioms source_quote_rel_mem
#print axioms standard_sourceTerm_quote_surjective
end PA194ModelLogic
