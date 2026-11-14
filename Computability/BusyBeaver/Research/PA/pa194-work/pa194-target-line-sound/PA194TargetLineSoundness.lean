import PA194TargetVectorJoin
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194TargetLineSoundness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194TargetCantor PA194TargetLeaves
 PA194TargetStep PA194TargetSound PA194TargetExtendedStep PA194ParamHistory PA194StackCode PA194StackHistory
 PA194TargetGuardedHistory PA194TargetVectorLength PA194TargetProofLeaf PA194TargetGeneralize PA194TargetReplay
 PA194TargetGate PA194TargetVectorJoin
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Seed (x : M) : Prop :=
  (∃ a b, x = F machineHead1 ![a,b]) ∨
  (∃ a b c, x = head2Value a b c) ∨
  (∃ a b c, x = head3Value a b c) ∨
  (∃ a b c, x = head4Value a b c) ∨
  (∃ a b, x = head5Value a b) ∨
  (∃ a b c, x = head6Value a b c) ∨
  (∃ a b c u, u ≤ a ∧ x = rho8Value a b c u) ∨
  (∃ a b c, c ≠ a ∧ c ≠ b ∧ x = oldBundleValue a b c) ∨
  (∃ a, x = diagonalValue a)

theorem seed_provable (x : M) (h : Seed x) : TargetProvable x := by
  rcases h with (⟨a,b,rfl⟩ | ⟨a,b,c,rfl⟩ | ⟨a,b,c,rfl⟩ | ⟨a,b,c,rfl⟩ |
    ⟨a,b,rfl⟩ | ⟨a,b,c,rfl⟩ | ⟨a,b,c,u,hu,rfl⟩ | ⟨a,b,c,ha,hb,rfl⟩ | ⟨a,rfl⟩)
  · exact head1_provable a b
  · exact head2_provable a b c
  · exact head3_provable a b c
  · exact head4_provable a b c
  · exact head5_provable a b
  · exact head6_provable a b c
  · exact rho8_provable a b c u hu
  · exact gate_provable a b c ha hb
  · exact diagonal_provable a

/-- Each numerical source line is a target seed, MP conclusion, or universal
conclusion with earlier premises. The actual controller-to-lines condition is
not assumed proved by this theorem. -/
theorem line_sound (lines : M)
    (hline : ∀ i < len lines, Seed lines.[i] ∨
      (∃ j < i, ∃ k < i, lines.[k] = impValue lines.[j] lines.[i]) ∨
      (∃ j < i, ∃ label, lines.[i] = allValue label lines.[j])) :
    ∀ i < len lines, TargetProvable lines.[i] := by
  haveI := targetProvable_definable (M := M)
  have hdef : 𝚺₁-Predicate (fun n : M => ∀ i < n, i < len lines → TargetProvable lines.[i]) := by
    definability
  have hall : ∀ n : M, ∀ i < n, i < len lines → TargetProvable lines.[i] := by
    intro n
    induction n using ISigma1.sigma1_succ_induction
    · exact hdef
    case zero => intro i hi; exact False.elim (not_lt_zero hi)
    case succ n ih =>
      intro i hi hil
      by_cases hlt : i < n
      · exact ih i hlt hil
      · have hieq : i = n := le_antisymm (lt_succ_iff_le.mp hi) (le_of_not_gt hlt)
        subst i
        rcases hline n hil with (hs | ⟨j,hj,k,hk,himp⟩ | ⟨j,hj,label,hall⟩)
        · exact seed_provable _ hs
        · have hminor := ih j hj (lt_trans hj hil)
          have hmajor := ih k hk (lt_trans hk hil)
          rw [himp] at hmajor
          exact mp_closed lines.[j] lines.[n] hminor hmajor
        · have hminor := ih j hj (lt_trans hj hil)
          rw [hall]
          exact generalize_closed label lines.[j] hminor
  intro i hi
  exact hall (len lines) i hi hi

#print axioms seed_provable
#print axioms line_sound
end models
end PA194TargetLineSoundness
