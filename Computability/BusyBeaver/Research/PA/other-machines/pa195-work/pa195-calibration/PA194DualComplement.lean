import PA194DualAtomCode
import PA194DualImpCode
import PA194DualForallCode

/-! Typed polarity invariants for the dual source-translation components.
These checks use Foundation's internal typed syntax and thus explicitly
assume IΣ₁. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace PA194DualComplement
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAHerbrandSelection PA194DualAtomCode PA194DualImpCode
  PA194DualForallCode PA194TemplateInternal

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem quoteNegBit [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    (⌜(Rew.emb ▹ (∼bitDef.val) : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2) =
      ∼(⌜(Rew.emb ▹ bitDef.val : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2) := by
  simp

/-- The two translated membership templates are logical negations after
Foundation's typed substitution, including for nonstandard labels. -/
theorem modelDualBitComplement [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (a b : M) :
    let φ := Bootstrapping.Semiformula.subst (substEnv a b 0)
      (⌜(Rew.emb ▹ bitDef.val : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)
    F dualBitCode ![a,b] = pair φ.val (∼φ).val := by
  dsimp only
  rw [modelDualBitInternal,quoteNegBit, Bootstrapping.Semiformula.substs_neg]

/-- Paired truth has complementary typed values. -/
theorem modelTruthComplement [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (n : M) :
    F dualTruthCode (fun _ => n) =
      pair (⊤ : Bootstrapping.Semiformula M ℒₒᵣ 0).val (∼(⊤ : Bootstrapping.Semiformula M ℒₒᵣ 0)).val := by
  rw [modelDualTruthInternal]
  simp

/-- The explicit equality/inequality code pair is a pair of complementary
typed formulas for arbitrary model-valued variable labels. -/
theorem modelDualEqComplement [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (a b : M) :
    let terms : Bootstrapping.SemitermVec M ℒₒᵣ 2 0 :=
      ![Bootstrapping.Semiterm.fvar a, Bootstrapping.Semiterm.fvar b]
    let φ : Bootstrapping.Semiformula M ℒₒᵣ 0 :=
      Bootstrapping.Semiformula.rel Language.ORing.Rel.eq terms
    F dualEqCode ![a,b] = pair φ.val (∼φ).val := by
  dsimp only
  rw [modelDualEqInternal]
  simp [Bootstrapping.Semiformula.rel_val, Bootstrapping.Semiformula.nrel_val,
    Bootstrapping.Semiformula.neg_rel, Bootstrapping.SemitermVec.val,
    Bootstrapping.Semiterm.fvar]
  change (0 : M) = ((Encodable.encode Language.ORing.Rel.eq : Nat) : M)
  rw [PA194EqAtomCode.equalitySymbolCode]
  simp

/-- The explicit PR implication code preserves a typed polarity invariant
for any two internally well-formed formulas. -/
theorem modelImpComplement [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (first second : Code 1)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (φ ψ : Bootstrapping.Semiformula M ℒₒᵣ 0) :
    F (dualImpCode first second) ![pair φ.val (∼φ).val,pair ψ.val (∼ψ).val] =
      pair (φ 🡒 ψ).val (∼(φ 🡒 ψ)).val := by
  rw [modelDualImpInternal first second hfirst hsecond]
  simp [Bootstrapping.Semiformula.imp_def]

/-- The quantifier wrapper preserves polarity if the supplied closing code
already maps both polarities to complementary correctly closed bodies. -/
theorem modelForallComplement [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (first second : Code 1) (close : Code 2)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label : M) (φ : Bootstrapping.Semiformula M ℒₒᵣ 0) (ψ : Bootstrapping.Semiformula M ℒₒᵣ 1)
    (hpos : F close ![label,φ.val] = ψ.val)
    (hneg : F close ![label,(∼φ).val] = (∼ψ).val) :
    F (dualForallCode first second close) ![label,pair φ.val (∼φ).val] =
      pair (∀⁰ ψ : Bootstrapping.Semiformula M ℒₒᵣ 0).val
        (∼(∀⁰ ψ : Bootstrapping.Semiformula M ℒₒᵣ 0)).val := by
  rw [modelDualForallInternal first second close hfirst hsecond, pi₁_pair,pi₂_pair,hpos,hneg]
  simp

#print axioms quoteNegBit
#print axioms modelDualBitComplement
#print axioms modelTruthComplement
#print axioms modelDualEqComplement
#print axioms modelImpComplement
#print axioms modelForallComplement
end models
end PA194DualComplement
