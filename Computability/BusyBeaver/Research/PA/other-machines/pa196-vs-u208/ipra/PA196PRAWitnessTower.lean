import PA196PRAQVecTowerPolynomial

/-! Transfer an IΣ₁ existential witness bound given by a polynomially
reparameterized tower to candidate-PRA witness bounds. -/
set_option autoImplicit false
namespace PA196PRAWitnessTower
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessTransfer PRAWitnessCalculus
  PA196PRAQVecTowerPolynomial PA196PAQVecTowerAlgebra PA196PASubstitutionTowerGraph
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_exs_towerPoly {n : ℕ} (ψ : ArithmeticSemisentence (n+1)) (hψ : Hierarchy 𝚺 1 ψ)
    (P : ArithmeticSemiterm Empty n)
    (hI : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) (x : V),
      ψ.Eval (x :> e) Empty.elim →
        ∃ x' ≤ iter (P.val e Empty.elim+2) (4*P.val e Empty.elim+1), ψ.Eval (x' :> e) Empty.elim)
    (hWB : WB M ψ) : WB M (∃⁰ ψ) := by
  apply wb_exs_bound ψ hψ (polyTowerGraph P) (polyTowerTerm P)
    (PRA_proves_polyTower_domination P) (polyTowerTerm_mono P) ?_ hWB
  intro V _ _ e x hx
  obtain ⟨x',hbound,hbody⟩ := hI V e x hx
  let t : V := iter (P.val e Empty.elim+2) (4*P.val e Empty.elim+1)
  refine ⟨t, ?_, x', hbound, hbody⟩
  apply (polyTowerGraph_eval P t e).mpr
  exact (towerGraph_eval t (P.val e Empty.elim)).mpr rfl

#print axioms wb_exs_towerPoly
end PA196PRAWitnessTower
