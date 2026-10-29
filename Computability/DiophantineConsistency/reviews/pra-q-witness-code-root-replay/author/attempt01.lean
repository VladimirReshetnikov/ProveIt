import DiophantineConsistency.PRAQOrderWitness

/-! A single primitive-recursive function symbol for the order witness. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAQOrderWitnessCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAQOrderWitness

def witnessCode : Code 2 := .comp predCode
  (.cons (.comp subCode (.cons (.proj 1) (.cons (.proj 0) (.nil 2)))) (.nil 2))

theorem witnessCode_primrec : Primrec (eval witnessCode) := eval_primrec witnessCode

theorem eval_witnessCode (x y : ℕ) :
    eval witnessCode (x ::ᵥ y ::ᵥ List.Vector.nil) = (y-x).pred := by
  change eval predCode (eval subCode (y ::ᵥ x ::ᵥ List.Vector.nil) ::ᵥ List.Vector.nil) = _
  rw [eval_subCode, eval_predCode]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelWitnessCode (x y : M) :
    Structure.func (L := language) witnessCode ![x,y] =
      Structure.func (L := language) predCode (fun _ =>
        Structure.func (L := language) subCode ![y,x]) := by
  have h := modelComposition (M := M) predCode
    (.cons (.comp subCode (.cons (.proj 1) (.cons (.proj 0) (.nil 2)))) (.nil 2)) ![x,y]
  have hs := modelSwapComposition (M := M) subCode x y
  have ha : (fun i => Structure.func (L := language)
      (getCode (.cons (.comp subCode (.cons (.proj 1) (.cons (.proj 0) (.nil 2)))) (.nil 2)) i) ![x,y]) =
      fun _ => Structure.func (L := language) subCode ![y,x] := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    exact hs
  change Structure.func (L := language) witnessCode ![x,y] = _ at h
  rw [ha] at h
  exact h

theorem modelWitnessByCode (x y : M)
    (hxy : Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]) :
    Structure.func (L := language) addCode
      ![x, Structure.func (L := language) Code.succ (fun _ =>
        Structure.func (L := language) witnessCode ![x,y])] = y := by
  rw [modelWitnessCode]
  exact modelWitness x y hxy

end models
end DiophantineConsistency.PRAQOrderWitnessCode
