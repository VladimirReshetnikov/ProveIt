import PA194RadixModel
import M6.Logic.RestrictedImplication

set_option autoImplicit false
set_option maxRecDepth 18000
set_option maxHeartbeats 4500000

namespace PA194RadixRestrictedImplication
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194RadixModel

universe u

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

noncomputable def implication (radix a b : M) : M := encode radix a b 0

theorem operands_le (radix a b : M) (hr : (1 : M) ≤ radix) :
    a ≤ implication radix a b ∧ b ≤ implication radix a b := by
  have hp : cantor a b ≤ radix*cantor a b := by
    simpa only [one_mul] using _root_.mul_le_mul_left hr (cantor a b)
  have he : cantor a b ≤ implication radix a b := by
    simpa [implication,encode] using hp
  exact ⟨le_trans (components_le a b).1 he,le_trans (components_le a b).2 he⟩

/-- The restricted axiom template uses only the numerical lower bounds on
    the two implication operands, not monotonicity of any recoding. -/
noncomputable def unrestricted (radix : M) (hr : (1 : M) ≤ radix)
    (Proof : M → Type u)
    (mp : ∀ {a b : M}, Proof (implication radix a b) → Proof a → Proof b)
    (row : ∀ a b c u : M, u ≤ a →
      Proof (implication radix (implication radix (implication radix c u) a)
        (implication radix (implication radix a c) (implication radix b c))))
    (a b c u : M) :
    Proof (implication radix (implication radix (implication radix c u) a)
      (implication radix (implication radix a c) (implication radix b c))) :=
  M6.Logic.RestrictedImplication.rho8All
    { mp := mp
      row := row
      refl := fun _ => le_rfl
      boundLeft := fun b h => le_trans h (operands_le radix _ b hr).1
      boundRight := fun a h => le_trans h (operands_le radix a _ hr).2 }
    a b c u

theorem unrestrictedProved (radix : M) (hr : (1 : M) ≤ radix)
    (proved : M → Prop)
    (mp : ∀ {a b : M}, proved (implication radix a b) → proved a → proved b)
    (row : ∀ a b c u : M, u ≤ a →
      proved (implication radix (implication radix (implication radix c u) a)
        (implication radix (implication radix a c) (implication radix b c))))
    (a b c u : M) :
    proved (implication radix (implication radix (implication radix c u) a)
      (implication radix (implication radix a c) (implication radix b c))) :=
  (unrestricted radix hr (fun n => PLift (proved n)) (fun f h => ⟨mp f.down h.down⟩)
    (fun a b c u h => ⟨row a b c u h⟩) a b c u).down

#print axioms operands_le
#print axioms unrestricted
#print axioms unrestrictedProved

end models
end PA194RadixRestrictedImplication
