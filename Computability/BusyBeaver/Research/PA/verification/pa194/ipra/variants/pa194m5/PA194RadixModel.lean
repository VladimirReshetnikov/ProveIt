import PA194MachineProjections

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4500000

namespace PA194RadixModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194MachineProjections

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

noncomputable def encode (radix left right tag : M) : M :=
  radix * cantor left right + tag

theorem quotient (radix left right tag : M) (ht : tag < radix) :
    encode radix left right tag / radix = cantor left right :=
  div_mul_add' (cantor left right) radix ht

theorem residue (radix left right tag : M) (ht : tag < radix) :
    encode radix left right tag % radix = tag := by
  rw [encode,mul_comm radix]
  exact mod_mul_add_of_lt _ _ ht

theorem decoded (radix left right tag : M) (ht : tag < radix) :
    let number := encode radix left right tag
    F fixedFirst ![number/radix] = left ∧ F fixedSecond ![number/radix] = right ∧
      number%radix = tag := by
  dsimp only
  rw [quotient radix left right tag ht,fixedFirst_model,first_cantor,
    fixedSecond_model,second_cantor,residue radix left right tag ht]
  exact ⟨rfl,rfl,rfl⟩

theorem componentDescent (radix left right tag : M) (hr : (2 : M) ≤ radix)
    (hpos : 0 < encode radix left right tag) :
    left < encode radix left right tag ∧ right < encode radix left right tag := by
  have hc : cantor left right < encode radix left right tag := by
    rcases zero_or_succ (cantor left right) with hz | ⟨pred,hpred⟩
    · simpa only [hz] using hpos
    · have hcpos : (0 : M) < cantor left right := by
        rw [hpred]
        exact lt_of_le_of_lt (zero_le) (lt_add_one _)
      have hdouble : cantor left right < cantor left right + cantor left right :=
        lt_add_of_pos_right _ hcpos
      have hmul : (2 : M)*cantor left right ≤ radix*cantor left right :=
        _root_.mul_le_mul_left hr (cantor left right)
      rw [two_mul] at hmul
      exact lt_of_lt_of_le hdouble (le_trans hmul (le_add_of_nonneg_right (zero_le : (0 : M) ≤ tag)))
  exact ⟨lt_of_le_of_lt (components_le left right).1 hc,
    lt_of_le_of_lt (components_le left right).2 hc⟩

theorem constructorInj (radix left right tag left' right' tag' : M)
    (ht : tag < radix) (ht' : tag' < radix)
    (h : encode radix left right tag = encode radix left' right' tag') :
    left = left' ∧ right = right' ∧ tag = tag' := by
  obtain ⟨hl,hr,hd⟩ := decoded radix left right tag ht
  obtain ⟨hl',hr',hd'⟩ := decoded radix left' right' tag' ht'
  rw [h] at hl hr hd
  exact ⟨hl.symm.trans hl',hr.symm.trans hr',hd.symm.trans hd'⟩

theorem reconstruct (radix number : M) :
    encode radix (F fixedFirst ![number/radix]) (F fixedSecond ![number/radix])
      (number%radix) = number := by
  rw [encode,fixedFirst_model,fixedSecond_model,cantor_projections]
  exact div_add_mod number radix

theorem decoderDescent (radix number : M) (hr : (2 : M) ≤ radix) (hp : 0 < number) :
    F fixedFirst ![number/radix] < number ∧ F fixedSecond ![number/radix] < number := by
  have ht := reconstruct radix number
  have h := componentDescent radix (F fixedFirst ![number/radix]) (F fixedSecond ![number/radix])
    (number%radix) hr (by rw [ht]; exact hp)
  simpa only [ht] using h

#print axioms decoded
#print axioms componentDescent
#print axioms constructorInj
#print axioms reconstruct
#print axioms decoderDescent
end models
end PA194RadixModel
