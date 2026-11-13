import DiophantineConsistency.DecodedOccupied
import DiophantineConsistency.ArithmeticModularCancellation
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DecodedSelectorShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactPartialBand CompactSymbolicKernel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem mod_add_mod' {n : V} (hn : 0<n) (x y : V) : (x%n+y)%n=(x+y)%n := by
  rw [mod_add hn, mod_eq_self_of_lt (mod_lt x hn), ← mod_add hn]

private theorem cyc_add_mod {n : V} (hn : 0<n) (k e : V) : (cyc n k e+e)%n=k%n := by
  unfold cyc
  rw [mod_add_mod' hn]
  have hle : e%n≤k+n := le_trans (le_of_lt (mod_lt e hn)) le_add_self
  have he : k+n-e%n+e=(k+n)+n*(e/n) := by
    calc
      _ = k+n-e%n+(n*(e/n)+e%n) := by rw [div_add_mod]
      _ = (k+n-e%n+e%n)+n*(e/n) := by ring
      _ = _ := by rw [tsub_add_cancel_of_le hle]
  rw [he,mod_add_mul' _ _ hn,mod_add_remove_right hn]

private theorem cyc_unique {n r k e : V} (hr : r<n) (h : (r+e)%n=k%n) : cyc n k e=r := by
  have hn : 0<n := lt_of_le_of_lt (Arithmetic.zero_le r) hr
  have he : cyc n k e % n = r % n := by
    apply ArithmeticModularCancellation.add_cancel hn
    rw [cyc_add_mod hn, h]
  simpa only [mod_eq_self_of_lt (cyc_lt hn k e),mod_eq_self_of_lt hr] using he

theorem cyclic_shift (n k T d : V) (hn : 0<n) (hd : d≤T) :
    cyc n ((k+d)%n) T = cyc n k (T-d) := by
  apply cyc_unique (cyc_lt hn k (T-d))
  have hsum : (cyc n k (T-d)+T)%n=(k+d)%n := by
    calc
      _ = ((cyc n k (T-d)+(T-d))+d)%n := by congr 1; rw [add_assoc, tsub_add_cancel_of_le hd]
      _ = (((cyc n k (T-d)+(T-d))%n)+d)%n := (mod_add_mod' hn _ _).symm
      _ = (k%n+d)%n := by rw [cyc_add_mod hn]
      _ = (k+d)%n := mod_add_mod' hn _ _
  simpa only [mod_mod_self _ _ hn] using hsum

theorem copy_is_shifted_selector (n C k : V) (T : ℕ) (j : Fin 41)
    (hn : 0<n) (hj : position j≤T) :
    copyDigit position n C k T j = selectorDigit n C ((k+(position j:V))%n) T ⟨0, by decide⟩ := by
  unfold copyDigit selectorDigit
  have hcast : (((T-position j):ℕ):V)=(T:V)-(position j:V) := by
    apply eq_tsub_of_add_eq
    exact_mod_cast (Nat.sub_add_cancel hj)
  rw [hcast]
  simp only [Nat.sub_zero]
  exact congrArg (dig 67 C) (cyclic_shift n k (T:V) (position j:V) hn (by exact_mod_cast hj)).symm

theorem decoded_occupied_shifts (n C k : V) (T : ℕ) (i : Fin 943)
    (hn : 0<n) (hT : 3296≤T)
    (hb : ∀ j, copyDigit position n C k T j≤1)
    (hw : (∑ j : Fin 41, (2:V)^j.val*copyDigit position n C k T j)=Compact943Decoder.tileValue (V:=V) i) :
    ∀ j : Fin 41, 34≤j.val → selectorDigit n C ((k+(position j:V))%n) T ⟨0, by decide⟩=1 := by
  intro j hj
  have hp := ForeignBandGeometry.copy_allowed j
  unfold ForeignBandGeometry.Allowed at hp
  have hjT : position j≤T := le_trans (by omega) hT
  rw [← copy_is_shifted_selector n C k T j hn hjT]
  exact DecodedOccupied.decoded_occupied n C k T i hb hw j hj
#print axioms DecodedSelectorShift.cyclic_shift
#print axioms DecodedSelectorShift.copy_is_shifted_selector
#print axioms DecodedSelectorShift.decoded_occupied_shifts
end DecodedSelectorShift
