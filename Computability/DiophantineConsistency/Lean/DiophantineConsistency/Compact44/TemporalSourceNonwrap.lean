import DiophantineConsistency.Compact44.TemporalStraddleWindow
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TemporalSourceNonwrap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem nonwrap (X n E t q r : V) (ht : t<n) (hq : q<n) (hqt : q<t)
    (hr0 : 0<r) (hr : r<67) (he : E%(67*n)=67*q+r)
    (hX : X<Exp.exp (67*n)) :
    let j := cyc n t q
    dig 67 (rot 1 (67*n) X (E%(67*n))) t =
      (dig 67 X j*Exp.exp r)%Exp.exp 67 + dig 67 X (cyc n j 1)/Exp.exp (67-r) := by
  let j := t-q
  let s := j-1
  let u := 67*(n-(t+1))
  have hi0 : 0<j := tsub_pos_iff_lt.mpr hqt
  have hin : j<n := lt_of_le_of_lt tsub_le_self ht
  have hqi : q+j=t := add_tsub_cancel_of_le (le_of_lt hqt)
  have hsi : s+1=j := tsub_add_cancel_of_le (pos_iff_one_le.mp hi0)
  have hrr : r+(67-r)=67 := add_tsub_cancel_of_le (le_of_lt hr)
  have hti : 67*t=(67*q+r)+(67*s+(67-r)) := by
    calc
      _ = 67*(q+(s+1)) := by rw [hsi,hqi]
      _ = 67*q+67*s+(r+(67-r)) := by rw [hrr]; ring
      _ = _ := by ring
  have htn : (t+1)+(n-(t+1))=n := add_tsub_cancel_of_le (lt_iff_succ_le.mp ht)
  have hwin : 67*t+67+u=67*n := by
    calc
      _ = 67*((t+1)+(n-(t+1))) := by dsimp [u]; ring
      _ = 67*n := congrArg (fun z : V => 67*z) htn
  have ht' : 67*t=E%(67*n)+(67*s+(67-r)) := by rw [he]; exact hti
  have hL : 67*n=E%(67*n)+(67*s+(67-r)+67+u) := by
    calc
      _ = 67*t+67+u := hwin.symm
      _ = (E%(67*n)+(67*s+(67-r)))+67+u := by rw [←ht']
      _ = E%(67*n)+(67*s+(67-r)+67+u) := by ring
  have hi : cyc n t q=j := cyc_of_le ht hq (le_of_lt hqt)
  have hs : cyc n j 1=s := (cyc_one hin).2 hi0
  have h := TemporalWindowFormula.nonwrap X n E t s r u hr0 hr hL ht' hX
  rw [hsi, ←hs] at h
  simpa only [hi] using h
#print axioms TemporalSourceNonwrap.nonwrap
end TemporalSourceNonwrap
