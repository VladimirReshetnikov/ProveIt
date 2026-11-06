import DiophantineConsistency.Mixed121.W121.TemporalStraddleWindow
/-! Width-121 port of `Compact44/TemporalSourceNonwrap` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.TemporalSourceNonwrap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem nonwrap (X n E t q r : V) (ht : t<n) (hq : q<n) (hqt : q<t)
    (hr0 : 0<r) (hr : r<121) (he : E%(121*n)=121*q+r)
    (hX : X<Exp.exp (121*n)) :
    let j := cyc n t q
    dig 121 (rot 1 (121*n) X (E%(121*n))) t =
      (dig 121 X j*Exp.exp r)%Exp.exp 121 + dig 121 X (cyc n j 1)/Exp.exp (121-r) := by
  let j := t-q
  let s := j-1
  let u := 121*(n-(t+1))
  have hi0 : 0<j := tsub_pos_iff_lt.mpr hqt
  have hin : j<n := lt_of_le_of_lt tsub_le_self ht
  have hqi : q+j=t := add_tsub_cancel_of_le (le_of_lt hqt)
  have hsi : s+1=j := tsub_add_cancel_of_le (pos_iff_one_le.mp hi0)
  have hrr : r+(121-r)=121 := add_tsub_cancel_of_le (le_of_lt hr)
  have hti : 121*t=(121*q+r)+(121*s+(121-r)) := by
    calc
      _ = 121*(q+(s+1)) := by rw [hsi,hqi]
      _ = 121*q+121*s+(r+(121-r)) := by rw [hrr]; ring
      _ = _ := by ring
  have htn : (t+1)+(n-(t+1))=n := add_tsub_cancel_of_le (lt_iff_succ_le.mp ht)
  have hwin : 121*t+121+u=121*n := by
    calc
      _ = 121*((t+1)+(n-(t+1))) := by dsimp [u]; ring
      _ = 121*n := congrArg (fun z : V => 121*z) htn
  have ht' : 121*t=E%(121*n)+(121*s+(121-r)) := by rw [he]; exact hti
  have hL : 121*n=E%(121*n)+(121*s+(121-r)+121+u) := by
    calc
      _ = 121*t+121+u := hwin.symm
      _ = (E%(121*n)+(121*s+(121-r)))+121+u := by rw [←ht']
      _ = E%(121*n)+(121*s+(121-r)+121+u) := by ring
  have hi : cyc n t q=j := cyc_of_le ht hq (le_of_lt hqt)
  have hs : cyc n j 1=s := (cyc_one hin).2 hi0
  have h := W121.TemporalWindowFormula.nonwrap X n E t s r u hr0 hr hL ht' hX
  rw [hsi, ←hs] at h
  simpa only [hi] using h
#print axioms W121.TemporalSourceNonwrap.nonwrap
end W121.TemporalSourceNonwrap
