import DiophantineConsistency.Mixed121.W121.TemporalSourceWrapped
/-! Width-121 port of `Compact44/TemporalSourceStraddle` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.TemporalSourceStraddle
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem straddle (X n E t r : V) (ht : t<n)
    (hr0 : 0<r) (hr : r<121) (he : E%(121*n)=121*t+r)
    (hX : X<Exp.exp (121*n)) :
    let j := cyc n t t
    dig 121 (rot 1 (121*n) X (E%(121*n))) t =
      (dig 121 X j*Exp.exp r)%Exp.exp 121 + dig 121 X (cyc n j 1)/Exp.exp (121-r) := by
  let u := 121*(n-(t+1))
  have hn : 0<n := lt_of_le_of_lt (by simp : (0:V)≤t) ht
  have hN : 0<(121:V)*n := mul_pos (by norm_num) hn
  have hrr : r+(121-r)=121 := add_tsub_cancel_of_le (le_of_lt hr)
  have htn : (t+1)+(n-(t+1))=n := add_tsub_cancel_of_le (lt_iff_succ_le.mp ht)
  have hwin : 121*t+121+u=121*n := by
    calc
      _ = 121*((t+1)+(n-(t+1))) := by dsimp [u]; ring
      _ = 121*n := congrArg (fun z : V => 121*z) htn
  have hL : 121*n=E%(121*n)+((121-r)+u) := by
    calc
      _ = 121*t+121+u := hwin.symm
      _ = 121*t+(r+(121-r))+u := by rw [hrr]
      _ = (121*t+r)+((121-r)+u) := by ring
      _ = E%(121*n)+((121-r)+u) := by rw [he]
  have hn1 : n-1+1=n := tsub_add_cancel_of_le (pos_iff_one_le.mp hn)
  have hbase : 121*n+121*t=(121*t+r)+(121*(n-1)+(121-r)) := by
    calc
      _ = 121*((n-1)+1)+121*t := by rw [hn1]
      _ = 121*(n-1)+121+121*t := by ring
      _ = 121*(n-1)+(r+(121-r))+121*t := by rw [hrr]
      _ = (121*t+r)+(121*(n-1)+(121-r)) := by ring
  have heN : E%(121*n)≤121*n := le_of_lt (mod_lt _ hN)
  have hecancel : 121*n-E%(121*n)+E%(121*n)=121*n := tsub_add_cancel_of_le heN
  have hi : 121*n-E%(121*n)+121*t=121*(n-1)+(121-r) := by
    have hc : (121*n-E%(121*n)+121*t)+E%(121*n) = (121*(n-1)+(121-r))+E%(121*n) := by
      calc
        _ = (121*n-E%(121*n)+E%(121*n))+121*t := by ring
        _ = 121*n+121*t := by rw [hecancel]
        _ = (121*t+r)+(121*(n-1)+(121-r)) := hbase
        _ = (121*(n-1)+(121-r))+E%(121*n) := by rw [he]; ring
    exact add_right_cancel hc
  have hj : cyc n t t=0 := by rw [cyc_of_le ht ht (le_refl t), tsub_self]
  have hs : cyc n 0 1=n-1 := (cyc_one hn).1 rfl
  have h := W121.TemporalStraddleWindow.straddling X n E t r u hn hr0 hr he hL hi hX
  simpa only [hj,hs] using h
#print axioms W121.TemporalSourceStraddle.straddle
end W121.TemporalSourceStraddle
