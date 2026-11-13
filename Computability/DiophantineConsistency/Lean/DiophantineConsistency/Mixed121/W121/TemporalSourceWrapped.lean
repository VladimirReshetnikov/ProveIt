import DiophantineConsistency.Mixed121.W121.TemporalSourceNonwrap
/-! Width-121 port of `Compact44/TemporalSourceWrapped` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.TemporalSourceWrapped
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem wrapped (X n E t q r : V) (ht : t<n) (hq : q<n) (htq : t<q)
    (hr0 : 0<r) (hr : r<121) (he : E%(121*n)=121*q+r) :
    let j := cyc n t q
    dig 121 (rot 1 (121*n) X (E%(121*n))) t =
      (dig 121 X j*Exp.exp r)%Exp.exp 121 + dig 121 X (cyc n j 1)/Exp.exp (121-r) := by
  let j := n-q+t
  let s := j-1
  let u := 121*(q-(t+1))+r
  have hn : 0<n := lt_of_le_of_lt (by simp : (0:V)≤t) ht
  have hN : 0<(121:V)*n := mul_pos (by norm_num) hn
  have hj : cyc n t q=j := cyc_of_lt hq htq
  have hj0 : 0<j := add_pos_of_pos_of_nonneg (tsub_pos_iff_lt.mpr hq) (by simp)
  have hjn : j<n := by rw [←hj]; exact cyc_lt hn _ _
  have hsi : s+1=j := tsub_add_cancel_of_le (pos_iff_one_le.mp hj0)
  have hrr : r+(121-r)=121 := add_tsub_cancel_of_le (le_of_lt hr)
  have hqe : (t+1)+(q-(t+1))=q := add_tsub_cancel_of_le (lt_iff_succ_le.mp htq)
  have hw : E%(121*n)=121*t+121+u := by
    rw [he]
    calc
      _ = 121*((t+1)+(q-(t+1)))+r := by rw [hqe]
      _ = _ := by dsimp [u]; ring
  have hnq : q+(n-q)=n := add_tsub_cancel_of_le (le_of_lt hq)
  have hbase : 121*n+121*t=(121*q+r)+(121*s+(121-r)) := by
    calc
      _ = 121*((q+(n-q))+t) := by rw [hnq]; ring
      _ = 121*(q+j) := by dsimp [j]; ring
      _ = 121*(q+(s+1)) := by rw [hsi]
      _ = 121*q+121*s+(r+(121-r)) := by rw [hrr]; ring
      _ = _ := by ring
  have heN : E%(121*n)≤121*n := le_of_lt (mod_lt _ hN)
  have hecancel : 121*n-E%(121*n)+E%(121*n)=121*n := tsub_add_cancel_of_le heN
  have hi : 121*n-E%(121*n)+121*t=121*s+(121-r) := by
    have hc : (121*n-E%(121*n)+121*t)+E%(121*n) = (121*s+(121-r))+E%(121*n) := by
      calc
        _ = (121*n-E%(121*n)+E%(121*n))+121*t := by ring
        _ = 121*n+121*t := by rw [hecancel]
        _ = (121*q+r)+(121*s+(121-r)) := hbase
        _ = (121*s+(121-r))+E%(121*n) := by rw [he]; ring
    exact add_right_cancel hc
  have hs : cyc n j 1=s := (cyc_one hjn).2 hj0
  have h := W121.TemporalOtherWindows.wrapped X n E t s r u hr0 hr hw hi
  rw [hsi, ←hs] at h
  simpa only [hj] using h
#print axioms W121.TemporalSourceWrapped.wrapped
end W121.TemporalSourceWrapped
