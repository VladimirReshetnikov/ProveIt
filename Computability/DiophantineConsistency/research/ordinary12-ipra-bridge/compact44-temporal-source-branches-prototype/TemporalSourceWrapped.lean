import DiophantineConsistency.TemporalSourceNonwrap
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TemporalSourceWrapped
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem wrapped (X n E t q r : V) (ht : t<n) (hq : q<n) (htq : t<q)
    (hr0 : 0<r) (hr : r<67) (he : E%(67*n)=67*q+r) :
    let j := cyc n t q
    dig 67 (rot 1 (67*n) X (E%(67*n))) t =
      (dig 67 X j*Exp.exp r)%Exp.exp 67 + dig 67 X (cyc n j 1)/Exp.exp (67-r) := by
  let j := n-q+t
  let s := j-1
  let u := 67*(q-(t+1))+r
  have hn : 0<n := lt_of_le_of_lt (by simp : (0:V)≤t) ht
  have hN : 0<(67:V)*n := mul_pos (by norm_num) hn
  have hj : cyc n t q=j := cyc_of_lt hq htq
  have hj0 : 0<j := add_pos_of_pos_of_nonneg (tsub_pos_iff_lt.mpr hq) (by simp)
  have hjn : j<n := by rw [←hj]; exact cyc_lt hn _ _
  have hsi : s+1=j := tsub_add_cancel_of_le (pos_iff_one_le.mp hj0)
  have hrr : r+(67-r)=67 := add_tsub_cancel_of_le (le_of_lt hr)
  have hqe : (t+1)+(q-(t+1))=q := add_tsub_cancel_of_le (lt_iff_succ_le.mp htq)
  have hw : E%(67*n)=67*t+67+u := by
    rw [he]
    calc
      _ = 67*((t+1)+(q-(t+1)))+r := by rw [hqe]
      _ = _ := by dsimp [u]; ring
  have hnq : q+(n-q)=n := add_tsub_cancel_of_le (le_of_lt hq)
  have hbase : 67*n+67*t=(67*q+r)+(67*s+(67-r)) := by
    calc
      _ = 67*((q+(n-q))+t) := by rw [hnq]; ring
      _ = 67*(q+j) := by dsimp [j]; ring
      _ = 67*(q+(s+1)) := by rw [hsi]
      _ = 67*q+67*s+(r+(67-r)) := by rw [hrr]; ring
      _ = _ := by ring
  have heN : E%(67*n)≤67*n := le_of_lt (mod_lt _ hN)
  have hecancel : 67*n-E%(67*n)+E%(67*n)=67*n := tsub_add_cancel_of_le heN
  have hi : 67*n-E%(67*n)+67*t=67*s+(67-r) := by
    have hc : (67*n-E%(67*n)+67*t)+E%(67*n) = (67*s+(67-r))+E%(67*n) := by
      calc
        _ = (67*n-E%(67*n)+E%(67*n))+67*t := by ring
        _ = 67*n+67*t := by rw [hecancel]
        _ = (67*q+r)+(67*s+(67-r)) := hbase
        _ = (67*s+(67-r))+E%(67*n) := by rw [he]; ring
    exact add_right_cancel hc
  have hs : cyc n j 1=s := (cyc_one hjn).2 hj0
  have h := TemporalOtherWindows.wrapped X n E t s r u hr0 hr hw hi
  rw [hsi, ←hs] at h
  simpa only [hj] using h
#print axioms TemporalSourceWrapped.wrapped
end TemporalSourceWrapped
