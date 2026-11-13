import DiophantineConsistency.TemporalSourceWrapped
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TemporalSourceStraddle
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem straddle (X n E t r : V) (ht : t<n)
    (hr0 : 0<r) (hr : r<67) (he : E%(67*n)=67*t+r)
    (hX : X<Exp.exp (67*n)) :
    let j := cyc n t t
    dig 67 (rot 1 (67*n) X (E%(67*n))) t =
      (dig 67 X j*Exp.exp r)%Exp.exp 67 + dig 67 X (cyc n j 1)/Exp.exp (67-r) := by
  let u := 67*(n-(t+1))
  have hn : 0<n := lt_of_le_of_lt (by simp : (0:V)≤t) ht
  have hN : 0<(67:V)*n := mul_pos (by norm_num) hn
  have hrr : r+(67-r)=67 := add_tsub_cancel_of_le (le_of_lt hr)
  have htn : (t+1)+(n-(t+1))=n := add_tsub_cancel_of_le (lt_iff_succ_le.mp ht)
  have hwin : 67*t+67+u=67*n := by
    calc
      _ = 67*((t+1)+(n-(t+1))) := by dsimp [u]; ring
      _ = 67*n := congrArg (fun z : V => 67*z) htn
  have hL : 67*n=E%(67*n)+((67-r)+u) := by
    calc
      _ = 67*t+67+u := hwin.symm
      _ = 67*t+(r+(67-r))+u := by rw [hrr]
      _ = (67*t+r)+((67-r)+u) := by ring
      _ = E%(67*n)+((67-r)+u) := by rw [he]
  have hn1 : n-1+1=n := tsub_add_cancel_of_le (pos_iff_one_le.mp hn)
  have hbase : 67*n+67*t=(67*t+r)+(67*(n-1)+(67-r)) := by
    calc
      _ = 67*((n-1)+1)+67*t := by rw [hn1]
      _ = 67*(n-1)+67+67*t := by ring
      _ = 67*(n-1)+(r+(67-r))+67*t := by rw [hrr]
      _ = (67*t+r)+(67*(n-1)+(67-r)) := by ring
  have heN : E%(67*n)≤67*n := le_of_lt (mod_lt _ hN)
  have hecancel : 67*n-E%(67*n)+E%(67*n)=67*n := tsub_add_cancel_of_le heN
  have hi : 67*n-E%(67*n)+67*t=67*(n-1)+(67-r) := by
    have hc : (67*n-E%(67*n)+67*t)+E%(67*n) = (67*(n-1)+(67-r))+E%(67*n) := by
      calc
        _ = (67*n-E%(67*n)+E%(67*n))+67*t := by ring
        _ = 67*n+67*t := by rw [hecancel]
        _ = (67*t+r)+(67*(n-1)+(67-r)) := hbase
        _ = (67*(n-1)+(67-r))+E%(67*n) := by rw [he]; ring
    exact add_right_cancel hc
  have hj : cyc n t t=0 := by rw [cyc_of_le ht ht (le_refl t), tsub_self]
  have hs : cyc n 0 1=n-1 := (cyc_one hn).1 rfl
  have h := TemporalStraddleWindow.straddling X n E t r u hn hr0 hr he hL hi hX
  simpa only [hj,hs] using h
#print axioms TemporalSourceStraddle.straddle
end TemporalSourceStraddle
