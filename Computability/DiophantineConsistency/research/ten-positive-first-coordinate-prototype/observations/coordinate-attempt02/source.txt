import DiophantineConsistency.ArithmeticPellFirstNorm

/-! Positive coordinate for a factored unscaled first root. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositiveFirstCoordinate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_coordinate (P K S0 b q t tau : V)
    (hP : S0≤P) (hq : 2≤q) (hb : 1≤b) (ht : 1≤t)
    (hK : 8*P+4≤K) (htau : P*K<tau) :
    ∃ s : V, 0<s ∧ tau+q*t*(b*K+1)=P*K+K+s+S0 := by
  have hPlt : P<8*P+4 := by
    calc
      P≤8*P := le_mul_of_one_le_left (by simp) (by norm_num)
      _<8*P+4 := by simp
  have hSK : S0<K := lt_of_le_of_lt hP (lt_of_lt_of_le hPlt hK)
  have hbK : K≤b*K := le_mul_of_one_le_left (by simp) hb
  have h2K : 2*K≤q*(b*K) := mul_le_mul hq hbK (by simp) (by simp)
  have hQ : q*(b*K)≤q*t*(b*K+1) := by
    calc
      q*(b*K)≤q*(b*K+1) := mul_le_mul_of_nonneg_left (by simp) (by simp)
      _≤q*t*(b*K+1) := by
        have he : q*(b*K+1)≤(q*(b*K+1))*t := le_mul_of_one_le_right (by simp) ht
        simpa only [mul_assoc,mul_comm,mul_left_comm] using he
  have hsmall : P*K+K+S0 < tau+q*t*(b*K+1) := by
    have ha : P*K+(K+S0)<tau+(K+K) :=
      add_lt_add htau (add_lt_add_of_le_of_lt le_rfl hSK)
    have hb' : tau+(K+K)≤tau+q*t*(b*K+1) := by
      have hh : K+K≤q*t*(b*K+1) := by
        simpa only [two_mul] using le_trans h2K hQ
      exact _root_.add_le_add (le_refl tau) hh
    exact lt_of_lt_of_le (by simpa only [add_assoc] using ha) hb'
  let s:=tau+q*t*(b*K+1)-(P*K+K+S0)
  have hs : 0<s := tsub_pos_iff_lt.mpr hsmall
  have he : s+(P*K+K+S0)=tau+q*t*(b*K+1) :=
    tsub_add_cancel_of_le (le_of_lt hsmall)
  refine ⟨s,hs,?_⟩
  calc
    tau+q*t*(b*K+1)=s+(P*K+K+S0) := he.symm
    _=P*K+K+s+S0 := by ring

#print axioms TenPositiveFirstCoordinate.positive_coordinate
end TenPositiveFirstCoordinate
