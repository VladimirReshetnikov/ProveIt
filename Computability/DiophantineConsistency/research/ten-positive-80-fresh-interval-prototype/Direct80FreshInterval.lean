import PellSandwichFloor
import Direct80SandwichBoth
import Direct80SymbolicPortBounds
import DiophantineConsistency.ArithmeticHalfBinomialSandwich

/-! A fresh unscaled first/main Pell pair has the actual graph's integer floor. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80FreshInterval
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open ArithmeticPellRecurrence ArithmeticPow ArithmeticHalfBinomial ArithmeticHalfBinomialSandwich
open CompactFixedBeta CompactSymbolicPorts
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80RankLower
open TenPositive80SymbolicPortBounds TenPositive80SandwichBoth TenPositivePellSandwichFloor
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_fresh_interval (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ r : V, 0 < r ∧ rankNat p v=2*r+1 ∧
      let X0:=X p v
      let Y0:=Y p v
      let K:=2*ycoord (r+1) (2*(X0*Y0*Y0-1)+1)
      let C:=ycoord (2*r+1) (Y0*(X0+1))
      K*Y0<C ∧ C<K*(Y0+1) := by
  obtain ⟨h31,hl,hh,hodd⟩ := fixed_bounds (V:=V) p hp0 hp2 hp3
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num) h31
  obtain ⟨r,hr,hR,hXeq,hlow,hup⟩ := graph_sandwich_both p v h31 hl hh hv hz hodd
  have hRlo := (graph_rank_lower p v h31 (hv 0) (hv 2) (hv 5)).2.2
  have hr15 := half_rank_ge_fifteen (rankNat p v) r hRlo hR
  have hr4 : 4≤r := le_trans (by norm_num) hr15
  have h72 : 72*r<X p v+1 := by
    have h := seventy_two_lt_exp r hr4
    rw [←hXeq] at h
    exact lt_of_lt_of_le h (by simp)
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hX1 : 1≤X p v := pos_iff_one_le.mp hX
  have hY1 : 1≤Y p v := pos_iff_one_le.mp hY
  have hr1 : 1≤r := pos_iff_one_le.mp hr
  have hsplit := split_floor (X p v) (Y p v) r (v 8) (v 9) (k v) (c p v)
    hr hXeq rfl rfl (hv 8) (hv 9) hlow hup
  have hN : power (X p v+1) (2*r)<2*(Y p v+1)*power (X p v) r := by
    obtain ⟨rem,hrem,heq⟩ := hsplit
    rw [heq]
    calc
      2*Y p v*power (X p v) r+rem<2*Y p v*power (X p v) r+power (X p v) r :=
        add_lt_add_of_le_of_lt le_rfl hrem
      _≤2*(Y p v+1)*power (X p v) r := by
        have e : 2*(Y p v+1)*power (X p v) r =
          (2*Y p v*power (X p v) r+power (X p v) r)+power (X p v) r := by ring
        rw [e]; simp
  have hfl := sandwich_lower (X p v) (Y p v) r hX1 hY1 hr1
  have hfu := sandwich_upper (X p v) (Y p v) r hX1 hY1 hr1 h72 hN
  refine ⟨r,hr,hR,?_⟩
  exact transfer_floor (Y p v) (power (X p v+1) (2*r)) (power (X p v) r)
    (2*ycoord (r+1) (2*(X p v*Y p v*Y p v-1)+1))
    (ycoord (2*r+1) (Y p v*(X p v+1))) hsplit hfl hfu

#print axioms TenPositive80FreshInterval.graph_fresh_interval
end TenPositive80FreshInterval
