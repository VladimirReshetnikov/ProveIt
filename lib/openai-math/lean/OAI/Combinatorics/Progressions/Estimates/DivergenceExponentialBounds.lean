import OAI.Combinatorics.Progressions.Dynamics.ModeThresholdLogBudget

namespace OAI

section

namespace Erdos3

theorem translationDivergence_le_exp (m n : ℕ) {K H S a b c : ℝ}
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hKa : K ≤ Real.exp a) (hHb : H ≤ Real.exp b) (hSc : S ≤ Real.exp c) :
    (m : ℝ)*(K*S+n*(K^2*H)) ≤ Real.exp (m+n+3*a+b+c+1) := by
  have hn : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hm : (m : ℝ) ≤ Real.exp m := by linarith [Real.add_one_le_exp (m : ℝ)]
  have hks : K*S ≤ Real.exp (a+c) := by rw [Real.exp_add]; gcongr
  have hnk : (n : ℝ)*(K^2*H) ≤ Real.exp (n+2*a+b) := by
    calc
      _ ≤ Real.exp n*((Real.exp a)^2*Real.exp b) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hs := add_le_exp_add_one (show 0 ≤ a+c by positivity) (show 0 ≤ (n : ℝ)+2*a+b by positivity) hks hnk
  calc
    _ ≤ Real.exp m*Real.exp (a+c+(n+2*a+b)+1) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem perturbationDivergence_le_exp (n : ℕ) {K H S a b c : ℝ}
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hKa : K ≤ Real.exp a) (hHb : H ≤ Real.exp b) (hSc : S ≤ Real.exp c) :
    1+2*K*S+(n : ℝ)*((2*K)^2*(H+1)) ≤ Real.exp (n+3*a+b+c+6) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hn : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have h2k : 2*K ≤ Real.exp (a+1) := by
    calc
      _ ≤ Real.exp 1*Real.exp a := by gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hh1 : H+1 ≤ Real.exp (b+1) := by simpa only [add_comm] using one_add_le_exp_succ hb hHb
  have hks : 2*K*S ≤ Real.exp (a+c+1) := by
    calc
      _ ≤ Real.exp (a+1)*Real.exp c := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hnk : (n : ℝ)*((2*K)^2*(H+1)) ≤ Real.exp (n+2*a+b+3) := by
    calc
      _ ≤ Real.exp n*((Real.exp (a+1))^2*Real.exp (b+1)) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hs := add_le_exp_add_one (show 0 ≤ a+c+1 by positivity) (show 0 ≤ (n : ℝ)+2*a+b+3 by positivity) hks hnk
  have hsum := one_add_le_exp_succ (show 0 ≤ a+c+1+(n+2*a+b+3)+1 by positivity) hs
  calc
    _ = 1+(2*K*S+(n : ℝ)*((2*K)^2*(H+1))) := by ring
    _ ≤ Real.exp (a+c+1+(n+2*a+b+3)+1+1) := hsum
    _ = _ := by congr 1; ring

end Erdos3

end

end OAI
