import DiophantineConsistency.ControllerRankStride

namespace DiophantineConsistency.ControllerRankStrideChecks
open ControllerRankStride
set_option Elab.async false

-- d=5,N=3,R=50,s=1 gives t=7, not the canonical representative1.
example : stride 5 3 50 = 7 := by decide
example : 0 < stride 5 3 50 ∧ 5*stride 5 3 50 = 50-5*3 ∧
    (stride 5 3 50 : ZMod 3) = 1 :=
  stride_spec (by decide) (by decide) (by decide : 2*(5*3)<50)
    (by decide : 50 ≡ 5*1 [MOD 5*3])
example : (stride 5 3 50 : ZMod 3).val = 1 :=
  stride_value (by decide) (by decide) (by decide) (by decide)
    (by decide : 50 ≡ 5*1 [MOD 5*3])

-- N=1 and residue zero are included; the derived stride is still positive.
example : ∃ t : ℕ, 0<t ∧ 7*t = 21-7*1 ∧ (t : ZMod 1)=0 :=
  exists_stride (by decide) (by decide) (by decide)
    (by decide : 21 ≡ 7*0 [MOD 7*1])

-- No s<N assumption: the supplied stride may already include full periods.
example : (stride 5 3 50 : ZMod 3) = (7 : ZMod 3) :=
  (stride_spec (by decide) (by decide) (by decide)
    (by decide : 50 ≡ 5*7 [MOD 5*3])).2.2

-- Congruence is essential; dropping it need not leave a divisible exponent.
example : ¬5 ∣ (51-5*3) := by decide
-- At R=d*N the forced exponent/stride is zero; positivity needs growth.
example : stride 5 3 15 = 0 := by decide

#print axioms rank_dvd
#print axioms quotient_mod
#print axioms quotient_gt
#print axioms stride_mul
#print axioms stride_quotient
#print axioms stride_mod
#print axioms stride_spec
#print axioms stride_value
#print axioms exists_stride

end DiophantineConsistency.ControllerRankStrideChecks
