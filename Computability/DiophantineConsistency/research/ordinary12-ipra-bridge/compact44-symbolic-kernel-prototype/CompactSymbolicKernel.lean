import DiophantineConsistency.CompactCoefficientMass
set_option autoImplicit false
set_option Elab.async false
namespace CompactSymbolicKernel
open scoped BigOperators

def slots : List ℕ := [1023,1024,1025,1026,1027,1028,1029,1030,1013,1014,1015,1016,1017,1018,1019,1020,1021,1003,1004,1005,1006,1007,1008,1009,1010,983,984,985,986,987,988,989,990,991,1031,1022,1011,992,1095,2195,3296]
theorem slots_length : slots.length = 41 := by decide
theorem slots_bounded : slots.all (fun p => decide (p < 4393)) = true := by decide
def position (i : Fin 41) : ℕ := slots.get ⟨i.val, by simpa only [slots_length] using i.isLt⟩
theorem position_lt_target (i : Fin 41) : position i < 4393 := by
  have hm : position i ∈ slots := List.get_mem slots _
  exact of_decide_eq_true ((List.all_eq_true.mp slots_bounded) (position i) hm)
theorem row_lt_target (i : Fin 943) : i.val < 4393 := by
  exact lt_trans i.isLt (by decide)
def rho : ℕ := 2^67
def block : ℕ := rho^8807
def reflected (e c : ℕ) : ℕ := c*(rho^(4393-e)+rho^(5495-e))
def selectorTerms : ℕ := ∑ i : Fin 943, reflected i.val (CompactCoefficientMass.selector (Compact943Data.row i))
def copyTerms : ℕ := ∑ i : Fin 41, reflected (position i) (2^(10+i.val))
def bareTerms : ℕ := rho^30+rho^62+rho^1100+rho^2201
def kernelNat : ℕ := bareTerms+selectorTerms+copyTerms+block*rho^42
#print axioms CompactSymbolicKernel.position_lt_target
#print axioms CompactSymbolicKernel.row_lt_target
end CompactSymbolicKernel
