import DiophantineConsistency.Sign17KRankedRawWord

/-! SOURCE-ONLY: symbolic control blocks and their finite literal vector. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KControlBlocks

def south (i : Fin 9) : ℕ := 2 * 2 ^ (35 + i.val)
def gap9 (_ : Fin 9) : ℕ := 0
def north (i : Fin 9) : ℕ := 2 * 2 ^ (18 + i.val)
def east (i : Fin 8) : ℕ := 2 * 2 ^ (27 + i.val)
def gap1 (_ : Fin 1) : ℕ := 0
def west (i : Fin 8) : ℕ := 2 * 2 ^ (10 + i.val)

def symbolic : Fin 44 → ℕ := Fin.append south (Fin.append gap9
  (Fin.append north (Fin.append east (Fin.append gap1 west))))

def literal : Fin 44 → ℕ := ![68719476736, 137438953472, 274877906944, 549755813888, 1099511627776, 2199023255552, 4398046511104, 8796093022208, 17592186044416, 0, 0, 0, 0, 0, 0, 0, 0, 0, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864, 134217728, 268435456, 536870912, 1073741824, 2147483648, 4294967296, 8589934592, 17179869184, 34359738368, 0, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144]

theorem symbolic_eq_literal (i : Fin 44) : symbolic i = literal i := by
  fin_cases i <;> decide +kernel

end DiophantineConsistency.Sign17KControlBlocks
#print axioms DiophantineConsistency.Sign17KControlBlocks.symbolic_eq_literal
