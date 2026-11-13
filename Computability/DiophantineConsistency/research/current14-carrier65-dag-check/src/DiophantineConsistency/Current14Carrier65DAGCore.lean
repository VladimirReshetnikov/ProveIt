import DiophantineConsistency.ArithmeticDAG

/-!
Source-only candidate: 65 binary gates, with arbitrary input and port values.
The graph transcription and all proof bodies still require review and Lean checking.
External graph SHA256: bf58ed6600eee34d86a802a992e3fd9b999e1835b57a5a83734a40073e1658a7
-/
namespace DiophantineConsistency.Current14Carrier65DAG
open ArithmeticDAG

def nodes : List (Node 14 4) :=
  [
    .input ⟨0, by decide⟩, -- 0: J
    .input ⟨1, by decide⟩, -- 1: F
    .input ⟨2, by decide⟩, -- 2: alpha
    .input ⟨3, by decide⟩, -- 3: z
    .input ⟨4, by decide⟩, -- 4: f
    .input ⟨5, by decide⟩, -- 5: i
    .input ⟨6, by decide⟩, -- 6: T
    .input ⟨7, by decide⟩, -- 7: s
    .input ⟨8, by decide⟩, -- 8: w
    .input ⟨9, by decide⟩, -- 9: n
    .input ⟨10, by decide⟩, -- 10: eta
    .input ⟨11, by decide⟩, -- 11: zeta
    .input ⟨12, by decide⟩, -- 12: y
    .input ⟨13, by decide⟩, -- 13: gamma
    .constant ⟨0, by decide⟩, -- 14: beta
    .constant ⟨1, by decide⟩, -- 15: K0
    .constant ⟨2, by decide⟩, -- 16: MC
    .constant ⟨3, by decide⟩, -- 17: MF
    .literal 1, -- 18: 1
    .literal 3, -- 19: 3
    .literal 4, -- 20: 4
    .mul 14 0, -- 21: qm
    .add 21 18, -- 22: q
    .mul 22 22, -- 23: q2
    .mul 23 22, -- 24: q3
    .mul 8 22, -- 25: X
    .mul 7 24, -- 26: Y
    .mul 25 26, -- 27: E
    .add 10 11, -- 28: k
    .mul 28 26, -- 29: kY
    .mul 27 29, -- 30: ell
    .add 29 10, -- 31: c
    .add 27 26, -- 32: a
    .mul 20 32, -- 33: four_a
    .add 33 19, -- 34: H
    .mul 32 32, -- 35: a2
    .add 35 34, -- 36: Delta
    .mul 32 31, -- 37: ac
    .add 25 37, -- 38: main_base
    .mul 13 34, -- 39: gammaH
    .add 38 39, -- 40: main_root
    .mul 31 31, -- 41: c2
    .mul 36 41, -- 42: Dc2
    .mul 40 40, -- 43: main_square
    .sub 43 42, -- 44: N1
    .sub 22 1, -- 45: qF
    .sub 45 2, -- 46: C
    .mul 21 45, -- 47: gap_product
    .add 47 2, -- 48: gap
    .sub 23 18, -- 49: q2minus1
    .mul 48 49, -- 50: rproduct
    .mul 22 17, -- 51: qMF
    .add 16 51, -- 52: maskfactor
    .mul 52 0, -- 53: mask
    .add 50 53, -- 54: R
    .mul 27 9, -- 55: En
    .add 55 28, -- 56: tau_partial
    .sub 56 54, -- 57: tau
    .mul 57 57, -- 58: tau2
    .add 30 28, -- 59: ell_plus_k
    .mul 30 59, -- 60: first_product
    .sub 58 60, -- 61: N0
    .add 15 8, -- 62: Kw
    .mul 62 46, -- 63: transport
    .add 63 45, -- 64: transport_partial
    .mul 3 21, -- 65: zqm
    .sub 64 65, -- 66: Nt
    .mul 4 4, -- 67: f2
    .mul 31 6, -- 68: cT
    .sub 68 54, -- 69: cTminusR
    .mul 67 69, -- 70: f2inner
    .sub 70 31, -- 71: V
    .mul 5 42, -- 72: normalized_S
    .mul 72 72, -- 73: normalized_S2
    .mul 71 71, -- 74: V2
    .mul 12 12, -- 75: y2
    .sub 74 75, -- 76: V2minusY2
    .mul 73 76, -- 77: aux_product
    .add 77 75, -- 78: Na
    .mul 36 67, -- 79: scaled_f2
    .sub 79 73, -- 80: scaled_Ns
    .mul 61 44, -- 81: product0
    .mul 81 78, -- 82: product1
    .mul 82 66, -- 83: product3
    .mul 83 80, -- 84: product4
    .sub 84 36 -- 85: polynomial
  ]

def output : ℕ := 85

def consumers : List ℕ :=
  [21, 45, 46, 65, 67, 72, 68, 26, 25, 55, 28, 28, 75, 39, 21, 62, 52, 51, 22, 34, 33, 22, 23, 24, 26, 27, 27, 30, 29, 30, 59, 37, 33, 34, 36, 36, 42, 38, 40, 40, 43, 42, 44, 44, 81, 46, 63, 48, 50, 50, 54, 52, 53, 54, 57, 56, 57, 58, 61, 60, 61, 81, 63, 64, 66, 66, 83, 70, 69, 70, 71, 74, 73, 77, 76, 76, 77, 78, 82, 80, 84, 82, 83, 84, 85]

theorem nodes_length : nodes.length = 86 := by decide +kernel

theorem topological : Topological nodes := by decide +kernel

private theorem consumer_certificate : ∀ i : Fin 85,
    i.val < consumers.getD i.val 0 ∧
    consumers.getD i.val 0 ≤ 85 ∧
    i.val ∈ (nodes.getD (consumers.getD i.val 0) (.literal 0)).dependencies :=
  by decide +kernel

theorem all_live (i : ℕ) (hi : i < nodes.length) : Reaches nodes output i := by
  exact reaches_of_consumer_table nodes consumers 85 nodes_length consumer_certificate i hi

theorem operation_count : operationCount nodes = 65 := by decide +kernel
theorem addition_count : kindCount nodes 3 = 16 := by decide +kernel
theorem subtraction_count : kindCount nodes 4 = 12 := by decide +kernel
theorem multiplication_count : kindCount nodes 5 = 37 := by decide +kernel

theorem live_operation_count : liveOperationCount nodes output = 65 := by
  rw [liveOperationCount_eq nodes output all_live]
  exact operation_count

theorem all_inputs : ∀ i : Fin 14, Node.input i ∈ nodes := by decide +kernel
theorem all_ports : ∀ i : Fin 4, Node.constant i ∈ nodes := by decide +kernel


end DiophantineConsistency.Current14Carrier65DAG

#print axioms DiophantineConsistency.Current14Carrier65DAG.topological
#print axioms DiophantineConsistency.Current14Carrier65DAG.operation_count
#print axioms DiophantineConsistency.Current14Carrier65DAG.addition_count
#print axioms DiophantineConsistency.Current14Carrier65DAG.subtraction_count
#print axioms DiophantineConsistency.Current14Carrier65DAG.multiplication_count
#print axioms DiophantineConsistency.Current14Carrier65DAG.live_operation_count
#print axioms DiophantineConsistency.Current14Carrier65DAG.all_inputs
#print axioms DiophantineConsistency.Current14Carrier65DAG.all_ports
