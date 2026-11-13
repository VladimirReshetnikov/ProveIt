module
public import M6.Source.ExactSource
public import M6.Source.Determinism
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace M6.Source.AXPush

def expected : Nat → Instruction
  | 0 => .dec 1 (some 28) (some 26)
  | 1 => .inc 6 (some 27)
  | 2 => .jump (some 25)
  | 3 => .dec 2 (some 31) (some 29)
  | 4 => .inc 1 (some 30)
  | 5 => .jump (some 28)
  | 6 => .dec 1 (some 35) (some 32)
  | 7 => .inc 7 (some 33)
  | 8 => .inc 6 (some 34)
  | 9 => .jump (some 31)
  | 10 => .dec 6 (some 41) (some 36)
  | 11 => .inc 7 (some 37)
  | 12 => .dec 6 (some 40) (some 38)
  | 13 => .inc 1 (some 39)
  | 14 => .jump (some 37)
  | 15 => .jump (some 31)
  | 16 => .dec 7 (some 44) (some 42)
  | 17 => .inc 2 (some 43)
  | 18 => .jump (some 41)
  | _ => .jump (some 44)

private theorem row_0 : resolveAt exactSites 25 = some (expected 0) := by rfl
private theorem row_1 : resolveAt exactSites 26 = some (expected 1) := by rfl
private theorem row_2 : resolveAt exactSites 27 = some (expected 2) := by rfl
private theorem row_3 : resolveAt exactSites 28 = some (expected 3) := by rfl
private theorem row_4 : resolveAt exactSites 29 = some (expected 4) := by rfl
private theorem row_5 : resolveAt exactSites 30 = some (expected 5) := by rfl
private theorem row_6 : resolveAt exactSites 31 = some (expected 6) := by rfl
private theorem row_7 : resolveAt exactSites 32 = some (expected 7) := by rfl
private theorem row_8 : resolveAt exactSites 33 = some (expected 8) := by rfl
private theorem row_9 : resolveAt exactSites 34 = some (expected 9) := by rfl
private theorem row_10 : resolveAt exactSites 35 = some (expected 10) := by rfl
private theorem row_11 : resolveAt exactSites 36 = some (expected 11) := by rfl
private theorem row_12 : resolveAt exactSites 37 = some (expected 12) := by rfl
private theorem row_13 : resolveAt exactSites 38 = some (expected 13) := by rfl
private theorem row_14 : resolveAt exactSites 39 = some (expected 14) := by rfl
private theorem row_15 : resolveAt exactSites 40 = some (expected 15) := by rfl
private theorem row_16 : resolveAt exactSites 41 = some (expected 16) := by rfl
private theorem row_17 : resolveAt exactSites 42 = some (expected 17) := by rfl
private theorem row_18 : resolveAt exactSites 43 = some (expected 18) := by rfl

theorem literal_binding : ∀ i : Fin 19,
    resolveAt exactSites (25+i.val) = some (expected i.val) := by
  intro i
  rcases i with ⟨i,hi⟩
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row_0
  · exact row_1
  · exact row_2
  · exact row_3
  · exact row_4
  · exact row_5
  · exact row_6
  · exact row_7
  · exact row_8
  · exact row_9
  · exact row_10
  · exact row_11
  · exact row_12
  · exact row_13
  · exact row_14
  · exact row_15
  · exact row_16
  · exact row_17
  · exact row_18

end M6.Source.AXPush

