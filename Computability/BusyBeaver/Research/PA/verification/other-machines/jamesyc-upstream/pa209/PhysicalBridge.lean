module

public import PhysicalCore
public import M6.Bounds

@[expose] public section

namespace PalomarPA

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

private theorem row_in_range : ∀ q : Fin 216, ∀ b : Bool,
    machineRow q.val b = M6.Literal.machine q.val b := by decide +kernel

private theorem rows_bounded : m6Rows.all (fun r => r.1 < 216) = true := by decide +kernel

private theorem literal_outside (q : Nat) (b : Bool) : M6.Literal.machine (q + 216) b = none := by
  cases b <;> rfl

theorem machineRow_eq (q : Nat) (b : Bool) : machineRow q b = M6.Literal.machine q b := by
  by_cases hq : q < 216
  · exact row_in_range ⟨q, hq⟩ b
  · have h : M6.Literal.machine q b = none := by
      have he : q = q - 216 + 216 := by omega
      rw [he, literal_outside]
    rw [h]
    unfold machineRow
    apply List.findSome?_eq_none_iff.mpr
    intro r hr
    have hb : r.1 < 216 := of_decide_eq_true (List.all_eq_true.mp rows_bounded r hr)
    rcases r with ⟨src, read, write, next, right⟩
    have hn : src ≠ q := by
      change src < 216 at hb
      omega
    simp [hn]

private theorem trimTape_eq (l : List Bool) : trimTape l = M6.Zip.trim l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [trimTape, M6.Zip.trim, ih]

/-- View the independently stated configuration in the proof's tape model. -/
def TapeConfig.toZip (c : TapeConfig) : M6.Zip.Conf := ⟨c.state, c.left, c.right⟩

theorem machineStep_eq (c : TapeConfig) :
    (machineStep c).map TapeConfig.toZip = M6.Zip.step M6.Literal.machine c.toZip := by
  unfold machineStep M6.Zip.step
  simp only [machineRow_eq, TapeConfig.toZip]
  cases h : M6.Literal.machine c.state (c.right.headD false) with
  | none => rfl
  | some row =>
    rcases row with ⟨w, d, q⟩
    cases d <;> simp only [Option.map_some, TapeConfig.toZip, M6.Zip.zc, M6.Zip.zl, trimTape_eq]

theorem machineRun_eq (n : Nat) (c : TapeConfig) :
    (machineRun n c).map TapeConfig.toZip = M6.Zip.run M6.Literal.machine n c.toZip := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [M6.Zip.run, ← machineStep_eq]
    cases h : machineStep c with
    | none => simp [machineRun, h]
    | some c' => simpa [machineRun, h] using ih c'

end PalomarPA
