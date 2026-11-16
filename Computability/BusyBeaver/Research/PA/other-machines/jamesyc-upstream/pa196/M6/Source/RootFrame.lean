module
public import M6.Source.PhysicalRegisters

/-! Canonical full physical root frames for source paths. The offset accounts
for header overflow and positive decrement; the box retains the entire file. -/
@[expose] public section

namespace M6.Source
open M6.Runtime

def rootFrame (path : Path) (extra : Nat := 0) (effect : Eff := .none) : SConf :=
  (84, false, [.bit true],
    path.map Seg.bit ++ [.run false 1 (38 + extra - path.length),
      .bit true, .box (.plain effect)])

def effectFile : Eff → List Nat → List Nat
  | .none, vs => vs
  | .inc r, vs => Runtime.incr r vs ++ [1]
  | .dec r, vs => Runtime.decr r vs

private theorem flat_bits (path : Path) (n : Nat) (vs : List Nat) :
    flat n vs (path.map Seg.bit) = path := by
  induction path with
  | nil => rfl
  | cons b path ih => simpa [flat,segList] using congrArg (b :: ·) ih

private theorem flat_append (a b : List Seg) (n : Nat) (vs : List Nat) :
    flat n vs (a ++ b) = flat n vs a ++ flat n vs b := by
  simp [flat]

/-- An affine padding shift and the exact runtime file effect are absorbed by
changing the frame parameters, not by weakening its full tape assertion. -/
theorem rootFrame_effect (path : Path) (hp : path.length ≤ 38)
    (extra n : Nat) (vs : List Nat) (effect : Eff) :
    conc n vs (rootFrame path extra effect) =
      conc (n + extra) (effectFile effect vs) (rootFrame path) := by
  have hlen : n + (38 + extra - path.length) = n + extra + (38 - path.length) := by omega
  simp only [rootFrame, conc, flat_append, flat_bits]
  cases effect <;> simp [flat, segList, boxList, effectFile, hlen]

/-- Canonical initial path headers preserve the exact prefix and all file cells. -/
theorem rootFrame_concrete (path : Path) (n : Nat) (vs : List Nat) :
    conc n vs (rootFrame path) =
      M6.Zip.zc 84 [true]
        (path ++ List.replicate (n + (38 - path.length)) false ++
          true :: sepsR vs) := by
  simp only [rootFrame, conc, flat_append, flat_bits]
  simp [flat, segList, boxList, List.append_assoc]

/-- Canonical zero extension identifies a control prefix with its leftmost
leaf without changing any physical tape cell or the complete register file. -/
theorem rootFrame_zero_extension (path : Path) (k n : Nat) (vs : List Nat)
    (hp : path.length + k ≤ 38) :
    conc n vs (rootFrame (path ++ List.replicate k false)) =
      conc n vs (rootFrame path) := by
  rw [rootFrame_concrete, rootFrame_concrete]
  have he : k + (n + (38 - (path.length + k))) = n + (38 - path.length) := by omega
  simp only [List.length_append, List.length_replicate, List.append_assoc]
  rw [← List.append_assoc (List.replicate k false), List.replicate_append_replicate, he]

#print axioms rootFrame_zero_extension
#print axioms rootFrame_effect
#print axioms rootFrame_concrete
end M6.Source

