from pathlib import Path
import argparse,json,hashlib
here=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description='Render exact inherited-label Lean tables from the pinned combined243 machine.')
ap.add_argument('--baseline',type=Path,default=here.parent/'reference/zfc_combined243_old.tm')
ap.add_argument('--output',type=Path,default=here/'Tables242.lean')
args=ap.parse_args()
old=args.baseline
assert hashlib.sha256(old.read_bytes()).hexdigest()=='4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
table={}
for line in old.read_text().splitlines():
    if line and not line.startswith('#'):
        q,b,w,d,t=line.split();table[int(q),int(b)]=(int(w),d,int(t))
new=table.copy()
for b in [0,1]:del new[15,b]
new[11,0]=(0,'R',27);new[27,1]=(1,'R',22)
assert len(table)==486 and len(new)==484
assert max(q for q,b in table)==255 and len({q for q,b in table})==243
assert len({q for q,b in new})==242
def action(a):
    w,d,t=a
    return f'⟨{str(bool(w)).lower()}, {str(d=="R").lower()}, {t}⟩'
def arr(name,t):
    out=[f'def {name} : Array (Option (Action × Action)) := #[']
    for q in range(256):
        s=f'some ({action(t[q,0])}, {action(t[q,1])})'if(q,0)in t else'none'
        out.append(f'  {s}'+(','if q<255 else'')+f' -- {q}')
    out.append(']\n');return '\n'.join(out)
header='''import Lean.Elab.Tactic.Omega

/-!
Exact inherited-label tables and ordinary finite-block simulation for the
242-state branch-borrowing reduction of combined243. All statements use
arbitrary Int-indexed binary tapes, head coordinates, and shared start95.
The theorem is relative to combined243; its source/logic calibration is
supplied separately in the research report. No consistency premise is used.
Original calculus/program: Mira-Cult. Public verification: Jeff Ketchersid.
Compiler: Andrew James Wade. Inherited ProveIt reductions retain attribution.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace BranchBorrow242
structure Action where
  write : Bool
  right : Bool
  next : Nat
  deriving DecidableEq, Repr
'''
args.output.write_text(header+arr('oldRows',table)+arr('newRows',new)+'''
def oldFinite (q : Fin 256) (b : Bool) : Option Action :=
  (oldRows[q.val]'q.isLt).map (fun pair => if b then pair.2 else pair.1)
def newFinite (q : Fin 256) (b : Bool) : Option Action :=
  (newRows[q.val]'q.isLt).map (fun pair => if b then pair.2 else pair.1)
def oldRow (q : Nat) (b : Bool) : Option Action :=
  if h : q < 256 then oldFinite ⟨q, h⟩ b else none
def newRow (q : Nat) (b : Bool) : Option Action :=
  if h : q < 256 then newFinite ⟨q, h⟩ b else none

def incoming (q : Nat) (b : Bool) (a : Action) : Prop :=
  ((a.next = 18 ∨ a.next = 47 ∨ a.next = 65) →
    a.right = true ∧ a.write = false) ∧
  (a.next = 27 → (q = 18 ∨ q = 47 ∨ q = 65) ∧
    b = false ∧ a.right = false) ∧
  (a.next = 15 → q = 11 ∧ b = false)
instance (q : Nat) (b : Bool) (a : Action) : Decidable (incoming q b a) := by
  unfold incoming
  infer_instance

def checkIncoming (q : Fin 256) (b : Bool) : Bool :=
  match oldFinite q b with
  | none => true
  | some a => decide (incoming q.val b a)

theorem incoming_finite : ∀ (q : Fin 256) (b : Bool),
    checkIncoming q b = true := by decide

def patched (q : Nat) (b : Bool) : Option Action :=
  if q = 15 then none
  else if q = 11 ∧ b = false then some ⟨false, true, 27⟩
  else if q = 27 ∧ b = true then some ⟨true, true, 22⟩
  else oldRow q b

theorem patch_finite : ∀ (q : Fin 256) (b : Bool),
    newFinite q b = patched q.val b := by decide

theorem newRow_patch (q : Nat) (b : Bool) : newRow q b = patched q b := by
  by_cases h : q < 256
  · simpa [newRow, h] using patch_finite ⟨q, h⟩ b
  · have h15 : q ≠ 15 := by omega
    have h11 : q ≠ 11 := by omega
    have h27 : q ≠ 27 := by omega
    simp [newRow, patched, oldRow, h, h15, h11, h27]

theorem incoming_all (q : Nat) (b : Bool) (a : Action)
    (hrow : oldRow q b = some a) : incoming q b a := by
  by_cases hq : q < 256
  · have hh := incoming_finite ⟨q, hq⟩ b
    have hr : oldFinite ⟨q, hq⟩ b = some a := by simpa [oldRow, hq] using hrow
    simp only [checkIncoming, hr] at hh
    exact of_decide_eq_true hh
  · simp [oldRow, hq] at hrow

def workingCount (rows : Array (Option (Action × Action))) : Nat :=
  rows.foldl (fun n a => if a.isSome then n + 1 else n) 0

theorem old_size : oldRows.size = 256 := by decide
theorem new_size : newRows.size = 256 := by decide
theorem old_working_count : workingCount oldRows = 243 := by decide
theorem new_working_count : workingCount newRows = 242 := by decide

theorem old_halt (b : Bool) : oldRow 254 b = none := by cases b <;> rfl
theorem new_halt (b : Bool) : newRow 254 b = none := by cases b <;> rfl

end BranchBorrow242
''')
print('generated exact old243 and new242 arrays')
