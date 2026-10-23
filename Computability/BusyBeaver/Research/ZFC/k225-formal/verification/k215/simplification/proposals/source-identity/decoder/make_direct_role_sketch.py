#!/usr/bin/env python3
"""Emit an uncompiled direct-program certificate pilot from audited data."""
from pathlib import Path
import runpy

ROOT = Path(__file__).resolve().parent
parse = runpy.run_path(str(ROOT / 'audit_direct_program.py'))['parse']
_, nodes, _, _, _, _, roles = parse()
renaming = {old: new for new, old in enumerate(i for i, n in enumerate(nodes) if n[0] == 'fork')}

head = '''import BusyBeaver.ZFC.K215Decoder
import BusyBeaver.ZFC.KSource215Program

/-!
UNCOMPILED PILOT, pinned to cbf94cb552a3b49509e0eee80e7455d4eb5974c6.
This file proposes a finite checker and retargeted role data only.
No direct-program semantic soundness theorem is supplied here.
The old K215Decoder import is a migration convenience for its formal table and
281 checked blocks. Production must split those into an independent block-data
module before this pilot removes anything from the dependency closure.
-/
namespace SetTheory.BusyBeaver.ZFC.DirectProgramCertificateDraft
open FramedWindow DecoderCertificate

inductive Link where
  | internal (target block : Nat)
  | primitive (action : Action)
  deriving DecidableEq, Repr

structure Role where
  node : Nat
  state : Nat
  suffix : List Bool
  zero : Link
  one : Link
  deriving DecidableEq, Repr

def branch (p : RegisterPath.Program) (n : Nat) (bit : Bool) : RegisterPath.Edge :=
  if bit then (p.nodes n).2 else (p.nodes n).1

def edgeCheck (M : Table) (p : RegisterPath.Program) (rs : Array Role)
    (bs : Array Block) (r : Role) (bit : Bool) : Bool :=
  match (if bit then r.one else r.zero), branch p r.node bit with
  | .primitive action, .node _ => false
  | .primitive action, _ => decide (M r.state bit = some action)
  | .internal k j, .node child =>
    match rs[k]?, bs[j]? with
    | some s, some b =>
      let w := r.suffix ++ [bit]
      decide (child < r.node ∧ s.node = child ∧ s.suffix = tail2 w ∧
        b.entry = r.state ∧ b.exit = s.state ∧ b.word.length ≤ w.length ∧
        b.word = w.drop (w.length - b.word.length))
    | _, _ => false
  | .internal _ _, _ => false

def roleCheck (M : Table) (p : RegisterPath.Program) (rs : Array Role)
    (bs : Array Block) (r : Role) : Bool :=
  decide (r.node < p.nnodes ∧ 0 < r.suffix.length ∧ r.suffix.length ≤ 2) &&
    edgeCheck M p rs bs r false && edgeCheck M p rs bs r true

def structuralCheck (M : Table) (p : RegisterPath.Program)
    (rs : Array Role) (bs : Array Block) : Bool :=
  match rs[0]? with
  | none => false
  | some r => decide (r.node = p.root ∧ r.state = 84 ∧ r.suffix = [true]) &&
      rs.toList.all (roleCheck M p rs bs)

-- The role order, physical states, suffixes, and internal block references
-- are unchanged. Only source labels are retargeted; primitive leaf IDs vanish.
def roles : Array Role := #[
'''


def b(x):
    return 'true' if x else 'false'


def link(e):
    if e[0] == 'internal':
        return f'(.internal {e[1]} {e[2]})'
    w, direction, q = e[2]
    direction = '1' if direction == 1 else '(-1)'
    return f'(.primitive ⟨{b(w)}, {direction}, {q}⟩)'


rows = []
for n, q, suffix, zero, one in roles:
    word = ', '.join(b(x) for x in suffix)
    rows.append(f'  ⟨{renaming[n]}, {q}, [{word}], {link(zero)}, {link(one)}⟩')

tail = '''
]

-- Proposed proof-assistant checks. These declarations have NOT been compiled.
theorem counts : roles.size = 234 ∧ K215Decoder.blocks.size = 281 := by
  decide +kernel

theorem structure_checked :
    structuralCheck K215Decoder.formal KSource215.p215 roles K215Decoder.blocks = true := by
  rw [← K215Decoder.fast_eq]
  decide +kernel

#print axioms counts
#print axioms structure_checked
end SetTheory.BusyBeaver.ZFC.DirectProgramCertificateDraft
'''
(ROOT / 'DirectProgramCertificateDraft.lean').write_text(head + ',\n'.join(rows) + tail)
print('Emitted uncompiled DirectProgramCertificateDraft.lean; no compiler invoked.')
