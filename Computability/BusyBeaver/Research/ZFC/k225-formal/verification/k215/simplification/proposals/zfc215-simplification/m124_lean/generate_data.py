#!/usr/bin/env python3
"""Reconstruct the checked Lean table facts from the exact K215 native table.

No theorem is assumed about the generator: the emitted facts use kernel
reduction, and the input bytes and complete emitted text are checked here.
"""
from pathlib import Path
import argparse
import hashlib

BASE_SHA = '9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'

def render(path):
    raw = Path(path).read_bytes()
    if hashlib.sha256(raw).hexdigest() != BASE_SHA:
        raise ValueError('This certificate is pinned to the accepted K215 native table')
    rows = {}
    for line in raw.decode().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, n = line.split()
        key = (int(q), int(b))
        if key in rows:
            raise ValueError('duplicate table row')
        rows[key] = (w == '1', d == 'R', int(n))
    labels = sorted({q for q, b in rows})
    assert len(labels) == 215 and len(rows) == 430
    assert all((q, b) in rows for q in labels for b in (0, 1))
    assert 0 in labels and 254 not in labels and max(labels) == 302
    assert all(a[2] in labels or a[2] == 254 for a in rows.values())
    def act(a):
        return '⟨' + str(a[0]).lower() + ', ' + str(a[1]).lower() + ', ' + str(a[2]) + '⟩'
    out = '''import Std

namespace Marker124

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

structure Act where
  write : Bool
  right : Bool
  dest : Nat
  deriving DecidableEq, BEq, Repr

def oldTable : Nat → Bool → Act
'''
    for q in labels:
        for b in (0, 1):
            out += f'  | {q}, {str(bool(b)).lower()} => {act(rows[q,b])}\n'
    out += '''  | _, _ => ⟨false, true, 254⟩

def newTable (q : Nat) (b : Bool) : Act :=
  match q, b with
  | 110, false => ⟨false, true, 124⟩
  | 124, false => ⟨false, false, 127⟩
  | 127, false => ⟨false, true, 8⟩
  | 127, true => ⟨true, true, 59⟩
  | _, _ => oldTable q b

def phi (q : Nat) : Nat := if q = 127 then 124 else q

def mapAct (a : Act) : Act := ⟨a.write, a.right, phi a.dest⟩

theorem old_bounds : ∀ (q : Fin 303) (b : Bool), (oldTable q.val b).dest < 303 := by decide +kernel

theorem incoming124 : ∀ (q : Fin 303) (b : Bool),
    (oldTable q.val b).dest = 124 →
    (oldTable q.val b).write = true ∧ (oldTable q.val b).right = true := by decide +kernel

theorem incoming127 : ∀ (q : Fin 303) (b : Bool),
    (oldTable q.val b).dest = 127 →
    (oldTable q.val b).write = false ∧ (oldTable q.val b).right = true := by decide +kernel

theorem regular_rows : ∀ (q : Fin 303) (b : Bool),
    q.val ≠ 124 → q.val ≠ 127 →
    newTable (phi q.val) b = mapAct (oldTable q.val b) := by decide +kernel

'''
    out += 'def workingLabels : List Nat := [' + ', '.join(map(str, labels)) + ']\n\n'
    out += '''theorem state_count : workingLabels.length = 215 := by decide +kernel
theorem distinct_labels : workingLabels.Nodup := by decide +kernel
theorem start_is_working : 0 ∈ workingLabels := by decide +kernel
theorem halt_is_separate : 254 ∉ workingLabels := by decide +kernel

theorem old_label_closure : ∀ (q : Fin 303) (b : Bool),
    q.val ∈ workingLabels → (oldTable q.val b).dest ∈ workingLabels ∨
      (oldTable q.val b).dest = 254 := by decide +kernel

theorem new_label_closure : ∀ (q : Fin 303) (b : Bool),
    q.val ∈ workingLabels → (newTable q.val b).dest ∈ workingLabels ∨
      (newTable q.val b).dest = 254 := by decide +kernel

end Marker124
'''
    return out

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('baseline')
    ap.add_argument('--output', default='Marker124Data.lean')
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    output = render(args.baseline)
    if args.check:
        assert Path(args.output).read_text() == output, 'generated Lean data differs'
        print('Exact generated Lean source matches the pinned table.')
    else:
        Path(args.output).write_text(output)

if __name__ == '__main__':
    main()
