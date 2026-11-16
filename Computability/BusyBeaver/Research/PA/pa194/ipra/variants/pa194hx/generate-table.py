#!/usr/bin/env python3
"""Regenerate temporary Lean definitions from the pinned dense PA194 table."""
from hashlib import sha256
from pathlib import Path
import sys

if len(sys.argv) != 3:
    raise SystemExit('usage: generate.py REPOSITORY OUTPUT_DIRECTORY')
repo, out = map(Path, sys.argv[1:])
data = (repo / 'Computability/BusyBeaver/Research/PA/docs/pa194_research_2026-11-14/hx194/machine/pa194hx.tm').read_bytes()
if sha256(data).hexdigest() != '3242a613d328d17c979ce3675a154733ea16a1949b4391cb824711b5aa46399a':
    raise SystemExit('unexpected HX machine table hash')

rows = {}
for line in data.decode('ascii').splitlines():
    if not line.strip() or line.lstrip().startswith('#'):
        continue
    fields = line.split()
    if len(fields) != 5:
        raise SystemExit('malformed transition')
    q, b, w, direction, target = fields
    q, b, w, target = map(int, (q, b, w, target))
    if (q, b) in rows or not (0 <= q < 194 and b in (0, 1) and w in (0, 1)
                                and direction in ('L', 'R') and 0 <= target <= 194):
        raise SystemExit('invalid transition')
    rows[q, b] = (w, direction == 'R', target)
if set(rows) != {(q, b) for q in range(194) for b in (0, 1)}:
    raise SystemExit('table does not contain exactly 388 transitions')
seen, todo = {0}, [0]
for q in todo:
    for b in (0, 1):
        target = rows[q, b][2]
        if target < 194 and target not in seen:
            seen.add(target)
            todo.append(target)
if len(seen) != 194:
    raise SystemExit('not every working label is graph-reachable')

def boolrow(q, b):
    w, direction, target = rows[q, b]
    return f"({'true' if w else 'false'}, {'true' if direction else 'false'}, {target})"

def tree(lo, hi, indent):
    p = ' ' * indent
    if hi - lo == 1:
        return f'{p}if read then {boolrow(lo, 1)} else {boolrow(lo, 0)}\n'
    mid = (lo + hi) // 2
    return (f'{p}if q < {mid} then\n' + tree(lo, mid, indent + 2)
            + f'{p}else\n' + tree(mid, hi, indent + 2))

literal = '''import M6.Zip
/-! Generated from the pinned PA194 archive member by generate.py. -/
namespace PA194HX.Literal
def transition (q : Nat) (read : Bool) : Bool × Bool × Nat :=
''' + tree(0, 194, 2) + '''
def machine : M6.Zip.TMN := fun q read =>
  if q < 194 then some (transition q read) else none
def workingLabels : List Nat := List.range 194
def start : Nat := 0
def halt : Nat := 194
theorem working_count : workingLabels.length = 194 := by decide +kernel
theorem row_count : workingLabels.length * 2 = 388 := by decide +kernel
theorem terminal_row (b : Bool) : machine 194 b = none := by
  simp [machine]
end PA194HX.Literal
'''
numeric = 'import Std\nnamespace PA194HXRows\ndef rows : List (Nat × Nat × Nat) := [\n'
numeric += ',\n'.join(f'  ({w}, {int(direction)}, {target})'
                      for q in range(194) for b in (0, 1)
                      for w, direction, target in [rows[q, b]])
numeric += '\n]\nend PA194HXRows\n'
out.mkdir(parents=True, exist_ok=True)
(out / 'PA194HXLiteral.lean').write_text(literal)
(out / 'PA194HXRows.lean').write_text(numeric)
print('Pinned PA194HX: 194 reachable working labels, 388 rows, start 0, terminal 194.')
