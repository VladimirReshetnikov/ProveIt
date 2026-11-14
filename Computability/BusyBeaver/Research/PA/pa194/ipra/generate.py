#!/usr/bin/env python3
"""Regenerate temporary Lean definitions from the pinned dense PA194 table."""
from hashlib import sha256
from pathlib import Path
from zipfile import ZipFile
import sys

if len(sys.argv) != 3:
    raise SystemExit('usage: generate.py REPOSITORY OUTPUT_DIRECTORY')
repo, out = map(Path, sys.argv[1:])
archive_path = repo / 'docs/incoming/pa194_conpa_2026-11-13.zip'
member = 'pa194_conpa/construction/tables/pa194.tm'
if sha256(archive_path.read_bytes()).hexdigest() != 'fda113b720aaa1615c26994a9ca6ccb3b34d3928deee3755b306678a41e21935':
    raise SystemExit('unexpected archive hash')
with ZipFile(archive_path) as archive:
    data = archive.read(member)
if sha256(data).hexdigest() != '4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f':
    raise SystemExit('unexpected machine table hash')

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
namespace PA194.Literal
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
end PA194.Literal
'''
numeric = 'import Std\nnamespace PA194Rows\ndef rows : List (Nat × Nat × Nat) := [\n'
numeric += ',\n'.join(f'  ({w}, {int(direction)}, {target})'
                      for q in range(194) for b in (0, 1)
                      for w, direction, target in [rows[q, b]])
numeric += '\n]\nend PA194Rows\n'
out.mkdir(parents=True, exist_ok=True)
(out / 'PA194Literal.lean').write_text(literal)
(out / 'PA194Rows.lean').write_text(numeric)
print('Pinned PA194: 194 reachable working labels, 388 rows, start 0, terminal 194.')
