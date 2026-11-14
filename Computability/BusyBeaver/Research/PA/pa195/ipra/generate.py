#!/usr/bin/env python3
"""Regenerate temporary Lean definitions from the pinned dense PA195 table."""
from hashlib import sha256
from pathlib import Path
from zipfile import ZipFile
import sys

if len(sys.argv) != 3:
    raise SystemExit('usage: generate.py REPOSITORY OUTPUT_DIRECTORY')
repo, out = map(Path, sys.argv[1:])
archive_path = repo / 'docs/incoming/pa195_conpa_2026-11-13.zip'
member = 'pa195_conpa/pa195/pa195.tm'
if sha256(archive_path.read_bytes()).hexdigest() != '0001250c43a40920027403d748bcca36e4519a5a45e94dec98cafad4f3c8ff9f':
    raise SystemExit('unexpected archive hash')
with ZipFile(archive_path) as archive:
    data = archive.read(member)
if sha256(data).hexdigest() != '5c6afd87f7c4f24d9ad8e9e302cc21df14b6f2e3715d03322a75463a431d8455':
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
    if (q, b) in rows or not (0 <= q < 195 and b in (0, 1) and w in (0, 1)
                                and direction in ('L', 'R') and 0 <= target <= 195):
        raise SystemExit('invalid transition')
    rows[q, b] = (w, direction == 'R', target)
if set(rows) != {(q, b) for q in range(195) for b in (0, 1)}:
    raise SystemExit('table does not contain exactly 390 transitions')
seen, todo = {0}, [0]
for q in todo:
    for b in (0, 1):
        target = rows[q, b][2]
        if target < 195 and target not in seen:
            seen.add(target)
            todo.append(target)
if len(seen) != 195:
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
/-! Generated from the pinned PA195 archive member by generate.py. -/
namespace PA195.Literal
def transition (q : Nat) (read : Bool) : Bool × Bool × Nat :=
''' + tree(0, 195, 2) + '''
def machine : M6.Zip.TMN := fun q read =>
  if q < 195 then some (transition q read) else none
def workingLabels : List Nat := List.range 195
def start : Nat := 0
def halt : Nat := 195
theorem working_count : workingLabels.length = 195 := by decide +kernel
theorem row_count : workingLabels.length * 2 = 390 := by decide +kernel
theorem terminal_row (b : Bool) : machine 195 b = none := by
  simp [machine]
end PA195.Literal
'''
numeric = 'import Std\nnamespace PA195Rows\ndef rows : List (Nat × Nat × Nat) := [\n'
numeric += ',\n'.join(f'  ({w}, {int(direction)}, {target})'
                      for q in range(195) for b in (0, 1)
                      for w, direction, target in [rows[q, b]])
numeric += '\n]\nend PA195Rows\n'
out.mkdir(parents=True, exist_ok=True)
(out / 'PA195Literal.lean').write_text(literal)
(out / 'PA195Rows.lean').write_text(numeric)
print('Pinned PA195: 195 reachable working labels, 390 rows, start 0, terminal 195.')
