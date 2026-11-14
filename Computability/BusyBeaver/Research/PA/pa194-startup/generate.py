#!/usr/bin/env python3
"""Generate untrusted PA194 startup checkpoints and Lean kernel checks."""
import argparse
import hashlib
from pathlib import Path
from zipfile import ZipFile

root = Path(__file__).resolve().parents[5]
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--out', type=Path, required=True)
p.add_argument('--start-block', type=int, default=0)
p.add_argument('--stop-block', type=int, default=455)
p.add_argument('--batch-size', type=int, default=10)
a = p.parse_args()
if not (0 <= a.start_block < a.stop_block <= 455 and a.batch_size > 0):
    raise SystemExit('invalid block range or batch size')
with ZipFile(root / 'docs/incoming/pa194_conpa_2026-11-13.zip') as z:
    raw = z.read('pa194_conpa/construction/tables/unfolded201.native.tm')
if hashlib.sha256(raw).hexdigest() != 'b25933d14de19f72709bdecf7a67a4e21c150f525cf61ec76c074ac577d6cc87':
    raise SystemExit('unfolded parent table hash mismatch')
rows = {}
for line in raw.decode().splitlines():
    q, b, w, direction, target = line.split()
    key = (int(q), int(b))
    if key in rows or direction not in ('L', 'R'):
        raise SystemExit('invalid or duplicated table row')
    rows[key] = (int(w), direction, int(target))
if len(rows) != 402:
    raise SystemExit('unexpected table size')

def trim(bits):
    while bits and bits[-1] == 0:
        bits.pop()
    return bits

def step(c):
    q, left, right = c
    bit = right[0] if right else 0
    write, direction, q = rows[(q, bit)]
    if direction == 'R':
        return q, trim([write] + left), trim(right[1:])
    new_head = left[0] if left else 0
    return q, trim(left[1:]), trim([new_head, write] + right[1:])

states = [(74, [], [])]
c = states[0]
for block in range(455):
    length = 42 if block == 454 else 128
    for _ in range(length):
        c = step(c)
    states.append(c)
if states[-1][0] != 84 or states[-1][1] != [1]:
    raise SystemExit('unexpected startup endpoint')

def bits(value):
    return '[' + ', '.join('true' if b else 'false' for b in value) + ']'

a.out.mkdir(parents=True, exist_ok=True)
entries = [f'def c{i:04d} : Conf := ⟨{q}, {bits(left)}, {bits(right)}⟩'
           for i, (q, left, right) in enumerate(states)]
data = '''import PA194PrimitiveSimulation
import PA194SourceProgram

/-! Checkpoint values are untrusted inputs to separately kernel-checked runs. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194StartupData
open M6.Zip M6.Source PA194PrimitiveSimulation PA194SourceProgram

def blank : Conf := ⟨74, [], []⟩
def seedFile : List Nat := [0,0,0,0,0,0,2,0,0] ++ List.replicate 26 1
def seedFrame : Conf := frame (path 25) 0 seedFile
''' + '\n'.join(entries) + '''

theorem first_eq : c0000 = blank := rfl

theorem last_eq : c0455 = seedFrame := by decide +kernel

#print axioms last_eq
end PA194StartupData
'''
(a.out / 'PA194StartupData.lean').write_text(data)
batches = []
for first in range(a.start_block, a.stop_block, a.batch_size):
    last = min(first + a.batch_size, a.stop_block)
    module = f'PA194StartupBlock{first:04d}_{last:04d}'
    proofs = []
    for i in range(first, last):
        length = 42 if i == 454 else 128
        proofs.append(f'''theorem run{i:04d} : run machine {length} c{i:04d} = some c{i+1:04d} := by
  exact PA196.FastRun.checked (by decide +kernel) (by decide +kernel)''')
    content = f'''import PA194StartupData
import PA196.FastRun
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {module}
open M6.Zip PA194RuntimeEngine PA194StartupData

''' + '\n\n'.join(proofs) + f'\n\n#print axioms run{last-1:04d}\nend {module}\n'
    (a.out / f'{module}.lean').write_text(content)
    batches.append((module, first, last))
if a.start_block == 0 and a.stop_block == 455:
    imports = '\n'.join('import ' + x[0] for x in batches)
    openings = '\n'.join('open ' + x[0] for x in batches)
    proof = ['  have step0000 := run0000']
    for i in range(1, 455):
        proof.append(f'  have step{i:04d} := compose step{i-1:04d} run{i:04d}')
    proof.append('  simpa only [first_eq, last_eq] using step0454')
    content = f'''{imports}
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194StartupComplete
open M6.Zip PA194RuntimeEngine PA194StartupData
{openings}

private theorem compose {{M : TMN}} {{a b c : Conf}} {{n m : Nat}}
    (ha : run M n a = some b) (hb : run M m b = some c) :
    run M (n+m) a = some c := by rw [run_add, ha]; exact hb

/-- The entire exact PA194 parent blank startup reaches the source seed frame. -/
theorem startup_exact : run machine 58154 blank = some seedFrame := by
''' + '\n'.join(proof) + '''

theorem startup_reach : Reach machine blank seedFrame := ⟨58154, startup_exact⟩
#print axioms startup_exact
#print axioms startup_reach
end PA194StartupComplete
'''
    (a.out / 'PA194StartupComplete.lean').write_text(content)
print(f'Generated {len(batches)} checkpoint batches, blocks {a.start_block}..{a.stop_block-1}; 58154 total steps')
