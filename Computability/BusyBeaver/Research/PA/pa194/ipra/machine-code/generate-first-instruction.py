#!/usr/bin/env python3
"""Generate untrusted literal PA194 first-source-instruction checkpoints."""
import argparse
import hashlib
from pathlib import Path
import re

parser = argparse.ArgumentParser()
parser.add_argument('--repo', type=Path, required=True)
parser.add_argument('--startup-data', type=Path, required=True)
parser.add_argument('--out', type=Path, required=True)
args = parser.parse_args()
table = args.repo / 'Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13/construction/tables/pa194.tm'
raw = table.read_bytes()
if hashlib.sha256(raw).hexdigest() != '4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f':
    raise SystemExit('pinned dense table hash mismatch')
startup = args.startup_data.read_bytes()
if hashlib.sha256(startup).hexdigest() != '7cd4f1ae6f6f5d0ee476840d6e7aa447500a3ec4e2293f6830e672cca735bbd7':
    raise SystemExit('pinned parent startup checkpoint source hash mismatch')
match = re.search(r'^def c0455 : Conf := ⟨84, \[true\], \[(.*?)\]⟩$', startup.decode(), re.M)
if match is None:
    raise SystemExit('missing checked startup seed checkpoint')
bits = match.group(1).split(', ')
if any(b not in ('true', 'false') for b in bits):
    raise SystemExit('invalid tape bit')
rows = {}
for line in raw.decode().splitlines():
    q,b,w,d,target = line.split()
    key = (int(q),int(b))
    if key in rows or d not in ('L','R'):
        raise SystemExit('invalid machine table')
    rows[key] = (int(w),d,int(target))
if len(rows) != 388:
    raise SystemExit('unexpected table row count')
q, left = 24, 1
right = sum((b == 'true') << i for i,b in enumerate(bits))
states = []
for step in range(463):
    if step in (0,128,256,384,462):
        states.append((q,left,right))
    if step == 462:
        break
    w,d,target = rows[q,right & 1]
    if d == 'R':
        left, right = (left << 1) | w, right >> 1
    else:
        left, right = left >> 1, ((right >> 1) << 2) | (w << 1) | (left & 1)
    q = target
if len(states) != 5:
    raise SystemExit('unexpected checkpoint count')
def bitlist(value):
    return '[' + ', '.join('true' if (value >> i) & 1 else 'false'
                            for i in range(value.bit_length())) + ']'
args.out.mkdir(parents=True, exist_ok=True)
parts = [f'def d{i:04d} : Conf := ⟨{q}, {bitlist(left)}, {bitlist(right)}⟩'
         for i,(q,left,right) in enumerate(states)]
head = """import PA194DenseStartupData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194FirstInstructionData
open M6.Zip
"""
tail = "'s exact source seed frame in the literal dense numbering. -/\ndef target : Conf := ⟨24,\n  (PA194PrimitiveSimulation.frame (PA194SourceProgram.path 27) 0 PA194StartupData.seedFile).l,\n  (PA194PrimitiveSimulation.frame (PA194SourceProgram.path 27) 0 PA194StartupData.seedFile).r⟩\ntheorem first_eq : d0000 = PA194DenseStartupData.c0455 := by decide +kernel\ntheorem target_eq : d0004 = target := by decide +kernel\n#print axioms first_eq\n#print axioms target_eq\nend PA194FirstInstructionData\n"
(args.out / 'PA194FirstInstructionData.lean').write_text(head + '\n'.join(parts) + '\n/-- Site 27' + tail)
for i, length in enumerate((128,128,128,78)):
    name = f'PA194FirstInstructionBlock{i}'
    source = f"""import PA194FirstInstructionData
import PA196.FastRun
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {name}
open M6.Zip PA194FirstInstructionData
theorem checked : run PA194.Literal.machine {length} d{i:04d} = some d{i+1:04d} := by
  exact PA196.FastRun.checked (by decide +kernel) (by decide +kernel)
#print axioms checked
end {name}
"""
    (args.out / (name + '.lean')).write_text(source)
(args.out / 'PA194FirstInstructionComplete.lean').write_text("import PA194FirstInstructionBlock0\nimport PA194FirstInstructionBlock1\nimport PA194FirstInstructionBlock2\nimport PA194FirstInstructionBlock3\nimport PA194DenseStartupComplete\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace PA194FirstInstructionComplete\nopen M6.Zip PA194FirstInstructionData\nprivate theorem compose {M : TMN} {a b c : Conf} {n m : Nat}\n    (ha : run M n a = some b) (hb : run M m b = some c) :\n    run M (n+m) a = some c := by rw [run_add, ha]; exact hb\n\n/-- The exact first source instruction's zero branch on the literal seed frame. -/\ntheorem firstInstruction :\n    run PA194.Literal.machine 462\n      ⟨24,PA194StartupData.seedFrame.l,PA194StartupData.seedFrame.r⟩ = some target := by\n  have h1 := compose PA194FirstInstructionBlock0.checked PA194FirstInstructionBlock1.checked\n  have h2 := compose h1 PA194FirstInstructionBlock2.checked\n  have h3 := compose h2 PA194FirstInstructionBlock3.checked\n  simpa only [first_eq, PA194DenseStartupData.seed_match, target_eq] using h3\n\n/-- Exact literal blank-to-site-27 seed-file configuration. -/\ntheorem blankToSite27 :\n    run PA194.Literal.machine 58616 ⟨0,[],[]⟩ = some target := by\n  have h := compose PA194DenseStartupComplete.startup_exact firstInstruction\n  exact h\n#print axioms firstInstruction\n#print axioms blankToSite27\nend PA194FirstInstructionComplete\n")
print('Generated 5 untrusted checkpoints and 4 blocks for a 462-step candidate trace.')
