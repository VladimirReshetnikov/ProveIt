#!/usr/bin/env python3
"""Generate untrusted dense-PA194 startup checkpoints and Lean checks."""
import argparse
import sys
from pathlib import Path
from hashlib import sha256

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('repository', type=Path)
parser.add_argument('output', type=Path)
args = parser.parse_args()
root = args.repository.resolve()
out = args.output.resolve()
out.mkdir(parents=True, exist_ok=True)
raw=(root / 'Computability/BusyBeaver/Research/PA/docs/pa194_research_2026-11-14/hx194/machine/pa194hx.tm').read_bytes()
assert sha256(raw).hexdigest()=='3242a613d328d17c979ce3675a154733ea16a1949b4391cb824711b5aa46399a'

rows={}
for line in raw.decode().splitlines():
 q,b,w,d,t=line.split(); assert d in ('R','L'); key=int(q),int(b); assert key not in rows
 rows[key]=(int(w),d,int(t))
assert len(rows)==388
def trim(xs):
 while xs and not xs[-1]: xs.pop()
 return xs
def step(c):
 q,l,r=c; w,d,q=rows[q,r[0] if r else 0]
 if d=='R': return q,trim([w]+l),trim(r[1:])
 return q,trim(l[1:]),trim([(l[0] if l else 0),w]+r[1:])
states=[(0,[],[])]; c=states[0]
for block in range(439):
 for _ in range(70 if block==438 else 128): c=step(c)
 states.append(c)
assert c[0]==24 and c[1]==[1] and len(c[2])==147
bits=lambda x:'['+', '.join('true' if b else 'false' for b in x)+']'
entries=[f'def c{i:04d} : Conf := ⟨{q}, {bits(l)}, {bits(r)}⟩' for i,(q,l,r) in enumerate(states)]
head='''import PA194HXLiteral
import PA194StartupData
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194HXDenseStartupData
open M6.Zip
'''
end='''
/-- The final dense tape is exactly the parent startup seed tape. -/
theorem seed_match : c0439 = ⟨24, PA194StartupData.seedFrame.l, PA194StartupData.seedFrame.r⟩ := by decide +kernel
#print axioms seed_match
end PA194HXDenseStartupData
'''
(out/'PA194HXDenseStartupData.lean').write_text(head+'\n'.join(entries)+end)
batches=[]
for first in range(0,439,10):
 last=min(first+10,439); mod=f'PA194HXDenseStartupBlock{first:04d}_{last:04d}'
 proofs=[]
 for i in range(first,last):
  n=70 if i==438 else 128
  proofs.append(f'''theorem run{i:04d} : run PA194HX.Literal.machine {n} c{i:04d} = some c{i+1:04d} := by
  exact PA196.FastRun.checked (by decide +kernel) (by decide +kernel)''')
 content=f'''import PA194HXDenseStartupData
import PA196.FastRun
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {mod}
open M6.Zip PA194HXDenseStartupData
'''+ '\n\n'.join(proofs)+f'\n#print axioms run{last-1:04d}\nend {mod}\n'
 (out/f'{mod}.lean').write_text(content); batches.append(mod)
imports='\n'.join('import '+m for m in batches); openings='\n'.join('open '+m for m in batches)
proof=['  have step0000 := run0000']
proof += [f'  have step{i:04d} := compose step{i-1:04d} run{i:04d}' for i in range(1,439)]
proof.append('  simpa only [PA194HXDenseStartupData.c0000, seed_match] using step0438')
content=f'''{imports}
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194HXDenseStartupComplete
open M6.Zip PA194HXDenseStartupData
{openings}
private theorem compose {{M : TMN}} {{a b c : Conf}} {{n m : Nat}}
    (ha : run M n a = some b) (hb : run M m b = some c) :
    run M (n+m) a = some c := by rw [run_add, ha]; exact hb
/-- The literal dense PA194 run reaches the parent seed tape after 56134 steps. -/
theorem startup_exact : run PA194HX.Literal.machine 56134 ⟨0, [], []⟩ =
    some ⟨24, PA194StartupData.seedFrame.l, PA194StartupData.seedFrame.r⟩ := by
'''+ '\n'.join(proof)+'''\n#print axioms startup_exact
end PA194HXDenseStartupComplete
'''
(out/'PA194HXDenseStartupComplete.lean').write_text(content)
print(f'Generated {len(states)} states, {len(batches)} modules')
