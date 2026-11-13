#!/usr/bin/env python3
"""Source/slot mapping check for the uncompiled five-norm assembly."""
import hashlib,json,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/nine-sharing-norm38-five-norms-draft';batched=D/'research/nine-sharing-norm38-slots-batched-retry01';out=Path('/tmp/nine-sharing-norm38-slots-batched-retry01-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
src=q/'Norm38FiveNorms.lean';assert sha(src)=='659df3272bc175cad9a3a461d01c52cc3d10a6375f16c351a0e6093a28f383d2';text=src.read_text();assert 'UNCOMPILED draft' in text and 'sorry' not in text and 'admit' not in text
state=batched/'attempt01/state.json';assert sha(state)=='5e2b9bc0792962fe16bb2015ee035a06c4e806acfeb85eafc2d942029eef8edc';records={r['module']:r for r in json.loads(state.read_text())['rows']}
expect={11:(44,'1'),16:(61,'1'),17:(66,'1'),27:(78,'1'),28:(80,'pairValue ι (v 36)')};groups=set()
for i,(target,rhs) in expect.items():
 group=f'Norm38Slots{i//3:02d}';groups.add(group);s=(batched/'src/DiophantineConsistency'/(group+'.lean')).read_text();stmt=re.search(r'^theorem slot'+f'{i:02d}'+r'\b.*? := by',s,re.S|re.M).group()
 assert f'(residualAt p {i}).evalRing' in stmt and f'pairValue ι (v {target}) - {rhs}' in stmt
 assert f'have h{i:02d} := each_slot_zero p w hz {i}' in text and f'rw [slot{i:02d} p ports w hp] at h{i:02d}' in text
for n in groups:
 r=records[n];assert r['deps']['exit']==r['compile']['exit']==0 and r['compile']['stop_reason'] is None
 assert sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256'] and sha(batched/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']
 assert 'import DiophantineConsistency.'+n in text
assert 'import DiophantineConsistency.Norm38EachSlot' in text
assert 'sub_eq_zero.mp h16, sub_eq_zero.mp h11, sub_eq_zero.mp h27,' in text and 'sub_eq_zero.mp h17, sub_eq_zero.mp h28' in text
assign=(D/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text()
for x in ['(v 61) = 1','(v 44) = 1','(v 78) = 1','(v 66) = 1','(v 80) = pairValue embed (v 36)']:assert x in assign
print(json.dumps({'status':'PASS_FIVE_NORM_SOURCE_MAPPING_ONLY','source_sha256':sha(src),'batched_state_sha256':sha(state),'slot_to_node':{str(i):target for i,(target,_) in expect.items()},'compiled_groups':sorted(groups),'scope':'Source and previously compiled group object point checks; each_slot and this assembly not checked here.'},indent=2,sort_keys=True))
