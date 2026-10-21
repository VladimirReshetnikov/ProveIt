#!/usr/bin/env python3
"""Own inert literal/read-record comparison; imports no delivered executable."""
from pathlib import Path
from collections import deque
import gzip, hashlib, json, re
P=Path('/tmp/zfc-intake198/extracted/K215_Composed_Selectors_2026-10-20/K215_Composed_Selectors_2026-10-20')
A=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/candidate-k215')
O=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def j(p):return json.loads(gzip.decompress(p.read_bytes()) if p.suffix=='.gz' else p.read_bytes())
def table(p):
 t={}
 for l in p.read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,d,z=l.split();q,b,w,z=map(int,(q,b,w,z));assert(q,b)not in t and b in(0,1)and w in(0,1)and d in('L','R');t[q,b]=(w,d,z)
 return t
old=table(A/'k215.native.tm');new=table(P/'machine/k215.native.tm')
mapping={0:0,254:254};inverse={0:0,254:254};todo=deque([0]);seen=set()
while todo:
 q=todo.popleft()
 if q in seen or q==254:continue
 seen.add(q)
 for b in(0,1):
  w,d,z=old[q,b];v,e,t=new[mapping[q],b];assert(w,d)==(v,e)
  assert mapping.get(z,t)==t and inverse.get(t,z)==z
  mapping[z]=t;inverse[t]=z;todo.append(z)
assert len(seen)==215 and len(mapping)==216 and mapping[84]==84
assert {(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in old.items()}==new
assert (P/'source/sites215.json').read_bytes()==(A/'sites215.json').read_bytes()
native_map={int(k):v for k,v in j(P/'machine/canonicalization.json')['native_to_canonical'].items()}
assert native_map[0]==0 and native_map[254]==215 and native_map[84]==83 and len(set(native_map.values()))==216
canonical=table(P/'machine/k215.tm')
assert {(native_map[q],b):(w,d,native_map[z])for(q,b),(w,d,z)in new.items()}==canonical
rendered={}
for q,a,b in re.findall(r'(\d+) & ([01][LR](?:\d+|H)) & ([01][LR](?:\d+|H))', (P/'sections/full_table.tex').read_text()):
 for bit,act in enumerate((a,b)):
  key=int(q),bit;assert key not in rendered;rendered[key]=(int(act[0]),act[1],215 if act[2:]=='H'else int(act[2:]))
assert rendered==canonical
closure={}
for rel in ['validate_native.py','runtime/symbolic_runtime.py','runtime/independent_runtime.py','inputs/legacy_mapping.json']:
 x=P/'code'/rel;y=A/'code/runtime-inputs'/rel;assert x.read_bytes()==y.read_bytes();closure[rel]=sha(x)
assert (P/'code/check_joint_fold.py').read_bytes()==Path('/tmp/k215-to214-folds/check_joint_fold.py').read_bytes()
closure['check_joint_fold.py']=sha(P/'code/check_joint_fold.py')
legacy={int(k):v for k,v in j(P/'code/inputs/legacy_mapping.json').items()}
def m(q):return legacy.get(q,q+1000)
state_rename={m(q):m(z)for q,z in mapping.items()}
cases=j(P/'evidence/runtime_cases.json.gz');oldcases=j(A/'verification/root-run1/runtime/runtime_cases.json.gz')
assert len(cases)==len(oldcases)==6176
for x,y in zip(oldcases,cases):
 z={**x,'rows':sorted([state_rename[q],b]for q,b in x['rows'])};assert z==y
startup=j(P/'evidence/startup.json.gz');oldstartup=j(A/'verification/root-run1/runtime/startup.json.gz')
tr=[[mapping[q],h,b,w,d,mapping[z]]for q,h,b,w,d,z in oldstartup['trace']]
assert {**oldstartup,'trace':tr}==startup
report=j(P/'evidence/runtime.json');oldreport=j(A/'verification/root-run1/runtime/runtime.json')
assert report['blocks']==oldreport['blocks']
assert report['status']=='UNIVERSAL_MATHEMATICAL_PASS'and report['failures']==[]
assert report['table_sha256']==sha(P/'machine/k215.native.tm')and report['sites_sha256']==sha(P/'source/sites215.json')
assert sum(c['symbolic_steps']for c in cases)==1698790 and min(c['duration'][0]for c in cases)==6
assert all(len(c['duration'])==13 and all(type(v)is int and v>=0 for v in c['duration']) for c in cases)
assert {tuple(k)for c in cases for k in c['rows']}=={(m(q),b)for q,b in new}
parent=table(P/'reference/partial216/machine/k216.native.tm')
assert len([k for k in new if new[k]!=parent[k]])==36
assert {q for q,b in parent}-{q for q,b in new}=={185}
refs={}
for rel,original in [
 ('reference/permuted216/sections/source_calibration.tex','/tmp/zfc-intake197/extracted/K216_Permuted_Commands_2026-10-21/sections/source_calibration.tex'),
 ('reference/permuted216/sites210.json','/tmp/zfc-intake197/extracted/K216_Permuted_Commands_2026-10-21/source/sites210.json')]:
 x=P/rel;y=Path(original)
 if not y.exists() and rel.endswith('sites210.json'):y=Path('/tmp/zfc-intake197/extracted/K216_Permuted_Commands_2026-10-21/source/primary/sites210.json')
 if not y.exists() and rel.endswith('sites210.json'):y=A/'code/source-inputs/permuted210.json'
 assert x.read_bytes()==y.read_bytes();refs[rel]=sha(x)
readfiles=['README.md','report.tex','sections/source_calibration.tex','sections/further_research.tex','sections/full_table.tex',
 'code/reconstruct.py','code/audit_source.py','code/audit_folds.py','code/audit_machine.py','code/audit_blank.py',
 'code/negative_control.py','code/validate_native.py','code/check_joint_fold.py','code/repack.py','verify.py','build.sh',
 'reference/SNAPSHOT.md','reference/foundational/KLower221.lean','provenance/INPUTS.json','provenance/ATTRIBUTION.md']
result={'status':'PASS_INDEPENDENT_LITERAL_AND_SAVED_RECORD_COMPARISON','scope':'No delivered execution, machine replay, compiler, manifest suite, ancestor replay or PDF-render claim. Native/dense and stored evidence comparison only, with earlier root actual proof transferred through exact initial/dispatcher/halt-preserving conjugacy.',
 'files':len([p for p in P.rglob('*')if p.is_file()]),'native_sha256':sha(P/'machine/k215.native.tm'),'canonical_sha256':sha(P/'machine/k215.tm'),
 'source_sha256':sha(P/'source/sites215.json'),'changed_native_labels':[[q,z]for q,z in sorted(mapping.items())if q!=z],
 'full_state_map_from_accepted':mapping,'rows_compared':430,'source_byte_identity':True,'typeset_rows_match':430,
 'all6176_saved_cases_match_after_exact_legacy_row_renaming':True,'all95714_saved_startup_events_match_after_native_renaming':True,
 'whole_tape_endpoint_unchanged':True,'runtime_blocks_identical':True,'delivered_timing_not_root_fresh':report['seconds'],
 'runtime_closure_exact_previous':closure,'reference_exact_previous':refs,
 'full_text_read_sha256':{p:sha(P/p)for p in readfiles},'own_reader_sha256':sha(Path(__file__))}
(O/'inspection.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ['full_state_map_from_accepted','full_text_read_sha256']},indent=2))
