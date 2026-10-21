"""Independent finite decoder-prefix audit, not received executable code."""
import os, sys
if sys.flags.optimize or os.environ.get("PYTHONOPTIMIZE"):
    raise SystemExit("Audit requires assertions: reject -O, -OO, and nonempty PYTHONOPTIMIZE.")
from pathlib import Path
import json,hashlib,collections
B=Path(__file__).resolve().parent
P=B/'extracted/K215_Checked_Simplifications_2026-10-21/decoder_lean/inputs'
EXPECTED_INPUT_SHA256={
 'decoder_context_certificate.json':'9dc3d2fb25020992de466b2d91eb15f00539da585d9e6219bb372e6352c7beff',
 'k215.native.tm':'9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2',
 'sites215.json':'17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba',
}
for name,expected in EXPECTED_INPUT_SHA256.items():
 if hashlib.sha256((P/name).read_bytes()).hexdigest()!=expected:
  raise SystemExit('Pinned decoder input changed: '+name)
doc=json.loads((P/'decoder_context_certificate.json').read_text());sites=json.loads((P/'sites215.json').read_text())
M={}
for line in (P/'k215.native.tm').read_text().splitlines():
 if line.startswith('#') or not line.strip():continue
 q,b,w,m,n=line.split();M[int(q),int(b)]=(int(w),1 if m=='R' else -1,int(n))
roles=doc['roles'];memo={}
def bound(i):
 if i in memo:return memo[i]
 role=roles[i];values=[]
 for e in role['edges']:
  if e['kind']=='primitive':values.append(1)
  else:
   assert roles[e['role']]['node']<role['node']
   values.append(e['steps']+bound(e['role']))
 memo[i]=max(values);return memo[i]
maximum=bound(0);hist=collections.Counter();max_paths=[];steps_total=0
for path,op,arg in sites:
 t={-1:1,**{i:int(b) for i,b in enumerate(path)}};initial=t.copy();q=84;h=0;rid=0;count=0
 for k,ch in enumerate(path):
  r=roles[rid];e=r['edges'][int(ch)];assert q==r['state'] and h==k and t==initial
  if k+1<len(path):
   assert e['kind']=='internal';nr=roles[e['role']]
   for _ in range(e['steps']):
    assert h in t
    w,delta,q=M[q,t[h]];t[h]=w;h+=delta;count+=1
   assert t==initial and h==k+1 and q==nr['state'];rid=e['role']
  else:
   assert e['kind']=='primitive' and doc['nodes'][e['node']]==[op,arg]
   assert tuple(e['action'])==M[q,t[h]]
   w,delta,q=M[q,t[h]];t[h]=w;h+=delta;count+=1
   wanted=initial.copy();wanted[k]=w;assert t==wanted
 hist[count]+=1;steps_total+=count
 if count==maximum:max_paths.append([path,op,arg])
assert max(hist)==maximum==56 and len(sites)==4751 and len(memo)==234
result={'source_json_sha256':hashlib.sha256((P/'decoder_context_certificate.json').read_bytes()).hexdigest(),'native_sha256':hashlib.sha256((P/'k215.native.tm').read_bytes()).hexdigest(),'sites_sha256':hashlib.sha256((P/'sites215.json').read_bytes()).hexdigest(),'expanded_paths_replayed':len(sites),'reachable_roles':len(memo),'maximum_steps_including_first_primitive_transition':maximum,'maximum_internal_block_prefix_steps':maximum-1,'minimum_path_length':min(len(p) for p,_,_ in sites),'maximum_path_length':max(len(p) for p,_,_ in sites),'literal_transitions_replayed':steps_total,'initial_guard':'state84 at head a, t(a-1)=1, source path bits at t(a+i)','guarantee':'Internal decoding blocks restore all known cells, do not read outside them, advance one path cell per block, then execute the exact leaf-entry action.','does_not_establish':['Full primitive semantics','Pointer return','Register-box preservation','KSites215 coverage','Universal compiled source-path theorem','Full endpoint or build performance'],'step_histogram':dict(sorted(hist.items())),'maximum_paths':max_paths}
(B/'DECODER_PREFIX_RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['step_histogram','maximum_paths']},indent=2));print('maximum paths',len(max_paths))
