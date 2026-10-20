#!/usr/bin/env python3
"""Own metadata/row parser; imports and executes no candidate module."""
from pathlib import Path
import hashlib,json
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC');P=ROOT/'k218-context-allocation';O=Path(__file__).resolve().parent
checks=0

def need(v,why):
 global checks
 assert v,why;checks+=1

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
 t={}
 for line in p.read_text().splitlines():
  if not line.strip()or line.startswith('#'):continue
  q,r,w,d,z=line.split();key=(int(q),int(r));row=(int(w),{'L':-1,'R':1}[d],int(z));need(key not in t,'Duplicate row');need(key[1]in(0,1)and row[0]in(0,1),'Binary row');t[key]=row
 states={q for q,r in t};need(set(t)=={(q,r)for q in states for r in(0,1)},'Total rows');return t
old=table(ROOT/'candidate-k218/k218.native.tm');need(len(old)==436,'218 baseline');need(max(q for q,r in old)==301,'Native301 exists')
a=(P/'history/context_allocate.py').read_text();b=(P/'context_allocate.py').read_text();anchor='old=s.tree('
need(a[a.index(anchor):]==b[b.index(anchor):],'Portable algorithm exact suffix')
need((P/'context_allocate.py').resolve().parents[5]==ROOT.parents[3],'Portable default repo path')
meta=json.loads((P/'publication.json').read_text());need(sha(P/'inputs/qs000.json')==meta['input_identities']['qs000']['sha256'],'QS copied input');need(sha(P/'inputs/mixed000.json')==meta['input_identities']['mixed000']['sha256'],'M copied input')
need((P/'inputs/qs000.json').read_bytes()==(ROOT/'k218-quantifier-stability/source-span-dp/evidence/verified/candidate000/sites.json').read_bytes(),'QS published source same')
need((P/'inputs/mixed000.json').read_bytes()==(ROOT/'k218-ks-mixed-commutation/source-pricing/evidence/verified-v2/candidate000/sites.json').read_bytes(),'M published source same')
results=[]
for name,total,fresh in [('qs-context000-v2',241,28),('m-context000',262,49)]:
 path=P/'evidence'/name;r=json.loads((path/'result.json').read_text());t=table(path/'prefix-only.tm');states={q for q,r in t};oldstates={q for q,r in old}
 need(r['status']=='CONTEXT_AWARE_PREFIX_PASS','Reported pass');need(len(t)//2==r['working_states']==total,'State count');need(r['fresh']==fresh==len(r['assignments']),'Fresh assignments')
 need(r['retired']==sorted(oldstates-states)==[135,142,174,185,214],'Retired list');need(218+fresh-len(r['retired'])==total,'Count accounting')
 for key in t:
  if key[0]in oldstates and key[0]!=84:need(t[key]==old[key],'All retained old rows unchanged except84')
 need(len({tuple(tuple(x)for x in a['rows'])for a in r['assignments']})==fresh,'Distinct new action pairs')
 for assignment in r['assignments']:
  q=assignment['state'];need(q>=302,'Fresh state beyond native301')
  for bit,row in enumerate(assignment['rows']):need(t[q,bit]==tuple(row),'Fresh assignment matches table')
 seen={0};todo=[0]
 for q in todo:
  for bit in(0,1):
   z=t[q,bit][2];need(z==254 or(z,0)in t,'Resolved target')
   if z!=254 and z not in seen:seen.add(z);todo.append(z)
 need(seen==states,'Exactly syntactically reachable states')
 results.append({'name':name,'states':total,'fresh':fresh,'retired':r['retired'],'seconds_reported':r['seconds'],'claim':'Recorded root prefix-pass; independently checked table structure, assignments, retained rows and input identities. No prefix or primitive execution by reviewer.'})
fail=json.loads((P/'evidence/qs-context000/result.json').read_text());need(fail['status']=='REJECTED','First actual failure retained');need({300,301}<={a['state']for a in fail['assignments']},'Failed numbering occupied native301')
protected=json.loads((P/'evidence/protected-result.json').read_text());need(len(protected['protected_states'])==38 and protected['status']=='REJECTED','38 helper protection rejected scope')
trace=[r for r in protected['old_live_helper_witnesses']if r['state']==69 and r['prefix']=='11010010011000'and r['bit']==0];need(len(trace)==1,'Old69 witness unique');need([t[0]for t in trace[0]['trace']]==[69,78,89],'Old helper sequence');need(trace[0]['trace'][-1][-1][-1]==104,'Old helper destination104')
rs=json.loads((P/'evidence/result.json').read_text());f=next(r for r in rs if 'changed_cells'in r);need(f['state']==17 and f['changed_cells']==[[16,1,0]]and f['attempted_states']==226,'First wrong-prefix diagnosis')
rs=json.loads((P/'evidence/result-protected.json').read_text());need(rs[0]['unexpected_unchanged_state']==183 and rs[0]['prefix']=='1101001001100110110','Protected wrong old role183')
f=next(r for r in rs if 'changed_cells'in r);a=next(a for a in f['ancestors']if a[0]==76);need([t[0]for t in a[3]]==[76,152,170,169,171,7,205]and a[3][-1][-1][-1]==183,'Wrong-context76 route')
inputs={str(f.relative_to(P)):{'sha256':sha(f),'bytes':f.stat().st_size}for f in sorted(P.rglob('*'))if f.is_file()}
r={'status':'INDEPENDENT_CONTEXT_ALLOCATOR_SOURCE_AND_RECORD_REVIEW_PASS','reviewer':'opening_encoder','role':'Author of the source-DP inputs and earlier rejected allocator policy, independent reader of root context-aware successor/localization. No candidate allocator, prefix simulator, primitive runtime or startup replay.','checks':checks,'inputs':inputs,'findings':[],'results':results,'source_review':['Full portable and executed source bodies match exactly after path setup.','Compatibility rejects changed prefix tape/head and recursively checks each internal child in its actual new prefix context. Leaves intentionally remain outside the proved contract.','Fresh numbering starts above native301; old rows are untouched except decoder root84 and syntactically unreachable removal. Final complete prefix check remains mandatory.','The old global-pool incoming-edge condition omitted multi-step helper uses. Protecting such helpers does not solve context-dependent old decoder placement; retained traces distinguish the two failures.','The100-step internal bound conservatively rejects slow or unresolved paths; no universal primitive behavior follows.','Portable driver has no seed/hash enforcement itself; this receipt pins the current published seed/input/library boundary and the documented records. Re-running against changed repository inputs would be a new experiment.'],'scope':'241/262 are conservative prefix-bound diagnostic table counts, not smaller machines or lower bounds. Literal leaf-entry actions, primitive runtime, startup and enumerator simulation remain unproved for these tables.'}
(O/'review.json').write_text(json.dumps(r,indent=2)+'\n');print(checks,sha(O/'review.json'))
