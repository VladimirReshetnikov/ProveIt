"""Validate only retained adoption/generation context while the kernel run continues."""
from pathlib import Path
from copy import deepcopy
import json
from evidence import digest,save,sha,validate_context
P=Path(__file__).resolve().parent;R=Path('/home/codex/.codex/worktrees/ec20/Proofs');run=Path('/tmp/k215-proof-phase5/lean-run1');basis=Path('/tmp/k215-proof-phase4/lean-run1')
read=lambda p:json.loads(p.read_text())
inv=read(run/'inventory.json');old=read(basis/'inventory.json');owner=read(run/'owner.json')
m={'review/context.json':(P/'context.json').read_bytes()}
for r in read(P/'context.json')['files']:
 p=Path(r['path']);assert sha(p)==r['sha256'];m[r['member']]=p.read_bytes()
for e in inv['modules']:m['execution/sources/'+e['module'].replace('.','/')+'.lean']=Path(e['source']).read_bytes()
checked=validate_context(m,inv,old,owner,R)
checks=[]
def reseal(v,n,f):
 r=json.loads(v[n]);f(r);v[n]=(json.dumps(r,indent=2)+'\n').encode()
 ctx=json.loads(v['review/context.json'])
 row=next(r for r in ctx['files'] if r['member']==n);row.update(sha256=digest(v[n]),bytes=len(v[n]))
 v['review/context.json']=(json.dumps(ctx,indent=2)+'\n').encode()
def reject(name,fn):
 v=deepcopy(m);fn(v)
 try:validate_context(v,inv,old,owner,R)
 except (AssertionError,KeyError):checks.append({'name':name,'status':'REJECTED'})
 else:raise AssertionError(name)
reject('self-consistent wrong adoption after pin',lambda v:reseal(v,'adoption/adoption.json',lambda r:r['sources'][0].update(after_sha256='0'*64)))
reject('self-consistent wrong adoption before pin',lambda v:reseal(v,'adoption/adoption.json',lambda r:r['sources'][0].update(before_sha256='0'*64)))
reject('missing one adoption',lambda v:reseal(v,'adoption/adoption.json',lambda r:r['sources'].pop()))
reject('self-consistent changed regeneration output',lambda v:reseal(v,'adoption/generation/result.json',lambda r:r['files'].update({'KSource215.lean':'0'*64})))
reject('self-consistent generator input changed',lambda v:reseal(v,'adoption/generation/result.json',lambda r:r['inputs'].update({next(iter(r['inputs'])):'0'*64})))
reject('storage report claims modified basis',lambda v:reseal(v,'adoption/storage-deduplication.json',lambda r:r.update(immutable_primary_and_predecessor_caches_untouched=False)))
for r in read(P/'context.json')['files']:assert sha(r['path'])==r['sha256']
record={'status':'PASS_READ_ONLY_ADOPTION_CONTEXT_CONTROLS','checked':checked,'negative_controls':checks,'sources':{n:sha(P/n) for n in ['evidence.py','capture.py','publish.py','control.py','context.json','context_controls.py']},'scope':'Original context/current source bindings and6 private resealed mutations only. No phase5 completion, compiler or regeneration/storage execution claim.'}
save(P/'context-controls1.json',record);print(json.dumps({'status':record['status'],'negative_controls':len(checks)},indent=2))
