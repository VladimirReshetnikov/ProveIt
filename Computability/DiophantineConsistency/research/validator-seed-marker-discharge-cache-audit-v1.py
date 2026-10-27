"""Read/hash a minimal current-source closure; no compiler or overlay."""
from pathlib import Path
import hashlib,json,re
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=ROOT/'Computability/DiophantineConsistency'
OUT=D/'research/validator-seed-marker-discharge-cache-plan.json'
OBS={}
def need(ok,msg):
    if not ok:raise RuntimeError(msg)
def rec(p):
    p=Path(p);data=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
def pin(p,h=None):
    if isinstance(p,dict):h=p['sha256'];p=p['path']
    r=rec(p);need(h is None or r['sha256']==h,'hash '+str(p));OBS[r['path']]=r;return r
def read(p):return json.loads(Path(p).read_text())
def imports(p):
    s=Path(p).read_text();out=[];i=depth=0
    while i<len(s):
        pair=s[i:i+2]
        if depth:
            if pair=='/-':depth+=1;i+=2
            elif pair=='-/':depth-=1;i+=2
            else:out.append('\n'if s[i]=='\n'else' ');i+=1
        elif pair=='/-':depth=1;i+=2
        elif pair=='--':
            while i<len(s)and s[i]!='\n':i+=1
        else:out.append(s[i]);i+=1
    need(depth==0,'balanced comments')
    return list(dict.fromkeys(['Init']+[n for line in re.findall(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',''.join(out),re.M)for n in line.split()]))
need(not OUT.exists(),'new inventory')
basepath=D/'reviews/validator-seed-guarded-comprehension222-cache.json'
pin(basepath,'ff8d69d0791575a5cc9f63e96d1c1fa90bef24ec92600929f773d6208cace568');base=read(basepath)
for r in base['inherited_observations']+base['parent_receipts']:pin(r)
tagpath=D/'research/validator-seed-tagged-interpretation-plan.json';pin(tagpath)
old=read(tagpath)['branches']['later_internal_marker_transport_candidates']
extra=next(r for r in old['modules_dependency_order']if r['module']=='BoundedPAConsistency.InternalRelativization')
pin(extra['source'],extra['source_sha256']);pin(extra['provenance'])
historic=read(extra['provenance']['path']);need(historic['status']=='PASS','historical success')
hs=next(x for x in historic['sources']if x['module']==extra['module'])
pin(hs['snapshot'],hs['source_sha256']);need(hs['source_sha256']==extra['source_sha256'],'historical source')
ho=next(x for x in historic['fresh_modules']if x['module']==extra['module'])
pin(ho);need(ho['sha256']==extra['objects'][0]['sha256'],'historical object')
for absent in extra['absent_companions']:need(not Path(absent).exists(),'historical absence changed')
mods={r['module']:r for r in base['modules']};mods[extra['module']]=extra
provider=next(x for x in historic['providers']if x['module']=='Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic')
current=mods[provider['module']]
need(current['source_sha256']==provider['source_sha256'],'direct Foundation source match')
need(next(x['sha256']for x in current['objects']if x['path'].endswith('.olean'))==provider['object_sha256'],'direct Foundation object match')
ext={r['module']:r for r in base['external']};seen=set();active=set();used=set();order=[]
def visit(n):
    if n not in mods:need(n in ext,'unknown boundary '+n);used.add(n);return
    if n in seen:return
    need(n not in active,'cycle');active.add(n);r=mods[n]
    pin(r['source'],r['source_sha256']);actual=imports(r['source'])
    need(actual==r.get('actual_imports',r['imports']),'header '+n)
    for dep in actual:visit(dep)
    for obj in r['objects']:pin(obj)
    active.remove(n);seen.add(n);order.append(r)
direct=['ZFCinPA.ValidatorSeedSourceBasis222','BoundedPAConsistency.InternalRelativization']
for n in direct:visit(n)
external=[ext[n]for n in sorted(used)]
for r in external:pin(r)
paths=[str(Path(extra['objects'][0]['path']).parents[1]),*base['lean_path'].split(':')]
providers=[]
for m in order+external:
    for obj in m['objects']if 'objects'in m else[m]:
        rel=Path(*m['module'].split('.')[:-1])/Path(obj['path']).name
        p=next((Path(q)/rel for q in paths if(Path(q)/rel).is_file()),None)
        need(p is not None,'provider '+str(rel));actual=pin(p,obj['sha256'])
        providers.append(dict(module=m['module'],expected=obj,actual=actual))
for name in ['compiler','manifest','toolchain']:pin(base[name],base[name+'_sha256'])
proposal=pin(D/'research/validator-seed-marker-discharge-plan.md');driver=pin(__file__)
counts=dict(cached_modules=len(order),foundation=sum(r['module'].startswith('Foundation.')for r in order),
    artifacts=sum(len(r['objects'])for r in order),external_boundaries=len(external))
need(counts==dict(cached_modules=202,foundation=136,artifacts=610,external_boundaries=45),'exact scope')
need(len(providers)==655,'all artifact providers')
OUT.write_text(json.dumps(dict(status='READ_ONLY_AUTHENTICATED_NO_COMPILER_OR_OVERLAY',
    direct_imports=direct,counts=counts,modules=order,external=external,search_paths=paths,
    actual_first_artifact_providers=providers,compiler=pin(base['compiler']),
    manifest=pin(base['manifest']),toolchain=pin(base['toolchain']),
    proposal=proposal,driver=driver,historical=pin(extra['provenance']),
    observations=list(OBS.values()),new_prerequisite_refresh=[],
    qualification='Historical source/object and its direct Foundation boundary match current selection. Absence/companion qualifications preserved; no broad rebuild.'),indent=2)+'\n')
print(json.dumps(dict(path=str(OUT),sha256=rec(OUT)['sha256'],counts=counts,providers=len(providers),paths=len(OBS)),indent=2))
