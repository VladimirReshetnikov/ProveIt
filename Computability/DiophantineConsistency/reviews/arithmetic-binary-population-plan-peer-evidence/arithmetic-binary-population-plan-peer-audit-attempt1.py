"""Independent read-only plan authentication: no subprocess or overlay."""
from pathlib import Path
import hashlib, json, re, shutil
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
DC=ROOT/'Computability/DiophantineConsistency'
OUT=DC/'reviews/arithmetic-binary-population-plan-peer-audit.json'
pins={}; count=0

def need(ok,msg):
    if not ok: raise RuntimeError(msg)
def record(path):
    p=Path(path); data=p.read_bytes()
    return dict(path=str(p),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
def check(pin):
    global count
    got=record(pin['path']); need(got['sha256']==pin['sha256'],'hash '+pin['path'])
    need('bytes' not in pin or got['bytes']==pin['bytes'],'bytes '+pin['path'])
    pins[got['path']]=got; count+=1; return got
def load(pin): return json.loads(Path(check(pin)['path']).read_text())
def header(path):
    s=Path(path).read_text(); clean=[]; i=depth=0
    while i<len(s):
        token=s[i:i+2]
        if depth:
            if token=='/-': depth+=1; i+=2
            elif token=='-/': depth-=1; i+=2
            else: clean.append('\n' if s[i]=='\n' else ' '); i+=1
        elif token=='/-': depth=1; i+=2
        elif token=='--':
            while i<len(s) and s[i]!='\n': i+=1
        else: clean.append(s[i]); i+=1
    need(depth==0,'balanced comments')
    s=''.join(clean)
    out=[] if re.search(r'^\s*prelude\s*$',s,re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',s,re.M):
        out.extend(line.split())
    return list(dict.fromkeys(out))

need(not OUT.exists(),'fresh audit output')
need(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
plan_pin=dict(path=str(DC/'research/arithmetic-binary-population-cache-plan.json'),
    sha256='8db28403220c05983a67306abafc73e78ee1fb85447948ab05ab584f29fae16e')
plan=load(plan_pin)
need(plan['status']=='READ_ONLY_AUTHENTICATED_PLAN_NO_COMPILER_OR_OVERLAY','plan status')
need(plan['direct_imports']==['Foundation.FirstOrder.Arithmetic.HFS.PRF','Mathlib.Tactic.Ring'],'imports')
for p in plan['pins']: check(p)
check(plan['proposal']); check(plan['auditor']); check(plan['accepted_receipt']); check(plan['compiler'])
parent=load(plan['parent']); peer=load(plan['accepted_peer'])
need(peer['status']=='INDEPENDENT_PEER_PASS','historical accepted status')
for p in parent['pins']: check(p)
for key in ['author_packet','state','inputs','driver','bundle_manifest']: check(peer[key])
for row in peer['records']:
    need(row['exit_code']==0 and row['matches_author'],'accepted independent match')
    for key in ['source','snapshot','log','timing','object']: check(row[key])
mods={m['module']:m for m in plan['modules']}
bound={m['module']:m for m in plan['external']}
need(len(mods)==len(plan['modules']) and len(bound)==len(plan['external']),'unique modules')
need(mods=={m['module']:m for m in parent['modules']},'unchanged inherited modules')
need(bound=={m['module']:m for m in parent['external']},'unchanged inherited boundaries')
seen=set(); active=set(); used=set(); order=[]
def visit(n):
    if n not in mods:
        need(n in bound,'unknown boundary '+n); used.add(n); return
    if n in seen: return
    need(n not in active,'acyclic'); active.add(n)
    m=mods[n]; check(m['source']); need(header(m['source']['path'])==m['imports'],'source header '+n)
    for child in m['imports']: visit(child)
    for artifact in m['objects']: check(artifact)
    active.remove(n); seen.add(n); order.append(n)
for name in plan['direct_imports']: visit(name)
need(seen==set(mods) and used==set(bound),'exact reachable scope')
need(order==plan['topological_order'],'topological order')
for m in bound.values():
    check(m['source'])
    for a in m['artifacts']: check(a)
need(plan['boundary_search']==parent['boundary_search'],'boundary search')
search=[str(Path(peer['private'])/'lib'),*plan['boundary_search']]
need(search==plan['audited_existing_search'],'accepted first-provider search')
stored={(p['module'],p['relative']):p for p in plan['first_providers']}
need(len(stored)==len(plan['first_providers']),'unique provider mappings')
actual=[]
for m in plan['modules']+plan['external']:
    for a in m.get('objects',m.get('artifacts')):
        relative=str(Path(*m['module'].split('.')[:-1])/Path(a['path']).name)
        first=next((Path(base)/relative for base in search if (Path(base)/relative).is_file()),None)
        need(first is not None,'missing first provider')
        p=stored[(m['module'],relative)]
        need(p['expected']==a and p['actual']['path']==str(first),'exact provider mapping')
        check(a); got=check(p['actual']); need(got['sha256']==a['sha256'],'provider artifact')
        actual.append(p)
counts=dict(custom=len(mods),Foundation=sum(n.startswith('Foundation.') for n in mods),
    artifacts=sum(len(m['objects']) for m in mods.values()),external=len(bound),
    boundary_artifacts=sum(len(m['artifacts']) for m in bound.values()),
    actual_first_providers=len(actual),fresh_prerequisites=0)
need(counts==plan['counts']==dict(custom=95,Foundation=95,artifacts=380,external=38,
    boundary_artifacts=114,actual_first_providers=494,fresh_prerequisites=0),'exact counts')
old=DC/'research/arithmetic-binary-population-cache-audit-attempt1.py'
current=Path(plan['auditor']['path'])
need(old.read_text().replace("peer['status'] == 'PASS'","peer['status'] == 'INDEPENDENT_PEER_PASS'")
    ==current.read_text(),'only historical administrative status correction')
for p in [old,DC/'research/arithmetic-binary-population-cache-audit-attempt1.md',Path(__file__)]: check(record(p))
for p in list(pins.values()): check(p)
need(shutil.disk_usage('/tmp').free>=512*1024**2,'final reserve')
result=dict(status='PASS_READ_ONLY_INDEPENDENT_PLAN_REAUTHENTICATION',plan=check(plan_pin),
    proposal=plan['proposal'],auditor=record(__file__),counts=counts,
    comparisons=count,unique_paths=len(pins),pins=list(pins.values()),first_providers=actual,
    mathematical_review='Complete proposal/PRF and precise fbit, length and bounded-definability contracts read. No mathematical gap identified; explicit existential exponential-bound witness is available for Sigma1 motives.',
    prior_role='Reviewer of accepted PellRecurrence; no authorship of the new population proposal and no new implementation reviewed.',
    limits='No Lean compiler, overlay, dependency refresh or source edit. Package internals remain inherited boundaries; this is not proof acceptance.',
    free_bytes=shutil.disk_usage('/tmp').free)
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(audit=record(OUT),counts=counts,comparisons=count,paths=len(pins)),indent=2))
