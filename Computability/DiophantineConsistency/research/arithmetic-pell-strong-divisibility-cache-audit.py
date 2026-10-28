from pathlib import Path
import hashlib,json,re
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs');D=ROOT/'Computability/DiophantineConsistency'
PARENT=D/'research/arithmetic-pell-congruences-cache-plan.json'
OUT=D/'research/arithmetic-pell-strong-divisibility-cache-plan.json'
pins={};observations=0

def require(ok,msg):
    if not ok:raise RuntimeError(msg)
def record(path):
    path=Path(path);data=path.read_bytes()
    return dict(path=str(path),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
def check(pin):
    global observations
    a=record(pin['path']);require(a['sha256']==pin['sha256'],'hash '+pin['path'])
    if 'bytes' in pin:require(a['bytes']==pin['bytes'],'size '+pin['path'])
    pins[a['path']]=a;observations+=1;return a

def imports(path):
    s=Path(path).read_text();o=[];i=depth=0
    while i<len(s):
        pair=s[i:i+2]
        if depth:
            if pair=='/-':depth+=1;i+=2
            elif pair=='-/':depth-=1;i+=2
            else:o.append('\n' if s[i]=='\n' else ' ');i+=1
        elif pair=='/-':depth=1;i+=2
        elif pair=='--':
            while i<len(s) and s[i]!='\n':i+=1
        else:o.append(s[i]);i+=1
    require(depth==0,'comments')
    clean=''.join(o);initial=[] if re.search(r'^\s*prelude\s*$',clean,re.M) else ['Init']
    return list(dict.fromkeys(initial+[n for line in re.findall(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',clean,re.M) for n in line.split()]))

require(not OUT.exists(),'new inventory')
check(dict(path=str(PARENT),sha256='a5182706264e4a28a0ff58f2a97cf32a2860e7246ff3c04d76a163a9e83f8f99'))
p=json.loads(PARENT.read_text())
for pin in p['pins']:check(pin)
packet=check(dict(path=str(D/'reviews/arithmetic-gcd-normalization-root-replay.json'),
    sha256='b74df44673d2f89c82b6c85237c1e203a03296068dd0f6d455ecf4ad29d14512'))
manifest=check(dict(path=str(D/'reviews/arithmetic-gcd-normalization-root-replay/FILES.json'),
    sha256='b63ead412d73162dce5f37a2605776c3662c779382f45620d96f38831aa5a009'))
receipt=check(dict(path=str(D/'reviews/arithmetic-gcd-normalization-root.md'),
    sha256='535322187b6410a60eed2c09d2ffaf715e6406781ebc0408d1c6ab1e74717d73'))
for pin in json.loads(Path(manifest['path']).read_text()):check(dict(pin,path=str(ROOT/pin['path'])))
g=json.loads(Path(packet['path']).read_text());require(g['status']=='PASS','accepted Gcd')
for row in g['records']:
    require(row['exit_code']==0 and row['author_object_and_full_log_equal'],'accepted byte comparison')
    for field in ['source','snapshot','object','log','timing']:check(row[field])
for field in ['author','state','durable_state','driver','final_authentication']:check(g[field])
gcd=next(row for row in g['records'] if row['module']=='DiophantineConsistency.ArithmeticGcdNormalization')
mods={m['module']:m for m in p['modules']};ext={e['module']:e for e in p['external']}
mods[gcd['module']]=dict(module=gcd['module'],source=gcd['source'],objects=[gcd['object']],
    imports=imports(gcd['source']['path']),provenance='ROOT accepted e821823841, independent fresh provider',
    accepted_packet=packet,accepted_manifest=manifest,accepted_receipt=receipt)
seen=set();active=set();order=[];used=set()
def visit(name):
    if name not in mods:require(name in ext,'new boundary '+name);used.add(name);return
    if name in seen:return
    require(name not in active,'cycle');active.add(name);item=mods[name]
    check(item['source']);require(imports(item['source']['path'])==item['imports'],'header '+name)
    for dep in item['imports']:visit(dep)
    for obj in item['objects']:check(obj)
    active.remove(name);seen.add(name);order.append(name)
direct=['DiophantineConsistency.ArithmeticPellRecurrence','DiophantineConsistency.ArithmeticGcdNormalization']
for name in direct:visit(name)
boundary=[ext[name] for name in sorted(used)];providers=[]
for item in boundary:
    check(item['source'])
    for obj in item['artifacts']:
        check(obj);rel=Path(*item['module'].split('.')[:-1])/Path(obj['path']).name
        first=next((Path(root)/rel for root in p['boundary_search'] if (Path(root)/rel).is_file()),None)
        require(first is not None,'boundary provider')
        providers.append(dict(module=item['module'],expected=obj,actual=check(dict(obj,path=str(first)))))
counts=dict(custom=len(order),Foundation=sum(n.startswith('Foundation.') for n in order),
    artifacts=sum(len(mods[n]['objects']) for n in order),external=len(boundary),
    boundary_artifacts=sum(len(e['artifacts']) for e in boundary),boundary_primaries=len(boundary),
    boundary_companions=sum(len(e['artifacts'])-1 for e in boundary),fresh_prerequisites=0)
require(counts==dict(custom=97,Foundation=95,artifacts=382,external=38,
    boundary_artifacts=114,boundary_primaries=38,boundary_companions=76,fresh_prerequisites=0),'minimal scope')
require('DiophantineConsistency.ArithmeticPellClassification' not in seen,'no classification import')
check(p['compiler']);check(record(__file__))
for pin in list(pins.values()):check(pin)
result=dict(status='READ_ONLY_AUTHENTICATED_PLAN_NO_COMPILER_OR_OVERLAY',parent=record(PARENT),
    direct_imports=direct,counts=counts,modules=[mods[n] for n in order],topological_order=order,
    external=boundary,boundary_search=p['boundary_search'],boundary_first_providers=providers,
    compiler=p['compiler'],audit=record(__file__),pins=list(pins.values()),observations=observations,
    unique_paths=len(pins),scope='Proposed ArithmeticPellStrongDivisibility plus Checks: exact internal sequence gcd, derived index-divisibility reflection and scaled common-divisor consequence. Recurrence and accepted Gcd only; no Classification/Congruences/CommonUnit imports, no compiler/overlay/dependency refresh or full relaxed-integrality claim.')
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(plan=record(OUT),counts=counts,observations=observations,unique_paths=len(pins)),indent=2))
