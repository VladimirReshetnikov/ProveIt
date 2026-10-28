from pathlib import Path
import hashlib, json, re
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=ROOT/'Computability/DiophantineConsistency'
PARENT=D/'research/arithmetic-pell-integral-solution-cache-plan.json'
OUT=D/'research/arithmetic-pell-index-divisibility-cache-plan.json'
pins={};observations=0

def require(ok,message):
    if not ok: raise RuntimeError(message)

def record(path):
    path=Path(path);data=path.read_bytes()
    return dict(path=str(path),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))

def check(expected):
    global observations
    actual=record(expected['path'])
    require(actual['sha256']==expected['sha256'],'hash '+expected['path'])
    if 'bytes' in expected: require(actual['bytes']==expected['bytes'],'size '+expected['path'])
    pins[actual['path']]=actual;observations+=1
    return actual

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
    clean=''.join(o)
    initial=[] if re.search(r'^\s*prelude\s*$',clean,re.M) else ['Init']
    return list(dict.fromkeys(initial+[n for line in re.findall(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',clean,re.M) for n in line.split()]))

def supplement(packet,sha,manifest,msha,module,status):
    packet=check(dict(path=str(D/packet),sha256=sha))
    manifest=check(dict(path=str(D/manifest),sha256=msha))
    for item in json.loads(Path(manifest['path']).read_text()):
        check(dict(item,path=str(ROOT/item['path'])))
    data=json.loads(Path(packet['path']).read_text())
    require(data['status']=='PASS','supplement status')
    for row in data['records']:
        for key in ['source','snapshot','log','timing','object']:check(row[key])
        require(row['exit_code']==0,'supplement exit')
    selected=next(row for row in data['records'] if row['module']==module)
    for key in ['state','final_state','durable_state','driver','final_authentication','freeze_authentication']:
        if key in data:check(data[key])
    return dict(module=module,source=selected['source'],objects=[selected['object']],
        imports=imports(selected['source']['path']),provenance=status,
        supplement_packet=packet,supplement_manifest=manifest)

require(not OUT.exists(),'new inventory')
check(dict(path=str(PARENT),sha256='27b365f34e47feeaaaa6e32c3987ed2cebbb3a6e333673c4d4717b52b3afcee2'))
p=json.loads(PARENT.read_text())
for pin in p['pins']:check(pin)
mods={x['module']:x for x in p['modules']};external={x['module']:x for x in p['external']}
sp=check(dict(path=str(D/'research/arithmetic-pell-integral-solution-accepted-strong-divisibility.json'),
    sha256='05fefd83261e8d29c8dd652190f92e0f952f049cfad6cc9f00dbfd1509168aa9'))
s=json.loads(Path(sp['path']).read_text())
for pin in s['pins']:check(pin)
old=mods[s['module']]
require(old['source']==s['source'] and old['objects']==[s['old_object']],'accepted supplement')
old['objects']=[s['accepted_object']]
old['provenance']='ROOT accepted provider supplement, original inventory unchanged'
entry=supplement('reviews/arithmetic-pell-integral-solution-replay.json',
    '7c71696cfc3682163f91bedeedd2e4c26f757cd887e196234d000934e1b33110',
    'reviews/arithmetic-pell-integral-solution-author-replay/FILES.json',
    '7fc8c5e8f8a707603278db924eedf50ed81b9e3cc8c58d983b080c1061059ff1',
    'DiophantineConsistency.ArithmeticPellIntegralSolution',
    'PROVISIONAL author-validated; ROOT independent acceptance pending')
require(entry['module'] not in mods,'new supplement');mods[entry['module']]=entry
seen=set();active=set();order=[];used=set()
def visit(name):
    if name not in mods:
        require(name in external,'new boundary '+name);used.add(name);return
    if name in seen:return
    require(name not in active,'cycle');active.add(name)
    item=mods[name];check(item['source'])
    require(imports(item['source']['path'])==item['imports'],'header '+name)
    for dep in item['imports']:visit(dep)
    for obj in item['objects']:check(obj)
    active.remove(name);seen.add(name);order.append(name)

direct=['DiophantineConsistency.ArithmeticPellIntegralSolution']
for name in direct:visit(name)
boundary=[external[name] for name in sorted(used)];first=[]
for item in boundary:
    check(item['source'])
    for obj in item['artifacts']:
        check(obj)
        relative=Path(*item['module'].split('.')[:-1])/Path(obj['path']).name
        actual=next((Path(root)/relative for root in p['boundary_search'] if (Path(root)/relative).is_file()),None)
        require(actual is not None,'missing boundary provider')
        first.append(dict(module=item['module'],expected=obj,actual=check(dict(obj,path=str(actual)))))
counts=dict(custom=len(order),Foundation=sum(name.startswith('Foundation.') for name in order),
    artifacts=sum(len(mods[name]['objects']) for name in order),external=len(boundary),
    boundary_artifacts=sum(len(item['artifacts']) for item in boundary),boundary_primaries=len(boundary),
    boundary_companions=sum(len(item['artifacts'])-1 for item in boundary),fresh_prerequisites=0)
require(counts==dict(custom=102,Foundation=95,artifacts=387,external=38,
    boundary_artifacts=114,boundary_primaries=38,boundary_companions=76,fresh_prerequisites=0),'exact scope')
check(p['compiler']);check(record(__file__))
for pin in list(pins.values()):check(pin)
result=dict(status='READ_ONLY_AUTHENTICATED_PLAN_NO_COMPILER_OR_OVERLAY',parent=record(PARENT),
    direct_imports=direct,counts=counts,modules=[mods[name] for name in order],topological_order=order,
    external=boundary,boundary_search=p['boundary_search'],boundary_first_providers=first,
    compiler=p['compiler'],audit=record(__file__),pins=list(pins.values()),observations=observations,
    unique_paths=len(pins),accepted_strong_supplement=sp,provisional_module='DiophantineConsistency.ArithmeticPellIntegralSolution',
    scope='Proposed ArithmeticPellIndexDivisibility plus Checks: natural quotient/certificate recurrence proves c|m and completes the actual relaxed norm endpoint using IntegralSolution. IntegralSolution author provider remains provisional pending ROOT acceptance. No compiler, overlay, source edits, dependency refresh, power/cubic congruence, final target-index or HA claim.')
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(plan=record(OUT),counts=counts,observations=observations,unique_paths=len(pins)),indent=2))
