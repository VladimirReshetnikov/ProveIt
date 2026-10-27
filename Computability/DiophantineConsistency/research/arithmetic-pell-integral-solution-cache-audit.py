from pathlib import Path
import hashlib,json,re
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=ROOT/'Computability/DiophantineConsistency'
OUT=D/'research/arithmetic-pell-integral-solution-cache-plan.json'
pins={};observations=0

def require(ok,message):
    if not ok:raise RuntimeError(message)

def record(path):
    p=Path(path);data=p.read_bytes()
    return dict(path=str(p),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))

def check(expected):
    global observations
    actual=record(expected['path'])
    require(actual['sha256']==expected['sha256'],'hash '+expected['path'])
    if 'bytes' in expected:require(actual['bytes']==expected['bytes'],'size '+expected['path'])
    pins[actual['path']]=actual;observations+=1
    return actual

def imports(path):
    s=Path(path).read_text();out=[];i=depth=0
    while i<len(s):
        pair=s[i:i+2]
        if depth:
            if pair=='/-':depth+=1;i+=2
            elif pair=='-/':depth-=1;i+=2
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif pair=='/-':depth=1;i+=2
        elif pair=='--':
            while i<len(s) and s[i]!='\n':i+=1
        else:out.append(s[i]);i+=1
    require(depth==0,'comments')
    clean=''.join(out)
    initial=[] if re.search(r'^\s*prelude\s*$',clean,re.M) else ['Init']
    return list(dict.fromkeys(initial+[n for line in re.findall(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',clean,re.M) for n in line.split()]))

def load_plan(name,sha):
    pin=check(dict(path=str(D/'research'/name),sha256=sha))
    data=json.loads(Path(pin['path']).read_text())
    for item in data['pins']:check(item)
    return pin,data

def supplement(packet,sha,manifest,msha,module,status):
    pp=check(dict(path=str(D/packet),sha256=sha))
    mm=check(dict(path=str(D/manifest),sha256=msha))
    for item in json.loads(Path(mm['path']).read_text()):check(dict(item,path=str(ROOT/item['path'])))
    data=json.loads(Path(pp['path']).read_text());require(data['status']=='PASS','supplement status')
    for row in data['records']:
        for key in ['source','snapshot','log','timing','object']:check(row[key])
        require(row['exit_code']==0,'supplement exit')
    for key in ['state','final_state','durable_state','driver','final_authentication','freeze_authentication']:
        if key in data:check(data[key])
    row=next(x for x in data['records'] if x['module']==module)
    return dict(module=module,source=row['source'],objects=[row['object']],
        imports=imports(row['source']['path']),provenance=status,
        supplement_packet=pp,supplement_manifest=mm)

require(not OUT.exists(),'new inventory')
p1,c=load_plan('arithmetic-pell-common-unit-cache-plan.json',
    '7081d8c2bc515ea333aadb90fd3d6506643b09c26a5686f1f049c000438a0942')
p2,s=load_plan('arithmetic-pell-strong-divisibility-cache-plan.json',
    '6540842617bdadcad5f9d28b42447ff6b3ed9b3ad28d225b323a808997bd4015')
require(c['boundary_search']==s['boundary_search'] and c['compiler']==s['compiler'],'compatible packages')
mods={x['module']:x for x in c['modules']};overlaps=[]
for row in s['modules']:
    if row['module'] in mods:
        old=mods[row['module']]
        require(old['source']==row['source'] and old['imports']==row['imports'],'source overlap')
        key=lambda z:sorted((Path(x['path']).name,x['sha256'],x['bytes']) for x in z['objects'])
        require(key(old)==key(row),'object overlap')
        overlaps.append(row['module'])
    mods[row['module']]=row
external={x['module']:x for x in c['external']}
for row in s['external']:require(external[row['module']]==row,'external overlap')
for row in [supplement('reviews/arithmetic-pell-common-unit-root-replay.json',
    'c3d7187860435dcbbb97a651aecb47ef0d43ad4e27afcb6f4e308b74479e4fda',
    'reviews/arithmetic-pell-common-unit-root-replay/FILES.json',
    'f2971527011060ca1ce991b7c1c3319e009aed8b21695a24c74f71ef7a6ddf51',
    'DiophantineConsistency.ArithmeticPellCommonUnit','ROOT accepted e072abe66c; independent fresh object'),
    supplement('reviews/arithmetic-pell-strong-divisibility-replay.json',
    'c85cf2c33f09b8aef36719430cffefcc8a1c4d51a19f3aabd8feaae1457dc4c7',
    'reviews/arithmetic-pell-strong-divisibility-author-replay/FILES.json',
    '16d21f1046d0fd0040530a4326dffd7507c2fe62cbcab8f55190b01d5505900e',
    'DiophantineConsistency.ArithmeticPellStrongDivisibility',
    'PROVISIONAL author-validated; ROOT independent acceptance pending')]:
    require(row['module'] not in mods,'new supplement');mods[row['module']]=row
seen=set();active=set();order=[];used=set()
def visit(name):
    if name not in mods:
        require(name in external,'new boundary '+name);used.add(name);return
    if name in seen:return
    require(name not in active,'cycle');active.add(name)
    row=mods[name];check(row['source'])
    require(imports(row['source']['path'])==row['imports'],'header '+name)
    for dep in row['imports']:visit(dep)
    for obj in row['objects']:check(obj)
    active.remove(name);seen.add(name);order.append(name)
direct=['DiophantineConsistency.ArithmeticPellCommonUnit',
    'DiophantineConsistency.ArithmeticPellStrongDivisibility']
for name in direct:visit(name)
boundary=[external[name] for name in sorted(used)];first=[]
for row in boundary:
    check(row['source'])
    for obj in row['artifacts']:
        check(obj);relative=Path(*row['module'].split('.')[:-1])/Path(obj['path']).name
        actual=next((Path(root)/relative for root in c['boundary_search'] if (Path(root)/relative).is_file()),None)
        require(actual is not None,'boundary first missing')
        first.append(dict(module=row['module'],expected=obj,actual=check(dict(obj,path=str(actual)))))
counts=dict(custom=len(order),Foundation=sum(n.startswith('Foundation.') for n in order),
    artifacts=sum(len(mods[n]['objects']) for n in order),external=len(boundary),
    boundary_artifacts=sum(len(row['artifacts']) for row in boundary),boundary_primaries=len(boundary),
    boundary_companions=sum(len(row['artifacts'])-1 for row in boundary),fresh_prerequisites=0)
require(counts==dict(custom=101,Foundation=95,artifacts=386,external=38,
    boundary_artifacts=114,boundary_primaries=38,boundary_companions=76,fresh_prerequisites=0),'scope')
check(c['compiler']);check(record(__file__))
for pin in list(pins.values()):check(pin)
result=dict(status='READ_ONLY_AUTHENTICATED_PLAN_NO_OVERLAY_OR_COMPILER',parents=[p1,p2],
    direct_imports=direct,counts=counts,modules=[mods[n] for n in order],topological_order=order,
    external=boundary,boundary_search=c['boundary_search'],boundary_first_providers=first,
    compiler=c['compiler'],audit=record(__file__),pins=list(pins.values()),observations=observations,
    unique_paths=len(pins),verified_overlap_modules=overlaps,
    provisional_module='DiophantineConsistency.ArithmeticPellStrongDivisibility',
    scope='Proposed ArithmeticPellIntegralSolution plus Checks: actual positive relaxed norm and large-c bound derive ep|n and an integral Pell index m with p|m. StrongDivisibility author provider remains provisional pending ROOT supplement. No compiler, overlay, refresh, final c|m, cubic congruence or full carrier/HA endpoint.')
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(plan=record(OUT),counts=counts,observations=observations,unique_paths=len(pins)),indent=2))
