"""Read-only source/provider audit; writes only this new plan and manifest.
No compiler, overlay, symlinks, source changes or Git mutation.
"""
from pathlib import Path
import copy, hashlib, json, re, shutil
R = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = R / 'Computability/DiophantineConsistency'
H = Path(__file__).resolve().parent
pins, observations = {}, 0
def rec(p):
    p = Path(p); b = p.read_bytes()
    return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def check(x):
    global observations
    a = rec(x['path']); assert a['sha256']==x['sha256'], (x,a)
    if 'bytes' in x: assert a['bytes']==x['bytes']
    pins[a['path']]=a; observations+=1
    return a
def load(p,sha):
    check(dict(path=str(p),sha256=sha)); return json.loads(Path(p).read_text())
def imports(p):
    s=Path(p).read_text(); out=[];i=depth=0
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
    assert depth==0
    return list(dict.fromkeys(['Init']+[n for line in re.findall(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',''.join(out),re.M) for n in line.split()]))
basep=D/'research/c222-site215-plan-20261027/cache-plan.json'
base=load(basep,'2db2db74059105fba7f58dacc502274b3fdb4dd0605dafa8a37bdd5bc7b35e88')
for x in base['authenticated_pins']:check(x)
rootp=D/'reviews/arithmetic-register-boxes215-root-replay.json'
root=load(rootp,'db5dc321c4511cfe6c8388c1e51c16a54caf61f24b7c8aa4a07cc353ad9f7c8f')
mfp=D/'reviews/arithmetic-register-boxes215-root-replay/FILES.json'
mf=load(mfp,'a068d6dedfafe2ac8f1368ae5a7d519cf067bb7e2a55ee8d857990f2db2a33ec')
for x in mf:check(x)
assert root['status']=='PASS' and root['provider']=='/tmp/register-boxes215-root-hzd4elpy/lib'
mods={m['module']:copy.deepcopy(m) for m in base['modules']}
for row in root['records']:
    if row['module'].endswith('Checks'):continue
    assert row['exit_code']==0 and row['author_object_and_full_log_equal']
    for k in ['source','snapshot','object','log','timing']:check(row[k])
    n=row['module']; previous=mods.get(n)
    mods[n]=dict(module=n,source=row['source'],actual_imports=imports(row['source']['path']),
        objects=[row['object']],parent=rec(rootp),provider='Accepted independent ROOT triple',
        historical_provenance=row,previous_plan_entry=previous)
direct=['DiophantineConsistency.ArithmeticRegisterBoxes215']
external={x['module']:copy.deepcopy(x) for x in base['external']}
seen,active,used,order=set(),set(),set(),[]
def visit(n):
    if n not in mods:
        assert n in external, ('unknown boundary',n);used.add(n);return
    if n in seen:return
    assert n not in active;active.add(n);m=mods[n]
    check(m['source']); actual=imports(m['source']['path'])
    assert actual==m['actual_imports'],n
    assert not m.get('refresh',False),('unresolved refresh',n)
    for d in actual:visit(d)
    for x in m['objects']:check(x)
    active.remove(n);seen.add(n);order.append(n)
for n in direct:visit(n)
providers=[]
for n in order:
    for x in mods[n]['objects']:providers.append(dict(module=n,provider=check(x),kind='selected cached artifact'))
bound=[external[n] for n in sorted(used)]
for m in bound:
    if 'source' in m:check(m['source'])
    for x in [m['object']]+m['companion_observations']:
        check(x);suffix=''.join(Path(x['path']).suffixes)
        rel=Path(*m['module'].split('.')).with_suffix(suffix)
        first=next((Path(p)/rel for p in base['package_paths'] if (Path(p)/rel).is_file()),None)
        assert first is not None and rec(first)['sha256']==x['sha256']
        providers.append(dict(module=m['module'],provider=check(rec(first)),kind='actual first package artifact'))
counts=dict(cached_custom=len(order),Foundation=sum(n.startswith('Foundation.') for n in seen),
    cached_artifacts=sum(len(mods[n]['objects']) for n in order),boundary_primaries=len(bound),
    boundary_companions=sum(len(m['companion_observations']) for m in bound),
    selected_first_artifact_providers=len(providers),refresh=0,new_leaves=2)
assert counts==dict(cached_custom=148,Foundation=95,cached_artifacts=433,
    boundary_primaries=41,boundary_companions=123,selected_first_artifact_providers=597,refresh=0,new_leaves=2),counts
route=[]
for stem in ['KRuntimeCore','KHome','KHomeReady','KSim','KSites215','KBoot215','ControlCatalogue']:
    route.append(check(rec(R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'/f'{stem}.lean')))
check(base['compiler']);check(rec(H/'PROPOSAL.md'));check(rec(__file__))
for x in list(pins.values()):check(x)
assert shutil.disk_usage('/tmp').free>=512*1024**2
result=dict(status='READ_ONLY_NO_COMPILER_OR_OVERLAY',direct_imports=direct,counts=counts,
    modules=[mods[n] for n in order],topological_order=order,external=bound,first_providers=providers,
    package_paths=base['package_paths'],compiler=base['compiler'],base=rec(basep),
    accepted_box_root=rec(rootp),accepted_box_manifest=rec(mfp),route_sources_not_new_imports=route,
    proposal=rec(H/'PROPOSAL.md'),planner=rec(__file__),observations=observations,
    authenticated_pins=list(pins.values()))
(H/'cache-plan.json').write_text(json.dumps(result,indent=2)+'\n')
(H/'FILES.json').write_text(json.dumps([rec(H/n) for n in ['PROPOSAL.md','planner.py','cache-plan.json']],indent=2)+'\n')
print(json.dumps(dict(counts=counts,observations=observations,unique_paths=len(pins),
    plan=rec(H/'cache-plan.json'),manifest=rec(H/'FILES.json'))))
