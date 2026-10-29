"""Read-only current-hierarchy prerequisite inventory; no compiler or overlay."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import tomllib

R = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = R / 'Computability/DiophantineConsistency'
pins = {}
observations = 0


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def record(path):
    path = Path(path)
    path = path if path.is_absolute() else R / path
    raw = path.read_bytes()
    return dict(path=str(path), sha256=hashlib.sha256(raw).hexdigest(), bytes=len(raw))


def check(expected):
    global observations
    actual = record(expected['path'])
    need(actual['sha256'] == expected['sha256'], 'hash: ' + actual['path'])
    need('bytes' not in expected or actual['bytes'] == expected['bytes'], 'size')
    pins[actual['path']] = actual
    observations += 1
    return actual


def load(relative, sha):
    pin = check(dict(path=str(D / relative), sha256=sha))
    return pin, json.loads(Path(pin['path']).read_text())


def imports(path):
    text = Path(path).read_text()
    out = []
    index = depth = 0
    while index < len(text):
        pair = text[index:index + 2]
        if depth:
            if pair == '/-':
                depth += 1
                index += 2
            elif pair == '-/':
                depth -= 1
                index += 2
            else:
                out.append('\n' if text[index] == '\n' else ' ')
                index += 1
        elif pair == '/-':
            depth = 1
            index += 2
        elif pair == '--':
            while index < len(text) and text[index] != '\n':
                index += 1
        else:
            out.append(text[index])
            index += 1
    need(depth == 0, 'balanced comments')
    text = ''.join(out)
    result = [] if re.search(r'^\s*prelude\s*$', text, re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', text, re.M):
        result.extend(line.split())
    return list(dict.fromkeys(result))


output=D/'research/arithmetic-current-hierarchy2011-cache-plan.json'
need(not output.exists(),'fresh plan')
need(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
parent_pin,parent=load('reviews/foundation-ha-consistency-normalization-replay/inputs.json','2eec550befdc20566c45943b4539b536f6148c3a6990e38245773d84de83d99c')
mp,mf=load('reviews/foundation-ha-consistency-normalization-replay/FILES.json','fca8110bfa4838b476f9da53e10b10f9bd25682e8c4427e3608e2ccc4420b268')
for row in mf['files']:check(dict(row,path=str(Path(mp['path']).parent/row['path'])))
pp,peer=load('reviews/foundation-ha-consistency-normalization-peer-replay.json','7f34393a2315a3965b32f278ef38af79ff8b100ff73f762493247b3fcb79043b')
need(peer['status']=='PASS','accepted historical independent packet')
pm,pmf=load('reviews/foundation-ha-consistency-normalization-peer-replay/FILES.json','3f7b2fa58adec39a599abc0d095c94b94b9710cb9f69dc21839638885e8da3e3')
for row in pmf['files']:check(dict(row,path=str(Path(pm['path']).parent/row['path'])))
legacy={m['module']:m for m in parent['modules']}
external={m['module']:m for m in parent['external']}
lake=check(record(R/'lakefile.toml'))
roots={x['name']:R/x.get('srcDir','.')for x in tomllib.loads(Path(lake['path']).read_text())['lean_lib']}
roots['Foundation']=Path('/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation')
modules={};order=[];active=set();used=set()
def visit(n):
 if n in modules:return
 prefix=n.split('.')[0]
 if prefix not in roots:
  need(n in external,'known explicit boundary '+n);used.add(n);return
 need(n not in active,'acyclic current headers '+n);active.add(n)
 path=roots[prefix]/Path(*n.split('.')).with_suffix('.lean')
 source=check(record(path));deps=imports(path)
 for c in deps:visit(c)
 active.remove(n);modules[n]=dict(module=n,source=source,imports=deps);order.append(n)
direct=['DiophantineConsistency.FoundationHACurrentNoZero2011','DiophantineConsistency.FoundationZFCConsistencyNat']
for n in direct:visit(n)
changed=[];new=[];affected=[];reused=[]
for n in order:
 m=modules[n];old=legacy.get(n)
 if old is None:new.append(n)
 elif m['source']['sha256']!=old['source_sha256']or m['imports']!=old['imports']:changed.append(n)
 causes=[d for d in m['imports']if d in affected]
 if n in new or n in changed or causes:
  affected.append(n);m.update(mode='FRESH_CURRENT_SOURCE_REQUIRED',changed=n in changed,new=n in new,affected_dependencies=causes,objects=[])
  if old is not None:m['historical_excluded_record']=old
 else:
  reused.append(n);need(old is not None,'old record');m.update(mode='REUSE_UNCHANGED_SOURCE_AND_ALL_DEPENDENCIES',objects=old['objects'],historical_record=old)
  for obj in m['objects']:check(obj)
need(len(order)==430 and len(reused)==390 and len(affected)==40,'current closure partition')
need(len(changed)==13 and len(new)==1 and new==['PAHF.PACore'],'exact direct changes')
need(sum(n.startswith('Foundation.')for n in order)==139,'Foundation count')
need(not any(n.startswith('Foundation.')for n in affected),'no Foundation refresh')
need(used==set(external)and len(used)==57,'complete boundary')
need(len({m['source']['path']for m in modules.values()})==len(modules),'source path uniqueness')
search=parent['lean_path'].split(':');boundary_search=search[1:]
need(all('/.lake/packages/'in q or q=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'for q in boundary_search),'explicit package/toolchain boundary')
providers=[]
for n in reused:
 m=modules[n]
 for obj in m['objects']:
  rel=str(Path(*n.split('.')[:-1])/Path(obj['path']).name)
  first=next((Path(root)/rel for root in search if(Path(root)/rel).is_file()),None)
  need(first is not None,'cached provider '+n)
  providers.append(dict(module=n,relative=rel,expected=obj,actual=check(dict(obj,path=str(first)))))
for n in sorted(used):
 m=external[n];check(m['source'])
 for obj in m['objects']:
  check(obj);rel=str(Path(*n.split('.')[:-1])/Path(obj['path']).name)
  first=next((Path(root)/rel for root in boundary_search if(Path(root)/rel).is_file()),None)
  need(first is not None,'boundary provider '+n)
  providers.append(dict(module=n,relative=rel,expected=obj,actual=check(dict(obj,path=str(first)))))
need(len({x['relative']for x in providers})==len(providers),'unique providers')
compiler=check(parent['compiler'])
counts=dict(prerequisite_modules=len(order),cached_modules=len(reused),fresh_prerequisites=len(affected),Foundation=139,cached_artifacts=sum(len(modules[n]['objects'])for n in reused),boundary_primaries=len(used),boundary_artifacts=sum(len(external[n]['objects'])for n in used),cached_first_providers=len(providers),new_target_leaves=2)
counts['boundary_companions']=counts['boundary_artifacts']-counts['boundary_primaries']
proposal=check(record(D/'research/arithmetic-current-hierarchy2011-proposal.md'));auditor=check(record(__file__))
# The candidate upstream endpoint build is deliberately not a selected provider.
candidate=check(dict(path='/tmp/hacurrent-client-audit-20261029/records.json',sha256='bd6416cf49c103faf6a5b5397d2ca88f732f526241b4ea7758113bc219fad255'))
candidate_modules={r['module']for r in json.loads(Path(candidate['path']).read_text())if r['status']==0}
need(not candidate_modules.intersection(affected),'candidate removes no needed refresh')
for x in list(pins.values()):check(x)
result=dict(status='READ_ONLY_REFRESH_PLAN_REQUIRES_INDEPENDENT_APPROVAL_NO_OVERLAY_OR_COMPILER',scope='Exact Foundation hierarchy certificates for both named endpoint sentences and their literal biconditional; no PRA calculus or conservation claim.',parent=parent_pin,parent_manifest=mp,historical_peer=pp,historical_peer_manifest=pm,proposal=proposal,auditor=auditor,direct_imports=direct,counts=counts,modules=[modules[n]for n in order],topological_order=order,reused_modules=reused,changed_modules=changed,new_modules=new,fresh_prerequisites=affected,external=[external[n]for n in sorted(used)],compiler=compiler,boundary_search=boundary_search,audited_existing_search=search,first_providers=providers,candidate_not_selected=candidate,prospective_build_policy='Authenticate 390 unchanged modules and their entire current dependencies; omit all 40 affected old objects and build those 40 current sources in topological order, then two new leaves. No Foundation refresh or shared outputs. Additional compiler authorization and full input/driver reads required.',pins=list(pins.values()),observations=observations,unique_paths=len(pins))
output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(plan=record(output),counts=counts,observations=observations,unique_paths=len(pins)),indent=2))
