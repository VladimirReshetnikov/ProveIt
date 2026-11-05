#!/usr/bin/env python3
"""Recheck partial header survey, provider choices and historic Matrix evidence."""
import collections
import hashlib
import json
import os
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
root=next(p for p in here.parents if (p/'lakefile.toml').is_file())
prior=root/'Computability/DiophantineConsistency/reviews/current14-matrix-import-order-probe/result.json'
audit=root/'Computability/DiophantineConsistency/reviews/current14-matrix-import-order-probe-independent-v1/result.json'
inputs={here/'direct-result.json':'8fc9a8a1978eecd0ddfb58928a5f2aa113a0a757dd4e7b63d1aeb120df76f787',
        here/'header-result.json':'7c5751dfd7002b3425e71f462f8058078ee0911e5f4ecbcd1e66871a4832b9fe',
        here/'header-observation.json':'b9608a987e17b93f18e226c15457449a7a031eb71dfcbab2189cda109b06054e',
        prior:'914339a67b5a866cb577de5e12b79a0212cb725c4307ae87c699e539efefe20d',
        audit:'3634e96a7e26d21f827746645408e34e9dc1f7147299c7f825933c867f7a27ae'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,msg):
    if not ok:raise RuntimeError(msg)
for p,h in inputs.items():require(p.is_file() and sha(p)==h,'input mismatch '+str(p))
d=json.loads((here/'direct-result.json').read_text());h=json.loads((here/'header-result.json').read_text())
o=json.loads((here/'header-observation.json').read_text());old=json.loads(prior.read_text());a=json.loads(audit.read_text())
require(d['status']=='PASS_DIRECT_DEPS_NOT_IMPORT_CHECK' and d['exit']==0,'direct probe failure')
require(h['status']=='PARTIAL_COMPILED_HEADERS' and len(h['modules'])==64 and len(h['frontier'])==199,'unexpected partial header scope')
require(o['exit']==0 and o['stop_reason'] is None and o['inputs_stable'] and o['result_sha256']==inputs[here/'header-result.json'],'header process mismatch')
require(a['status']=='PASS_CAPTURED_EVIDENCE' and a['lean_exits']==[1,1],'historic order probe not audited')
require(set(h['seeds'])==set(d['selected'])-{'Init'},'seed set mismatch')
for name in h['seeds']:
    require(h['modules'][name]['path']==d['selected'][name]['path'],'direct/header selection mismatch '+name)
matches=0
for path,previous in old['provider_guards'].items():
    current=d['guards_after'].get(path,'MISSING')
    require(current!='MISSING','old guard not included '+path)
    if previous is None:require(current is None,'old absent guard now present '+path)
    else:require(current is not None and current['sha256']==previous['sha256'] and current['realpath']==previous['realpath'],'historic Matrix artifact changed '+path)
    matches+=1

roots=[Path(x['path']) for x in h['roots']]
suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean',
          '.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def observe():
    out={}
    for name in sorted(h['modules']):
        stem=Path(*name.split('.'))
        for root_path in roots:
            for suffix in suffixes:
                p=root_path/(str(stem)+suffix)
                if os.path.lexists(p):
                    require(p.is_file(),'broken alternate candidate '+str(p));st=p.stat()
                    out[str(p)]={'realpath':str(p.resolve()),'sha256':sha(p),'size':st.st_size,'mtime_ns':st.st_mtime_ns}
                else:out[str(p)]=None
    return out
before=observe();collisions=[]
for name,rec in h['modules'].items():
    require(rec['path'] in before and before[rec['path']] is not None,'selected object absent '+name)
    inventory=h['artifacts'][rec['path']]
    require(before[rec['path']]['sha256']==inventory['sha256'] and
            before[rec['path']]['realpath']==inventory['metadata']['realpath'],'selected inventory drift '+name)
    stem=str(Path(*name.split('.')))+'.olean'
    choices=[{'path':str(r/stem),**before[str(r/stem)]} for r in roots if before[str(r/stem)] is not None]
    if len(choices)>1:collisions.append({'module':name,'choices':choices,
        'different_hashes':len({x['sha256'] for x in choices})>1})

targets={'Foundation.Vorspiel.Matrix','Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber'}
new_seeds=sorted(set(h['seeds'])-targets);reach={}
for seed in new_seeds:
    queue=collections.deque([(seed,[seed])]);seen={seed};found=[];unknown=[]
    while queue:
        name,path=queue.popleft()
        if name in targets:found.append(path);continue
        if name not in h['modules']:
            unknown.append(name);continue
        for dep in h['modules'][name]['imports']:
            if dep not in seen:seen.add(dep);queue.append((dep,path+[dep]))
    reach[seed]={'known_paths_to_matrix':found,'unexpanded_reachable':sorted(set(unknown)),
                 'closure_complete_without_target':not found and not unknown}
after=observe();require(before==after,'provider candidates changed during analysis')
for p,digest in inputs.items():require(sha(p)==digest,'input changed '+str(p))
result={'status':'PASS_PARTIAL_ANALYSIS','visited_modules':len(h['modules']),'frontier_modules':len(h['frontier']),
        'direct_seed_count':len(new_seeds),'historic_matrix_guards_matched':matches,
        'direct_collisions':d['collisions'],'visited_object_collisions':sorted(collisions,key=lambda x:x['module']),
        'reachability':reach,'provider_guards_before':before,'provider_guards_after':after,
        'matrix_seed_headers':{n:h['modules'][n]['imports'] for n in sorted(targets)},
        'scope':'Point-in-time direct resolution and partial serialized-header reachability only; no combined import, complete closure, dynamic import, or project build.'}
print(json.dumps(result,indent=2,sort_keys=True))
