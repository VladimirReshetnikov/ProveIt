#!/usr/bin/env python3
from itertools import permutations,combinations_with_replacement
from pathlib import Path
import subprocess
import sys
import json

root=Path(__file__).resolve().parent
def image(mask,p):return sum(((mask>>i)&1)<<p[i] for i in range(3))
profiles=[]
for J in (1,3,7):
    perms=[p for p in permutations(range(3)) if image(J,p)==J]
    cores=set()
    for a,b in combinations_with_replacement(range(8),2):
        cores.add(min(tuple(sorted((image(a,p),image(b,p)))) for p in perms))
    profiles.extend((J,a,b) for a,b in sorted(cores))
print('Rooted core profile counts:',{J:sum(p[0]==J for p in profiles) for J in (1,3,7)},flush=True)
records=[]
for J,a,b in profiles:
    path=root/f'core_schur_{J}_{a}_{b}.json'
    if not path.exists():
        subprocess.run([sys.executable,str(root/'build_core_schur_certificate.py'),str(J),str(a),str(b)],check=True,stdout=subprocess.DEVNULL)
    v=json.loads(path.read_text());records.append(v)
    print(J,a,b,'bases',v['basis_profiles_checked'],'negative',bool(v['negative']),'seconds',v['seconds'],flush=True)
    if v['negative']:break
out={'scope':'Exact rooted-core Schur cone certificate progress','total_profiles':len(profiles),'completed_profiles':len(records),'all_profile_list':profiles,'negative':next((x for x in records if x['negative']),None),'coefficient_entries_checked':sum(sum(y['terms'] for y in x['records']) for x in records),'basis_instances':sum(len(x['records']) for x in records),'records':records}
(root/'core_schur_manifest.json').write_text(json.dumps(out,indent=2)+'\n')
print('FINISHED',json.dumps({k:v for k,v in out.items() if k not in ('records','all_profile_list')},default=str),flush=True)
