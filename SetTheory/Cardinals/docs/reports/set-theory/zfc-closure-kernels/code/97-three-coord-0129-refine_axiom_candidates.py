#!/usr/bin/env python3
"""Run the inherited routing annealer on new AX-order seeds.

Every constraint edit is an exact replacement of the old AX word by the
explicit proposed AX word. No core projection or bootstrap lock is changed.
"""
import sys,json,subprocess,time,concurrent.futures
from pathlib import Path
HERE=Path(__file__).resolve().parent
m=json.loads((HERE/'axiom_search_metadata.json').read_text())
REF=Path(m['reference'])
if not REF.is_absolute():REF=HERE/REF
base=m['base'];oldax=max(base['roots'],key=len)
out=HERE/'refinements';out.mkdir(exist_ok=True)
exe=out/'anneal_canonical_dynamic'
subprocess.run(['g++','-O3','-std=c++17',str(REF/'anneal_canonical_dynamic.cpp'),'-o',str(exe)],check=True)
seconds=float(sys.argv[1])if len(sys.argv)>1 else 30
files=[f for f in sorted((HERE/'candidates').glob('axiom-128-enumerate-*.json'))if f.name!='axiom-128-enumerate-0.json']
if len(sys.argv)>2:files=files[:int(sys.argv[2])]
def run(item):
    i,f=item;d=json.loads(f.read_text());folder=out/f.stem;folder.mkdir(exist_ok=True)
    newax=max(d['roots'],key=len)
    text=[f'{len(d["rules"])} {len(d["roots"])} {len(m["terms"])}']
    text += [f'{len(a)} {w} {i}'for i,(w,a,b)in enumerate(d['rules'])]
    text += d['roots']
    text += [f'{w} {mask}'for w,mask in m['terms'].items()]
    (folder/'grammar.txt').write_text('\n'.join(text)+'\n')
    ct=(REF/'inputs/canonical-constraints.txt').read_text()
    count=ct.split().count(oldax);assert count==1,count
    ct='\n'.join(' '.join(newax if t==oldax else t for t in row.split())for row in ct.splitlines())+'\n'
    (folder/'constraints.txt').write_text(ct)
    resume=[str(len(d['rules']))]+[f'{len(a)} {w}'for w,a,b in d['rules']]
    resume += [str(len(d['routes']))]+[r['word']for r in d['routes']]
    (folder/'resume.txt').write_text('\n'.join(resume)+'\n')
    cmd=[str(exe),str(folder/'grammar.txt'),str(folder/'constraints.txt'),str(folder/'best.json'),str(seconds),str(912014+i),
        '127',str(REF/'inputs/canonical-lock54.txt'),str(folder/'resume.txt'),'6']
    start=time.monotonic()
    with (folder/'search.log').open('w')as log:r=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT)
    status=dict(seed=f.name,exit_code=r.returncode,seconds=time.monotonic()-start)
    if r.returncode==0:
        result=json.loads((folder/'best.json').read_text())
        for key in ['source_replacements','axiom_order','axiom_roles','role_maps']:
            result[key]=d[key]
        result['status']='AX_SYMMETRY_ABSTRACT_GRAMMAR'
        (folder/'best.json').write_text(json.dumps(result,indent=2)+'\n')
        status.update(grammar=result['rules_count'],iterations=result['iterations'],properties=result['properties'])
    print(json.dumps(status),flush=True)
    return status
with concurrent.futures.ThreadPoolExecutor(max_workers=2)as pool:results=list(pool.map(run,enumerate(files)))
(out/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
