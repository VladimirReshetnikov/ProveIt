#!/usr/bin/env python3
"""Regenerate the bounded incoming-transition surgery experiment offline."""
from pathlib import Path
import argparse,os,subprocess,json,re
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--radius',type=int,default=20)
p.add_argument('--fuel',type=int,default=128)
a=p.parse_args();assert 1<=a.radius<=30 and 1<=a.fuel<=4096
env=dict(os.environ,ZF_CONTEXT_RADIUS=str(a.radius))
subprocess.run([os.sys.executable,'collect_contexts.py'],cwd=HERE,env=env,check=True)
x=json.loads((HERE/'contexts.json').read_text())
with (HERE/'contexts_search.txt').open('w') as f:
    f.write(f"{x['width']} {len(x['table'])}\n")
    for q,b,w,d,t in x['table']:f.write(f"{q} {b} {w} {-1 if d=='L' else 1} {t}\n")
    f.write(f"{len(x['contexts'])}\n")
    for key,ps in x['contexts'].items():
        q,b=key.split(',');f.write(f'{q} {b} {len(ps)}\n'+'\n'.join(ps)+'\n')
    f.write(f"{len(x['eligible'])}\n")
    for q in x['eligible']:
        ins=x['incoming'][str(q)];f.write(f'{q} {len(ins)}\n'+'\n'.join(f'{p} {b}' for p,b in ins)+'\n')
subprocess.run(['g++','-O3','-std=c++17','confluence_search.cpp','-o','confluence_search'],cwd=HERE,check=True)
controls=subprocess.run([str(HERE/'confluence_search'),'--self-test'],cwd=HERE,capture_output=True,text=True,check=True)
(HERE/'search_controls.txt').write_text(controls.stdout)
result=subprocess.run([str(HERE/'confluence_search'),str(a.fuel)],cwd=HERE,capture_output=True,text=True,check=True)
(HERE/'confluence_result.txt').write_text(result.stdout)
(HERE/'confluence_rejections.tsv').write_text(result.stderr)
match=re.search(r'SUMMARY states=(\d+) tested=(\d+) successful=(\d+) radius=(\d+) fuel=(\d+)',result.stdout)
assert match
summary={k:int(v) for k,v in zip(['eligible_states','tested_edge_alternatives','certified_deletions','radius','step_fuel_per_side'],match.groups())}
summary.update({k:v for k,v in x['summary'].items() if k!='elapsed_seconds'})
summary['scope']='Bounded partial-tape confluence search, not a state lower bound or a full semantic rejection of candidates.'
(HERE/'search_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(result.stdout.strip())
print('Catalog files are reproducible scratch intermediates and need not be archived.')
