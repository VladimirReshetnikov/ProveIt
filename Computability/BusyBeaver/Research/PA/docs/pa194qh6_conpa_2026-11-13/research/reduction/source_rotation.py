#!/usr/bin/env python3
"""Reject a source-preserving outer reassociation plus shortened scanner."""
from pathlib import Path
import argparse,sys,json,tempfile,hashlib
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--package-root',type=Path,default=HERE.parents[1]);ap.add_argument('--output',type=Path);a=ap.parse_args()
sys.path.insert(0,str(a.package_root/'construction'))
import compiler as c
import support as b
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
ns={k:tup(v)for k,v in json.loads((HERE/'inputs/primary.nodes.json').read_text()).items()}
raw0=b.read_table(HERE/'inputs/primary.raw201.native.tm');c.machine=lambda:(raw0,[]);c.raw_nodes=lambda:ns
inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
g=c.read_grammar(HERE/'inputs/primary.grammar.json');sites0,ins0,cs0=c.source(g)
raw,_,_=c.build(g);rows,_=b.apply_folds(raw,json.loads((HERE/'inputs/primary.folds.json').read_text()))
assert hashlib.sha256(b.table_text(rows).encode()).hexdigest()=='e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'
baseline=c.validate(rows,cs0);assert baseline['ok'] and len(cs0)==4780
ns['node172']=('node7',(('node20','node170'),'node23'));sites,ins,cs=c.source(g);assert ins==ins0
rows.update({(84,0):(0,True,68),(84,1):(1,True,310),(310,0):(0,True,53),(53,0):(0,True,69),(53,1):(1,True,214)})
child={k:(w,d,75 if n==34 else n)for k,(w,d,n)in rows.items()if k[0]!=34}
failed=[]
for co in cs:
    if c.run(child,co,fuel=1024)is None:failed.append(dict(site=co[0],branch=co[1],path=''.join(map(str,sites[co[0]][0]))))
assert len(child)==386 and len(failed)==52
result=dict(experimental_states=193,accepted=False,source_sites=len(sites),source_graph_unchanged=True,baseline=baseline,failed_contracts=len(failed),fuel_bound=1024,failures=failed)
out=a.output or Path(tempfile.mkdtemp(prefix='qh6-scanner-'));out.mkdir(parents=True,exist_ok=True)
(out/'source_rotation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
