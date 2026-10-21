#!/usr/bin/env python3
from pathlib import Path
import argparse,json,hashlib,importlib.util
p=argparse.ArgumentParser();p.add_argument('table');p.add_argument('output');p.add_argument('--radius',type=int,default=5);p.add_argument('--blank',action='store_true');a=p.parse_args()
module=Path(__file__).parent/'invariant.py'
sp=importlib.util.spec_from_file_location('inv',module);inv=importlib.util.module_from_spec(sp);sp.loader.exec_module(inv)
T,start=inv.read(a.table);x=inv.analyze(T,start,a.radius,a.blank)
states=sorted({q for q,b in T});halt=set(z for w,d,z in T.values())-set(states);assert len(halt)==1
out=Path(a.output)
with out.open('w') as f:
    print(a.radius,start,halt.pop(),len(states),file=f)
    for q in states: print(q,*T[q,0],*T[q,1],len(x['masks'][q]),*x['masks'][q],file=f)
metadata={'table':str(Path(a.table).resolve()),'table_sha256':hashlib.sha256(Path(a.table).read_bytes()).hexdigest(),'radius':a.radius,'blank_window':a.blank,'configs':x['configs'],'unreachable_rows':x['unreachable_rows'],'input_sha256':hashlib.sha256(out.read_bytes()).hexdigest()}
out.with_suffix('.metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
print(json.dumps(metadata))
