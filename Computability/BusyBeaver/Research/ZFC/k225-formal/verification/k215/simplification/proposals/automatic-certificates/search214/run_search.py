#!/usr/bin/env python3
"""Reproduce predecessor-specific elimination searches on pinned K215 alternatives."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess,time
HERE=Path(__file__).resolve().parent
TABLES={
 'primary':'k215.native.tm',
 'commands120':'alternatives/commands120/k215.native.tm',
 'composed':'alternatives/composed/k215.native.tm',
 'reencoded':'alternatives/reencoded/machine/k215.native.tm',
 'zero_spare':'alternatives/zero-spare/machine/z215.native.tm',
 'zero_spare_z201':'alternatives/zero-spare-z201/primary/z201.native.tm',
 'zero_spare_transfer':'alternatives/zero-spare-transfer/primary/machine/zero_spare_transfer215.native.tm',
 'mp_first_transfer':'alternatives/mp-first-transfer/machine/t215.native.tm',
 'rho6_210':'alternatives/rho6/machines/rho6_210/candidate.native.tm',
 'rho6_120':'alternatives/rho6/machines/rho6_120/candidate.native.tm',
 'zero_spare_mp_first':'alternatives/zero-spare-mp-first/machine/candidate.native.tm',
 'direct_transfer':'alternatives/direct-transfer/machine/st215.native.tm',
 'conditional_marker':'alternatives/conditional-marker/machine/marker215.native.tm',
 'rebalanced':'alternatives/rebalanced/machine/k215r.native.tm',
 'dr215':'alternatives/dr215/DR215/machine/dr215.native.tm',
 'forced_transfer':'alternatives/forced-transfer/forced215/machine.native.tm',
 'zero_credit':'alternatives/zero-credit/machine/zc215.native.tm',
 'gc215':'alternatives/gc215/machine/gc215.native.tm',
 'context_returns':'alternatives/context-returns/machine/k215-context.native.tm',
 'context_shallow':'alternatives/context-returns/machine/k215-shallow.native.tm',
 'gc_zc215':'alternatives/gc-zc215/hybrid215/machine.native.tm',
}
p=argparse.ArgumentParser();p.add_argument('--source',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--radius',type=int,default=5);p.add_argument('--cap',type=int,default=96);p.add_argument('--names',nargs='*');p.add_argument('--reentry',action='store_true');a=p.parse_args()
a.out.mkdir(parents=True,exist_ok=True)
sp=importlib.util.spec_from_file_location('inv',HERE/'invariant.py');inv=importlib.util.module_from_spec(sp);sp.loader.exec_module(inv)
results=[]
for name,rel in TABLES.items():
    if a.names and name not in a.names: continue
    path=a.source/rel;raw=path.read_bytes();T,start=inv.read(path)
    states=sorted({q for q,b in T});assert len(states)==215
    halt={v[2] for v in T.values()}-set(states);assert len(halt)==1
    x=inv.analyze(T,start,a.radius,False);inp=a.out/(name+'.input')
    with inp.open('w') as f:
        print(a.radius,start,halt.pop(),len(states),file=f)
        for q in states: print(q,*T[q,0],*T[q,1],len(x['masks'][q]),*x['masks'][q],file=f)
    out=a.out/(name+'.json')
    with out.open('w') as f: subprocess.run([str(HERE/'contextual_eliminate'),str(inp),str(a.cap),str(int(a.reentry))],stdout=f,check=True)
    result=json.loads(out.read_text());result['input']={'name':name,'relative_path':rel,'table_sha256':hashlib.sha256(raw).hexdigest(),'input_sha256':hashlib.sha256(inp.read_bytes()).hexdigest(),'invariant_configs':x['configs'],'unreachable_rows':x['unreachable_rows']}
    out.write_text(json.dumps(result,indent=2)+'\n');inp.unlink()
    item={'name':name,**result['input'],**result['summary'],'near':[{'deleted':s['deleted'],'passed':s['passed'],'total':s['total']} for s in result['states'] if s['passed'] and s['passed']>=s['total']-1]}
    results.append(item);print(json.dumps(item),flush=True)
(a.out/'summary.json').write_text(json.dumps({'radius':a.radius,'cap':a.cap,'same_row_reentry':a.reentry,'search_sha256':hashlib.sha256((HERE/'contextual_eliminate.cpp').read_bytes()).hexdigest(),'results':results},indent=2)+'\n')
