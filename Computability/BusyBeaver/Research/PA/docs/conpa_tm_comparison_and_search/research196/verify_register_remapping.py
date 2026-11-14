#!/usr/bin/env python3
"""Reproduce the three register-retargeting contract and startup experiments.

Supply --core and --source when moving this file outside the research checkout.
This executable check is not a Lean proof and claims no state reduction.
"""
import argparse,importlib.util,json,random,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
DEFAULT=HERE.parent/'support'
ap=argparse.ArgumentParser();ap.add_argument('--core',type=Path,default=DEFAULT/'work/optimize196/core.py');ap.add_argument('--source',type=Path,default=DEFAULT/'sources/BusyBeaver');ap.add_argument('--output',type=Path,default=HERE/'register_permutations/remap_validation.json');ap.add_argument('--startup-limit',type=int,default=1000000);args=ap.parse_args()
sp=importlib.util.spec_from_file_location('reference_core',args.core);c=importlib.util.module_from_spec(sp);sp.loader.exec_module(c);c.ROOT=args.source
ENGINE={0,1,2,3,4,5,6,9,10,15,16,22,23,24,25,32,33,34,35,36,40,48,49,51,54,55,60,64,66,74,75,94,97,113,198,302}
old,labels=c.machine();sites,ins=c.program()
def contracts(physical):
    out=[]
    for i,code in enumerate(ins):
        st=c.frame(sites[i][0])
        if code[0]=='inc':
            _,r,n=code;out.append((i,None,st,c.canonical(c.frame(sites[n][0],0,('x','inc',physical[r])))))
        elif code[0]=='dec':
            _,r,z,p=code
            out.append((i,(physical[r],True),st,c.canonical(c.frame(sites[z][0]))))
            out.append((i,(physical[r],False),st,c.canonical(c.frame(sites[p][0],1,('x','dec',physical[r])))))
        elif code[0]=='jump':out.append((i,None,st,c.canonical(c.frame(sites[code[1]][0]))))
        else:out.append((i,None,st,None))
    return out
file=[0]*9+[1]*26;file[6]=2
right=[1]+[0]*47+[1]+sum(([0]+[1]*(v+1) for v in file),[])
expected={-1}|{i for i,b in enumerate(right) if b}
def startup(rows):
    ones=set();head=0;q=labels[0]
    for step in range(args.startup_limit+1):
        if q==84 and len(ones)==len(expected) and {x-head for x in ones}==expected:
            return {'ok':True,'steps':step,'head':head,'state':q,'physical_file':file,'gap':48}
        if step==args.startup_limit:break
        b=int(head in ones)
        if (q,b) not in rows:return {'ok':False,'halted':True,'steps':step,'state':q}
        w,d,q=rows[q,b]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=1 if d else -1
    return {'ok':False,'steps_limit':args.startup_limit,'state':q,'head':head,'ones':len(ones)}
result={'status':'No state reduction claimed','baseline_physical':c.PHYSICAL,'retargeted_entry_rows':[[q,b,*a]for(q,b),a in sorted(old.items()) if q not in ENGINE and a[2] in c.SK],'baseline_startup':startup(old),'experiments':[]}
perms=[[6,0,2,4,3,7,8,5,1],[6,2,0,3,4,7,8,5,1],[6,8,7,5,4,3,2,1,0]]
for p in perms:
    mapping={c.SK[c.PHYSICAL[i]]:c.SK[p[i]] for i in range(9)}
    rows={k:(w,d,mapping.get(n,n) if k[0] not in ENGINE else n)for k,(w,d,n)in old.items()}
    e={'physical':p,'working_states':len(rows)//2,'contracts':c.validate(rows,contracts(p)),'startup':startup(rows)}
    result['experiments'].append(e);print(json.dumps(e),flush=True)
args.output.parent.mkdir(exist_ok=True,parents=True);args.output.write_text(json.dumps(result,indent=2))
