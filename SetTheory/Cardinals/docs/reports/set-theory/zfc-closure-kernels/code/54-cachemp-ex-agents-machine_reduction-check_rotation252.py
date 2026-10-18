#!/usr/bin/env python3
"""Complete conditional affine instruction check for supplied finite decoder DAG.

The executor uses unchanged original register-box contracts. This diagnostic
does not itself prove its implementation or infer a ZFC endpoint.
"""
from pathlib import Path
import json,importlib.util,sys,types,time,argparse
from collections import Counter
import rotation_search252 as r

sys.modules['cost_search']=types.SimpleNamespace()
spec=importlib.util.spec_from_file_location('rotation252_strict',r.HERE/'27-variant-experiments-machine_search-grammar_search-strict_affine.py');strict=importlib.util.module_from_spec(spec);spec.loader.exec_module(strict)
spec=importlib.util.spec_from_file_location('rotation252_audit',r.HERE/'candidate252_independent_audit.py');audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)

class Tracking(dict):
    def __init__(self,x):super().__init__(x);self.used=set()
    def __getitem__(self,key):self.used.add(key);return super().__getitem__(key)

def cases(nodes,root):
    todo=[(('N',root),'')]
    while todo:
        e,p=todo.pop()
        if e[0]=='N':
            a,b=nodes[e[1]];todo.extend([(b,p+'1'),(a,p+'0')]);continue
        op='C'+e[0];arg=e[1] if len(e)>1 else None
        for zero in ((True,False) if op=='CD' else (None,)):
            physical=r.NEWPHYS[arg] if op in ('CD','CI') else arg
            branch=(physical,zero) if op=='CD' else None
            targetpc=audit.successor(p,op,arg,zero)
            effect=('inc',physical) if op=='CI' else ('dec',physical) if op=='CD' and not zero else None
            right=[('b',int(c)) for c in targetpc] if targetpc is not None else []
            right += [('r',0,1,(41 if targetpc is None else 40)-len(targetpc or '')),('b',1),('box',('plain',effect))]
            yield p,op,arg,zero,branch,strict.canon([('b',1)],right)

def run(table,nodes,root,stop=False):
    total=0;failures=[];rules=Counter();seen=set();began=time.monotonic()
    for p,op,arg,z,branch,target in cases(nodes,root):
        t=Tracking(table)
        try:
            rr,literal=strict.run(t,p,branch,target,halt=op=='CH',fuel=1000);assert literal>0;rules.update(rr)
        except (KeyError,AssertionError) as ex:
            failures.append({'case':total,'path':p,'op':op,'arg':arg,'zero':z,'error':str(ex)})
        seen.update(t.used);total+=1
        if failures and stop:break
    return {'cases_checked':total,'failures':failures,'used_rows':sorted(seen,key=lambda x:(int(x[0]),x[1])),'rule_counts':rules,'elapsed_seconds':time.monotonic()-began}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('dag',type=Path);ap.add_argument('--table',type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--physical',help='Comma-separated logical-to-physical register permutation; otherwise use DAG metadata.');args=ap.parse_args()
    if not __debug__:ap.error('Assertions must remain enabled; do not use Python -O.')
    d=json.loads(args.dag.read_text());ns={int(k):tuple(map(tuple,v)) for k,v in d['nodes'].items()};root=d['root']
    physical=list(map(int,args.physical.split(','))) if args.physical else d.get('logical_to_physical',d.get('physical'))
    if physical is not None:
        assert sorted(physical)==list(range(9))
        r.NEWPHYS=tuple(physical)
    if args.table:
        t={}
        for line in args.table.read_text().splitlines():
            if not line or line.startswith('#'):continue
            q,b,w,di,ta=line.split();t[q,int(b)]=int(w),di,ta
    else:t=r.emit(ns,root)
    result=run(t,ns,root)
    result['physical_map']=list(r.NEWPHYS)
    result['max_leaf_depth']=max(len(item[0]) for item in cases(ns,root))
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('used_rows','rule_counts')},indent=2))

if __name__=='__main__':main()
