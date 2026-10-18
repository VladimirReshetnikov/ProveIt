#!/usr/bin/env python3
"""Uniform-fold diagnostic for the successful-MP cache continuation variant.

Every candidate retains all 55 attributed register box support rows. Each
survivor receives every changed-program conditional affine case. Passing this
check does not establish its blank-tape initialization or a formal endpoint.
"""
from pathlib import Path
from collections import defaultdict,Counter
import argparse,json,time,hashlib
import rotation_search252 as r
import check_rotation252 as c

def read_table(path):
    table={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();table[q,int(b)]=int(w),d,t
    return table

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--name',default='mp-cache252');ap.add_argument('--output',type=Path);ap.add_argument('--physical');ap.add_argument('--start',default='64');args=ap.parse_args()
    if args.physical:r.NEWPHYS=tuple(map(int,args.physical.split(',')))
    folder=r.HERE/'rotation-candidates';d=json.loads((folder/(args.name+'.json')).read_text());ns={int(k):tuple(map(tuple,v)) for k,v in d['nodes'].items()};root=d['root'];table=read_table(folder/(args.name+'.tm'))
    cases=list(c.cases(ns,root));usage=defaultdict(list);all_used=set();states=sorted({q for q,b in table},key=int)
    protected={(str(q),b) for q,b in c.audit.BOX_PAIRS};protected_targets={table[k][2] for k in protected};eligible=[q for q in states if q!='96' and q not in protected_targets and all((q,b)not in protected for b in (0,1))]
    def check(table,i):
        p,op,arg,z,b,target=cases[i]
        try:rules,literal=c.strict.run(table,p,b,target,halt=op=='CH',fuel=1000);assert literal>0;return sum(rules.values()),None
        except (AssertionError,KeyError) as ex:return 0,str(ex)
    t0=time.monotonic();minliteral=10**9
    for i in range(len(cases)):
        traced=c.Tracking(table);cost,why=check(traced,i);assert why is None,(i,why);all_used.update(traced.used)
        for q in {q for q,b in traced.used}:usage[q].append((cost,i))
    for vals in usage.values():vals.sort()
    print('BASELINE',len(cases),'usedstates',len(usage),'usedrows',len(all_used),'eligible',len(eligible),'time',time.monotonic()-t0,flush=True)
    ledger=[];survivors=[];checks=0;reasons=Counter();best=252
    for j,dead in enumerate(eligible):
        record={'deleted':int(dead),'failures':[]}
        for target in states:
            if target==dead:continue
            cand={(q,b):(w,d,target if t==dead else t) for(q,b),(w,d,t)in table.items() if q!=dead}
            assert all(cand[k]==table[k] for k in protected)
            fail=None;why=None
            for _,i in usage[dead]:
                _,why=check(cand,i);checks+=1
                if why is not None:fail=i;break
            if fail is None:
                for i in range(len(cases)):
                    _,why=check(cand,i);checks+=1
                    if why is not None:fail=i;break
            if fail is None:
                stem=f'{args.name}-fold-{dead}-to-{target}'
                output_table=folder/(stem+'.tm');r.save(output_table,cand)
                output_table.write_text(output_table.read_text().replace('#! start 64\n',f'#! start {args.start}\n',1))
                survivors.append({'dead':dead,'target':target,'table':stem+'.tm'});print('SURVIVOR',dead,target,flush=True)
            else:reasons[why]+=1
            record['failures'].append([int(target),fail])
        ledger.append(record)
        if j%25==0:print('Searched',j+1,'/',len(eligible),'checks',checks,'survivors',len(survivors),'elapsed',round(time.monotonic()-t0,2),flush=True)
    out=args.output or r.HERE/(args.name+'-uniform-folds.json')
    out.write_text(json.dumps({'input_name':args.name,'input_sha256':hashlib.sha256((folder/(args.name+'.tm')).read_bytes()).hexdigest(),'baseline_cases':len(cases),'baseline_used_states':len(usage),'baseline_used_rows':len(all_used),'eligible':list(map(int,eligible)),'recipes':len(eligible)*(len(states)-1),'checks':checks,'survivors':survivors,'elapsed_seconds':time.monotonic()-t0,'failure_counts':reasons,'ledger':ledger,'scope':'Complete bounded uniform-fold family, 1000 affine-rule fuel, four unchanged Box contracts. A checker failure is not a semantic impossibility proof.'},indent=2)+'\n')
    print('DONE',len(eligible)*(len(states)-1),checks,len(survivors),time.monotonic()-t0,flush=True)

if __name__=='__main__':main()
