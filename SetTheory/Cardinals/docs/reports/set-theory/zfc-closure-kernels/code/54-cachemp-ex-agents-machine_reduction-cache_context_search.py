#!/usr/bin/env python3
"""Lazy full incoming-action search on the cache-MP semantic variant.

Mutations never touch the protected box support. A failed trace without an
undefined row is identical across its unassigned completions. This searches
two coordinated incoming actions including write/move, beyond simple folds.
Finite symbolic rejection is not semantic impossibility.
"""
from pathlib import Path
from collections import Counter
import argparse,json,time,itertools
import rotation_search252 as r
import check_rotation252 as c
from fold_changed252 import read_table

class NeedRow(Exception):
    pass

class Partial(dict):
    def __init__(self,t,undefined):super().__init__(t);self.undefined=set(undefined)
    def __getitem__(self,key):
        if key in self.undefined:raise NeedRow(key)
        return super().__getitem__(key)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--dead',type=int,default=252);ap.add_argument('--seconds',type=float,default=180);ap.add_argument('--target-only',action='store_true');ap.add_argument('--output',type=Path);args=ap.parse_args()
    folder=r.HERE/'rotation-candidates';d=json.loads((folder/'mp-cache252.json').read_text());ns={int(k):tuple(map(tuple,v)) for k,v in d['nodes'].items()};root=d['root'];table=read_table(folder/'mp-cache252.tm');dead=str(args.dead);cases=list(c.cases(ns,root));states=sorted({q for q,b in table}-{dead},key=int)
    incoming=[k for k,v in table.items() if v[2]==dead and k[0]!=dead];protected={(str(q),b) for q,b in c.audit.BOX_PAIRS};assert all(k not in protected for k in incoming);assert all(k[0]!=dead for k in protected);assert dead!='96'
    baseline=[]
    for i,(p,op,arg,z,branch,target) in enumerate(cases):
        t=c.Tracking(table);rules,literal=c.strict.run(t,p,branch,target,halt=op=='CH',fuel=1000)
        if any(k[0]==dead for k in t.used):baseline.append((sum(rules.values()),i))
    baseline.sort();order=[i for _,i in baseline];print('INPUT',dead,incoming,'affected',len(order),'branching',len(states)*(1 if args.target_only else 4),flush=True)
    choices={key:[(table[key][0],table[key][1],t) for t in states] if args.target_only else [(w,d,t) for w in (0,1) for d in ('L','R') for t in states] for key in incoming}
    base={k:v for k,v in table.items() if k[0]!=dead};stack=[({},0)];pruned=0;seen=0;checks=0;survivors=[];whycount=Counter();begin=time.monotonic();prunes=[]
    while stack and time.monotonic()-begin<args.seconds:
        assigned,startcase=stack.pop();seen+=1;cur=Partial(base,[k for k in incoming if k not in assigned]);cur.update(assigned);failed=None;need=None
        for j in range(startcase,len(order)):
            i=order[j];p,op,arg,z,branch,target=cases[i]
            try:c.strict.run(cur,p,branch,target,halt=op=='CH',fuel=1000);checks+=1
            except NeedRow as ex:need=ex.args[0];break
            except (AssertionError,KeyError) as ex:failed=str(ex);checks+=1;break
        if failed is not None:
            weight=1
            for k in incoming:
                if k not in assigned:weight*=len(choices[k])
            pruned+=weight;whycount[failed]+=weight;prunes.append({'assigned':[[*k,*v] for k,v in assigned.items()],'first_failure_case':i,'weight':weight});continue
        if need is not None:
            assert need not in assigned
            for action in reversed(choices[need]):stack.append((dict(assigned,**{})|{need:action},j))
            continue
        if len(assigned)<len(incoming):
            need=next(k for k in incoming if k not in assigned)
            for action in reversed(choices[need]):stack.append((assigned|{need:action},0))
            continue
        allcheck=c.run(dict(cur),ns,root,stop=True)
        if allcheck['failures']:
            pruned+=1;whycount['full_recheck_failure']+=1;continue
        stem=f'cache-context-delete{dead}-{len(survivors)}';r.save(folder/(stem+'.tm'),cur);survivors.append({'table':stem+'.tm','assignment':[[*k,*v] for k,v in assigned.items()]});print('SURVIVOR',survivors[-1],flush=True)
    frontier=[];remaining=0
    for a,i in stack:
        weight=1
        for k in incoming:
            if k not in a:weight*=len(choices[k])
        remaining+=weight;frontier.append({'assigned':[[*k,*v] for k,v in a.items()],'case_index':i,'weight':weight})
    planned=1
    for k in incoming:planned*=len(choices[k])
    assert planned==pruned+remaining+len(survivors)
    result={'dead':args.dead,'incoming':incoming,'target_only':args.target_only,'source_table':'mp-cache252.tm','affected_cases':len(order),'planned':planned,'pruned':pruned,'remaining':remaining,'survivors':survivors,'partial_assignments':seen,'affine_checks':checks,'elapsed_seconds':time.monotonic()-begin,'seconds_limit':args.seconds,'pruning_reasons':whycount,'frontier':frontier,'prune_ledger':prunes,'scope':'Coordinated incoming-action diagnostics conditional on unchanged Box contracts; no candidate startup or formal endpoint inferred.'}
    out=args.output or r.HERE/f'cache-context-delete{dead}-{"target" if args.target_only else "fullaction"}.json';out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ('prune_ledger','frontier','pruning_reasons')},indent=2),flush=True)

if __name__=='__main__':main()
