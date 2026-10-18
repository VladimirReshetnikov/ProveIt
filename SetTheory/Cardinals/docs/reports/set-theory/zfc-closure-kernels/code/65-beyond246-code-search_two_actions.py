#!/usr/bin/env python3
"""Lazy two-incoming-action deletion search; diagnostic, not an impossibility proof."""
import search_actions as base
from pathlib import Path
from collections import Counter
import json,time,argparse

class Hole(Exception):
    def __init__(self,key):self.key=key
class MutableTable(dict):
    def __init__(self,table,holes):super().__init__(table);self.holes=set(holes);self.assigned={}
    def __getitem__(self,key):
        if key in self.holes:
            if key not in self.assigned:raise Hole(key)
            return self.assigned[key]
        return super().__getitem__(key)
class TimeLimit(Exception):pass

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=600);ap.add_argument('--targets-only',action='store_true');ap.add_argument('--states');args=ap.parse_args()
    assert __debug__
    T,CASES=base.T,base.CASES
    began=time.monotonic();states=sorted({q for q,b in T},key=int)
    proof=json.loads((base.BASE/'results/macro-inductions.json').read_text());protected=set()
    def walk(v):
        if isinstance(v,dict):
            if v.get('rule') in ('literal','unary-induction'):protected.add((str(v['state']),v['read']))
            for c in v.values():walk(c)
        elif isinstance(v,list):
            for c in v:walk(c)
    walk(proof)
    keep={q for q,b in protected}|{T[k][2] for k in protected}|{'96','95'}
    trace=base.TraceTable(T);usage=[]
    for i in range(len(CASES)):
        trace.used=set();base.check(trace,i);usage.append(trace.used)
    print('Baseline8391 PASS; exact box support',len(protected),flush=True)
    candidates=[]
    for q in states:
        if q in keep:continue
        inc=[k for k,row in T.items() if row[2]==q and k[0]!=q]
        if len(inc)!=2 or any(k in protected for k in inc):continue
        if args.states and q not in args.states.split(','):continue
        ids=[i for i,u in enumerate(usage) if u&(set(inc)|{(q,0),(q,1)})]
        candidates.append((q,inc,ids))
    out=base.ROOT/'experiments/two_action_search';out.mkdir(exist_ok=True)
    done=[];survivors=[];current=None;total=Counter();stopped=False
    for q,inc,ids in candidates:
        table=MutableTable({k:v for k,v in T.items() if k[0]!=q},inc)
        allowed={k:([(T[k][0],T[k][1],r) for r in states+['254'] if r!=q] if args.targets_only else [(w,d,r) for w in (0,1) for d in ('L','R') for r in states+['254'] if r!=q]) for k in inc}
        stats=Counter();failures=Counter();start=time.monotonic()
        def visit():
            if time.monotonic()-began>args.seconds:raise TimeLimit()
            stats['nodes']+=1;total['nodes']+=1
            for at,i in enumerate(ids):
                stats['checks']+=1;total['checks']+=1
                try:base.check(table,i)
                except Hole as e:
                    key=e.key;assert key not in table.assigned
                    stats['branches']+=1
                    for action in allowed[key]:
                        table.assigned[key]=action;visit()
                    del table.assigned[key]
                    return
                except (AssertionError,KeyError) as e:
                    ids.insert(0,ids.pop(at));failures[str(e)]+=1
                    mass=1
                    for k in inc:
                        if k not in table.assigned:mass*=len(allowed[k])
                    stats['pruned_assignments']+=mass
                    return
            # If an unqueried hole remains, every completion has the same
            # accepted old-affected traces; enumerate it explicitly anyway.
            remaining=[k for k in inc if k not in table.assigned]
            if remaining:
                key=remaining[0]
                for action in allowed[key]:table.assigned[key]=action;visit()
                del table.assigned[key];return
            for i in range(len(CASES)):base.check(table,i)
            item=dict(deleted=q,edits=[[list(k),list(v)] for k,v in table.assigned.items()],all_cases=len(CASES))
            survivors.append(item);stats['survivors']+=1
            mutant=dict(table);mutant.update(table.assigned)
            name=f'candidate-{q}-{len(survivors)}.tm'
            (out/name).write_text('#! start 95\n'+''.join(f'{a} {b} {w} {d} {r}\n' for (a,b),(w,d,r) in sorted(mutant.items(),key=lambda z:(int(z[0][0]),z[0][1]))))
            print('SURVIVOR',item,flush=True)
        try:visit()
        except TimeLimit:stopped=True
        current=dict(deleted=q,incoming=[list(k) for k in inc],stats=dict(stats),seconds=time.monotonic()-start,complete=not stopped,failures=dict(failures),active_assignment=[[list(k),list(v)] for k,v in table.assigned.items()])
        if not stopped:
            planned=len(allowed[inc[0]])*len(allowed[inc[1]])
            assert stats['pruned_assignments']+stats['survivors']==planned
            current['planned']=planned;done.append(current)
        print('State',q,'complete',not stopped,'nodes',stats['nodes'],'pruned',stats['pruned_assignments'],'seconds',round(time.monotonic()-start,2),flush=True)
        summary=dict(status='partial' if stopped else 'running',total_seconds=time.monotonic()-began,stats=dict(total),completed=done,current=current,planned_states=[q for q,k,ids in candidates],survivors=survivors,targets_only=args.targets_only,scope='All four box contracts unchanged; failed symbolic traces are finite-checker outcomes, not semantic impossibility.')
        (out/'result.json').write_text(json.dumps(summary,indent=2)+'\n')
        if stopped:break
    summary['status']='partial' if stopped else 'complete'
    (out/'result.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(summary['status'],'survivors',len(survivors),'seconds',time.monotonic()-began,flush=True)
if __name__=='__main__':main()
