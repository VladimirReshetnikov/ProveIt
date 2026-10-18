#!/usr/bin/env python3
"""Lazy joint search: incoming rewrites may compensate for one another."""
import sys,json,time,itertools,ast,random,argparse,math
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
from check_merges_symbolic import BASE,affine,build,cases
from search_invariant_merges import live_cases

class Need(Exception):
    def __init__(self,key):self.key=key

class PartialTable(dict):
    def __init__(self,base,options,assigned):
        super().__init__(base);self.options=options;self.assigned=assigned
    def __getitem__(self,key):
        if key in self.options:
            if key not in self.assigned:raise Need(key)
            return self.assigned[key]
        return super().__getitem__(key)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--prefix',default='incoming_extended')
    ap.add_argument('--seconds',type=float,default=60)
    ap.add_argument('--nodes',type=int,default=300000)
    ap.add_argument('--restricted',action='store_true')
    args=ap.parse_args()
    raw=build.build();T={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in raw.items()}
    CC=live_cases() if args.restricted else list(cases());random.Random(927).shuffle(CC)
    info=json.loads((HERE/(args.prefix+'_action_candidates.json')).read_text())
    output={}
    for q,v in info.items():
        if v['combinations']<1000:continue
        began=time.monotonic();nodes=checks=0;rejected=[];frontier=[];sol=[]
        options={}
        for e,acts in v['incoming'].items():
            a,b=ast.literal_eval(e)
            options[str(a),b]=[(w,'R' if d==1 else 'L',str(r)) for w,d,r in acts]
        base={k:row for k,row in T.items() if k[0]!=q}
        def freeze(assignment):
            return {str(k):list(row) for k,row in sorted(assignment.items())}
        def visit(assigned,index):
            nonlocal nodes,checks
            nodes+=1
            if nodes>args.nodes or time.monotonic()-began>args.seconds:
                frontier.append(dict(assignment=freeze(assigned),case=index));return
            table=PartialTable(base,options,assigned)
            for i in range(index,len(CC)):
                c=CC[i]
                try:
                    _,steps=affine.run(table,*c[:3],halt=c[3],fuel=1200)
                    assert steps>0
                    checks+=1
                except Need as need:
                    for action in options[need.key]:
                        visit(assigned|{need.key:action},i)
                        if sol:return
                    return
                except (AssertionError,KeyError) as exc:
                    rejected.append(dict(assignment=freeze(assigned),case=i,path=c[0],branch=c[1],detail=str(exc)))
                    return
            # Any still-unassigned edge was absent in every accepted trace;
            # choose its first action and then verify the completed table.
            completed=assigned|{k:opts[0] for k,opts in options.items() if k not in assigned}
            D=base|completed
            for c in CC:
                _,steps=affine.run(D,*c[:3],halt=c[3],fuel=1200);assert steps>0
            sol.append(freeze(completed))
            actual={(int(a),b):(w,d,int(r)) for (a,b),(w,d,r) in D.items()}
            (HERE/f'candidate_compensating_{q}.tm').write_text(build.encode(actual,95))
            print('SOLUTION',q,freeze(completed),flush=True)
        visit({},0)
        output[q]=dict(status='SOLUTION' if sol else ('BOUNDED_FRONTIER' if frontier else 'NO_SURVIVOR_IN_FAMILY'),
            raw_combinations=v['combinations'],cases=len(CC),nodes=nodes,completed_case_checks=checks,
            solutions=sol,rejected_partial_assignments=rejected,unfinished_frontier=frontier,
            seconds=time.monotonic()-began,
            scope='1200-rule affine checker with inherited macro contracts, after bounded local action screens; not a global state lower bound.')
        (HERE/(args.prefix+'_compensating_search.json')).write_text(json.dumps(output,indent=2))
        print('target',q,'status',output[q]['status'],'nodes',nodes,'checks',checks,'rejected',len(rejected),'frontier',len(frontier),'seconds',time.monotonic()-began,flush=True)

if __name__=='__main__':main()
