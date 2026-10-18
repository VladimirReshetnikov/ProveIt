#!/usr/bin/env python3
"""Affine-filter individual rewrites before jointly deleting a decoder state."""
import sys,json,time,itertools,ast,random,argparse,math
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
from check_merges_symbolic import BASE,affine,build,cases
from search_invariant_merges import live_cases

class Recording(dict):
    def __init__(self,d):super().__init__(d);self.visited=set()
    def __getitem__(self,k):self.visited.add(k);return super().__getitem__(k)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--prefix',default='incoming_extended')
    ap.add_argument('--restricted',action='store_true')
    args=ap.parse_args()
    began=time.monotonic();raw=build.build()
    T={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in raw.items()}
    CC=live_cases() if args.restricted else list(cases());random.Random(927).shuffle(CC)
    bykey={k:[] for k in T};rec=Recording(T)
    for i,c in enumerate(CC):
        rec.visited.clear();affine.run(rec,*c[:3],halt=c[3],fuel=1200)
        for k in rec.visited:bykey[k].append(i)
    info=json.loads((HERE/(args.prefix+'_action_candidates.json')).read_text())
    out={};survivors=[];tests=0
    for q,v in info.items():
        if v['combinations']<1000:continue
        opts={};ledger=[]
        for e,acts in v['incoming'].items():
            a,b=ast.literal_eval(e);key=str(a),b;valid=[]
            for act in acts:
                w,d,r=act;D=T.copy();D[key]=w,'R' if d==1 else 'L',str(r)
                passed=0
                try:
                    for i in bykey[key]:
                        c=CC[i];affine.run(D,*c[:3],halt=c[3],fuel=1200);passed+=1
                except (AssertionError,KeyError) as exc:reason=str(exc);status='REJECT'
                else:reason='all affected cases passed';status='PASS';valid.append(act)
                ledger.append(dict(edge=e,action=act,status=status,cases_passed=passed,detail=reason));tests+=1
            opts[e]=valid
        remaining=math.prod(map(len,opts.values()))
        print('deleted',q,'raw',v['combinations'],'after_individual',remaining,'options',{k:len(x) for k,x in opts.items()},flush=True)
        joint=[]
        if remaining<=100000:
            keys=[ast.literal_eval(e) for e in opts]
            for acts in itertools.product(*opts.values()):
                D={k:row for k,row in T.items() if k[0]!=q}
                for (a,b),(w,d,r) in zip(keys,acts):D[str(a),b]=(w,'R' if d==1 else 'L',str(r))
                assert q not in {r for w,d,r in D.values()}
                passed=0
                try:
                    for c in CC:affine.run(D,*c[:3],halt=c[3],fuel=1200);passed+=1
                except (AssertionError,KeyError) as exc:reason=str(exc);status='REJECT'
                else:
                    reason='all instruction cases passed';status='PASS';survivors.append((q,acts))
                    actual={(int(a),b):(w,d,int(r)) for (a,b),(w,d,r) in D.items()}
                    (HERE/f'candidate_incoming_{q}_{len(survivors)}.tm').write_text(build.encode(actual,95))
                    print('SURVIVOR',q,acts,flush=True)
                joint.append(dict(actions=acts,status=status,cases_passed=passed,detail=reason))
        out[q]=dict(individual=ledger,options=opts,joint_combinations=remaining,joint=joint)
        (HERE/(args.prefix+'_affine_filter.json')).write_text(json.dumps(out,indent=2))
    print('DONE','tested',tests,'survivors',survivors,'seconds',time.monotonic()-began,flush=True)

if __name__=='__main__':main()
