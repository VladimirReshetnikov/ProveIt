"""Explore exact source-CFG-preserving rotations through a one-node plateau.

Search only: accepted output still requires full source and binary validation.
Uses the attributed exact_reassociate.py implementation in this directory.
"""
from pathlib import Path
import argparse,json,random,time,math
import exact_reassociate as e

def main():
    p=argparse.ArgumentParser();p.add_argument('--steps',type=int,default=100000)
    p.add_argument('--seed',type=int,default=1906);p.add_argument('--cap',type=int,default=226)
    p.add_argument('--output',type=Path,default=Path(__file__).parent/'stochastic_result.json')
    p.add_argument('--source',type=Path)
    p.add_argument('--cold',action='store_true')
    a=p.parse_args()
    if a.source:
        data=json.loads(a.source.read_text());e.S[:]=map(tuple,data['structures']);e.I.clear();e.I.update({x:i for i,x in enumerate(e.S)});e.ROOT=data['root'];e.N0=len(e.S)
    r=random.Random(a.seed);initial=e.ROOT;root=initial
    current=e.score(root);best=current;start=time.monotonic();accepted=0;examined=0;baseline=e.signature(initial)
    print('START',current,flush=True)
    for step in range(a.steps):
        choices=[(n,x) for n in e.live(root) for x in e.rotations(n)]
        n,(alt,d,chunks,closed)=r.choice(choices);new=e.replace(root,n,alt)
        sc=e.score(new);examined+=1
        # Node count is the primary cost. Temperature periodically crosses one
        # extra-node barriers; zero-run six remains a hard compiler constraint.
        temperature=([.02,.10,.25,.10] if a.cold else [.25,.6,1.0,.6])[(step//5000)%4]
        delta=sc[0]-current[0]+.005*(sc[2]-current[2])
        if sc[0]<=a.cap and sc[1]<=6 and (delta<=0 or r.random()<math.exp(-delta/temperature)):
            root=new;current=sc;accepted+=1
            if sc[0]<best[0]:
                assert e.signature(root)==baseline
                e.export(root,[],a.output.name,{'status':'SOURCE_CANDIDATE_FULL_CFG_IDENTITY','steps':step+1,'seed':a.seed,'accepted':accepted,'seconds':time.monotonic()-start})
                best=sc;print('BEST',best,'step',step+1,flush=True)
                if best[0]<=223:return
        if (step+1)%1000==0:
            # Only the current exact source needs retention: a complete direct
            # source control-graph comparison certifies the final result.
            roots=e.compact([(initial,[]),(root,[])])
            initial,root=roots[0][0],roots[1][0]
        if (step+1)%5000==0:
            print('PROGRESS',step+1,current,'accepted',accepted,'seconds',round(time.monotonic()-start,2),flush=True)
        if (step+1)%20000==0:
            root=initial;current=e.score(root)
    a.output.write_text(json.dumps({'status':'BOUNDED_SEARCH_NO_NODE_REDUCTION','steps':a.steps,'examined':examined,'accepted':accepted,'best':best,'seed':a.seed,'cap':a.cap,'seconds':time.monotonic()-start},indent=2)+'\n')
    print('DONE',best,flush=True)
if __name__=='__main__':main()
