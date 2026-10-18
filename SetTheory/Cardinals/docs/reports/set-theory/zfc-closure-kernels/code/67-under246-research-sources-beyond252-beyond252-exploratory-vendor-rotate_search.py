"""Search local closed-subroutine reassociations and commuting increments.

The candidate is always another RM decoder DAG. This script does not emit a
Turing machine or assert any new small-machine record.
"""
from dag_tools import *
import random,math,json,time,argparse

def edge_bounds(nodes):
    @lru_cache(None)
    def b(e):
        if e[0]=='N':
            x,y=map(b,nodes[e[1]])
            return (1+max(x[0],y[0]),max(x[1]-1,y[1]),max(x[2],y[2]-1))
        return (0, e[1] if e[0]=='B' else (1 if e[0]=='D' else 0), e[1] if e[0]=='C' else 0)
    return b

def zero_metrics(nodes,root):
    @lru_cache(None)
    def calc(e):
        if e[0]!='N':return (0,0,0)
        x,y=map(calc,nodes[e[1]])
        prefix=1+x[0]
        return prefix,max(prefix,x[1],y[1]),1+max(x[2],y[2])
    return calc(('N',root))

def options(nodes):
    b=edge_bounds(nodes);closed=lambda e:b(e)[1:]==(0,0)
    out=[]
    for n,(x,y) in nodes.items():
        if x[0]=='N':
            a,c=nodes[x[1]]
            if all(map(closed,(a,c,y))):out.append((n,('T',a,('T',c,y)),'associate_right'))
        if y[0]=='N':
            a,c=nodes[y[1]]
            if all(map(closed,(x,a,c))):out.append((n,('T',('T',x,a),c),'associate_left'))
        if x[0]==y[0]=='I' and x!=y:out.append((n,('T',y,x),'commute_increments'))
    return out

def mutate(nodes,root,n,exp):
    new={};seen={}
    def intern(a,b):
        p=(a,b)
        if p not in seen:i=len(new);seen[p]=i;new[i]=p
        return ('N',seen[p])
    @lru_cache(None)
    def edge(e):
        if e[0]=='N':
            if e[1]==n:return edge(exp)
            a,b=nodes[e[1]];return intern(edge(a),edge(b))
        if e[0]=='T':return intern(edge(e[1]),edge(e[2]))
        return e
    r=edge(('N',root))[1]
    return new,r

def run(iterations=10000,restarts=5,maxzeros=7,maxdepth=58,seed=254,suffix='constrained',inputfile=None):
    initial,ir=interned(unfold(read_p254()));best=initial;br=ir;hist=[]
    if inputfile:
        data=json.loads(Path(inputfile).read_text())
        best={int(i):tuple(tuple(e) for e in p) for i,p in data['nodes'].items()};br=data['root']
    t0=time.time();rng=random.Random(seed)
    for restart in range(restarts):
        cur,r=best,br
        for it in range(iterations):
            opts=options(cur)
            if not opts:break
            n,exp,kind=rng.choice(opts)
            nxt,nr=mutate(cur,r,n,exp)
            zm=zero_metrics(nxt,nr)
            if zm[1]>maxzeros or zm[2]>maxdepth:continue
            d=len(nxt)-len(cur)
            temperature=.05+.4*(1-it/iterations)
            if d<=0 or rng.random()<math.exp(-d/temperature):cur,r=nxt,nr
            if len(cur)<len(best):
                best,br=cur,r;hist.append([restart,it,len(best),kind])
                print('best',hist[-1],flush=True)
                checkpoint=Path(__file__).resolve().parent/f'rotated_dag_{suffix}.json'
                checkpoint.write_text(json.dumps({'root':br,'nodes':best},indent=2)+'\n')
    out=Path(__file__).resolve().parent
    result={'baseline_decoder_nodes':len(initial),'best_decoder_nodes':len(best),
            'depth':edge_bounds(best)(('N',br))[0],'iterations_per_restart':iterations,
            'restarts':restarts,'improvements':hist,'seconds':time.time()-t0,
            'max_zero_run':zero_metrics(best,br)[1],'limit_zero_run':maxzeros,
            'limit_depth':maxdepth,'seed':seed,'is_Turing_machine_state_count':False}
    (out/f'rotation_results_{suffix}.json').write_text(json.dumps(result,indent=2)+'\n')
    (out/f'rotated_dag_{suffix}.json').write_text(json.dumps({'root':br,'nodes':best},indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--iterations',type=int,default=10000);ap.add_argument('--restarts',type=int,default=5)
    ap.add_argument('--maxzeros',type=int,default=7);ap.add_argument('--maxdepth',type=int,default=58)
    ap.add_argument('--seed',type=int,default=254);ap.add_argument('--suffix',default='constrained')
    ap.add_argument('--inputfile')
    a=ap.parse_args();run(a.iterations,a.restarts,a.maxzeros,a.maxdepth,a.seed,a.suffix,a.inputfile)
