"""Search semantics-preserving global closed-sequence rotations.

Every accepted edge uses the zero boundary lemma; final evidence also uses two
independent complete guarded-CFG resolvers. This optimizes source sharing only.
It does not assert a compiler/state-count result.
"""
from pathlib import Path
import argparse, collections, functools, json, math, random, sys, time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent/'source_work/portable/baseline226/verification'))
import reconstruct227 as c

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--sites', type=Path, default=HERE.parent/'source_work/search/fused/i1-j2-h167/sites.json')
    ap.add_argument('--seconds', type=float, default=600)
    ap.add_argument('--seed', type=int, default=2517)
    ap.add_argument('--output', type=Path, default=HERE/'source_dag_search')
    ap.add_argument('--table', type=Path)
    ap.add_argument('--preserve-aliases', action='store_true')
    ap.add_argument('--commute', action='store_true')
    args=ap.parse_args(); args.output.mkdir(parents=True, exist_ok=True)
    oldrows=json.loads(args.sites.read_text()); oldtree=c.tree(oldrows)
    vals=[]; inv={}; bounds=[]; leading=[]; zeros=[]; heights=[]; touches=[]
    def intern(x):
        if x in inv:return inv[x]
        q=len(vals);inv[x]=q;vals.append(x)
        if isinstance(x[0],str):
            b=c.boundary(x); lead=0; z=0; h=0
            touch=(1<<x[1]) if x[0] in ('CI','CD') else 0
        else:
            a,b=x; ba,bb=bounds[a],bounds[b]
            b=(max(ba[0]-1,0,bb[0]),max(ba[1],bb[1]-1,0),ba[2]or bb[2])
            lead=1+leading[a];z=max(lead,zeros[a],zeros[x[1]]);h=1+max(heights[a],heights[x[1]])
            touch=touches[a]|touches[x[1]]
        bounds.append(b);leading.append(lead);zeros.append(z);heights.append(h);touches.append(touch)
        return q
    def parse(x):return intern(x if c.leaf(x) else (parse(x[0]),parse(x[1])))
    first=parse(oldtree)
    alias_trees=[]
    if args.preserve_aliases:
        sys.path.insert(0, str(HERE.parent/'source_work/search'))
        import rotate_search as rs
        assert args.table is not None
        groups,_=rs.mapping(rs.read_table(args.table),oldtree)
        alias_trees=list({n for ns in groups.values() if len(ns)>1 for n in ns})
    protected={parse(n) for n in alias_trees}
    def live(root):
        seen=set();todo=[root]
        while todo:
            q=todo.pop()
            if q in seen:continue
            seen.add(q);x=vals[q]
            if not isinstance(x[0],str):todo.extend(x)
        return seen
    def replace(root,src,dst):
        memo={src:dst}
        def f(q):
            if q in memo:return memo[q]
            x=vals[q]
            ans=q if isinstance(x[0],str) else intern((f(x[0]),f(x[1])))
            memo[q]=ans;return ans
        return f(root)
    def rotations(root):
        for q in live(root):
            x=vals[q]
            if isinstance(x[0],str):continue
            if args.commute and x[0]!=x[1] and all(bounds[v]==(0,0,False) for v in x) and not(touches[x[0]]&touches[x[1]]):
                nn=intern((x[1],x[0]));yield q,2,nn,replace(root,q,nn)
            for side in (0,1):
                child=vals[x[side]]
                if isinstance(child[0],str):continue
                a,b,d=(*child,x[1]) if side==0 else (x[0],*child)
                if any(bounds[v]!=(0,0,False) for v in (a,b,d)):continue
                nn=intern((a,intern((b,d)))) if side==0 else intern((intern((a,b)),d))
                yield q,side,nn,replace(root,q,nn)
    def path_to(root,q):
        def f(at,p):
            if at==q:return p
            x=vals[at]
            if isinstance(x[0],str):return None
            a=f(x[0],p+'0')
            return a if a is not None else f(x[1],p+'1')
        return f(root,'')
    def decode(q):
        x=vals[q]
        return x if isinstance(x[0],str) else (decode(x[0]),decode(x[1]))
    def cost(root):return len(live(root)),zeros[root],heights[root]
    initial=cost(first);best=initial;bestroot=first;besthist=[]
    rng=random.Random(args.seed);start=time.time();seen={first};evaluated=0;walk=0
    def save(root,hist):
        rows=c.sites(decode(root));graph,nchecks=c.graph_arithmetic(rows)
        assert graph==c.graph_intervals(rows)
        if not args.commute:assert graph==c.graph_arithmetic(oldrows)[0]
        (args.output/'best_sites.json').write_bytes(c.compact(rows))
        (args.output/'best.json').write_text(json.dumps({'input':str(args.sites),'metrics':c.metrics(decode(root)),'initial':initial,'history':hist,'cfg_equal':not args.commute,'source_equivalence':'closed rotations and disjoint-register closed commutations' if args.commute else 'closed rotations','cfg_checks':nchecks,'elapsed':time.time()-start,'evaluated':evaluated,'seed':args.seed},indent=2)+'\n')
    print('INITIAL',initial,flush=True);save(first,[])
    while time.time()-start<args.seconds:
        root=first if walk%4==0 else bestroot;history=[] if root==first else besthist[:]
        current=cost(root);temperature=0.1 if walk%3 else 0.4
        for step in range(500):
            if time.time()-start>=args.seconds:break
            choices=[]
            for q,side,nn,nr in rotations(root):
                evaluated+=1
                if nr in seen:continue
                if protected and not protected.issubset(live(nr)):continue
                met=cost(nr)
                if met[1]>6 or met[0]>best[0]+2:continue
                penalty=met[0]+0.005*met[2]
                choices.append((penalty+rng.expovariate(1/temperature),met,q,side,nn,nr))
            if not choices:break
            _,met,q,side,nn,nr=min(choices)
            if met[0]>current[0] and rng.random()>math.exp((current[0]-met[0])/temperature):
                seen.add(nr);continue
            history.append({'path':path_to(root,q),'direction':('right','left','swap')[side]})
            root=nr;current=met;seen.add(root)
            if met<best:
                best=met;bestroot=root;besthist=history[:];save(root,history)
                print('BEST',best,'walk',walk,'step',step,'history',len(history),'evaluated',evaluated,'elapsed',round(time.time()-start,2),flush=True)
                if best[0]<initial[0]:
                    print('SOURCE_DAG_REDUCED',flush=True)
            if best[0]<=208:break
        walk+=1
        if walk%3==0:print('WALK',walk,'best',best,'eval',evaluated,'nodes',len(vals),'elapsed',round(time.time()-start,2),flush=True)
        if best[0]<=208:break
        # Interning every explored neighbor accumulates dead nodes. Keep only
        # the roots and protected patterns between walks.
        besttree=decode(bestroot)
        vals.clear();inv.clear();bounds.clear();leading.clear();zeros.clear();heights.clear();touches.clear()
        first=parse(oldtree);bestroot=parse(besttree)
        protected={parse(n) for n in alias_trees};seen={first,bestroot}
    print('DONE',best,'evaluated',evaluated,'elapsed',time.time()-start,flush=True)
if __name__=='__main__':main()
