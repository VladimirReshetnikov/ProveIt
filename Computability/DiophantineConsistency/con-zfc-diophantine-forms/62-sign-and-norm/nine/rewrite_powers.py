"""Replace pure-base power subgraphs by a shared addition chain.

The rewrite changes no polynomial. The independent certificate is a list
of exponent additions checked for exact integer equality.
"""
import json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent))
from circuit import DAG

def rewrite(src):
    B=src['named_nodes']['B']; exps=[]
    for k,n in enumerate(src['nodes']):
        e=1 if k==B else (0 if n['kind']=='literal' and n['value']==1 else None)
        if k!=B and n['kind']=='mul':
            a,b=exps[n['left']],exps[n['right']]
            if a is not None and b is not None:e=a+b
        exps.append(e)
    req=set()
    for k,n in enumerate(src['nodes']):
        if n['kind'] in ['mul','add','sub'] and exps[k] is None:
            for v in [n['left'],n['right']]:
                if exps[v] is not None and exps[v]>1:req.add(exps[v])
    chains={1:None}
    def direct(e,known):
        return next(((x,e-x) for x in sorted(known) if e-x in known),None)
    def plan(e,known,depth=0):
        if e in known:return []
        pair=direct(e,known)
        if pair:return [(e,*pair)]
        candidates=[]
        h=e//2
        z=plan(h,known,depth+1); kn=known|{t[0] for t in z}
        if 2*h not in kn:z.append((2*h,h,h));kn.add(2*h)
        if e!=2*h:z.append((e,2*h,1))
        candidates.append(z)
        for x in sorted(known,reverse=True):
            if x>=e or e-x>=e:continue
            y=e-x
            p=direct(y,known)
            if p:candidates.append([(y,*p),(e,x,y)])
        return min(candidates,key=lambda z:(len(z),tuple(t[0] for t in z)))
    for e in sorted(req):
        for v,a,b in plan(e,set(chains)):
            if v not in chains:chains[v]=(a,b)
    d=DAG();cache={};powers={}
    def rec(k):
        if k in cache:return cache[k]
        n=src['nodes'][k]
        if exps[k] is not None and exps[k]>1:out=power(exps[k])
        elif n['kind']=='variable':out=d.var(n['name'])
        elif n['kind']=='literal':out=d.const(n['value'])
        elif n['kind']=='fixed':out=d.fixed(n['name'])
        else:out=d.binary(n['kind'],rec(n['left']),rec(n['right']))
        cache[k]=out;return out
    def power(e):
        if e not in powers:
            if e==1:powers[e]=rec(B)
            else:
                a,b=chains[e];powers[e]=d.times(power(a),power(b))
        return powers[e]
    out=rec(src['output']);
    for name,k in src['named_nodes'].items():
        if k in cache:d.save(name,cache[k])
    nodes,out,names=d.prune(out)
    from collections import Counter
    counts=dict(Counter(n['kind'] for n in nodes if n['kind'] in ['add','mul','sub']))
    dst=dict(src,nodes=nodes,output=out,named_nodes=names,total_operations=sum(counts.values()),operation_counts=counts,power_method='global certified chain')
    return dst,{'old_power_gates':sum(e is not None and e>1 for e in exps),'required_exponents':sorted(req),'chain':[(e,*p) for e,p in chains.items() if p is not None],'new_power_gates':len(chains)-1,'old_operations':src['total_operations'],'new_operations':dst['total_operations']}

if __name__=='__main__':
    source=Path(sys.argv[1]);result,cert=rewrite(json.loads(source.read_text()));target=source.with_name(source.stem+'_global.json');target.write_text(json.dumps(result,separators=(',',':'))+'\n');target.with_suffix('.certificate.json').write_text(json.dumps(cert,indent=2)+'\n');print(cert)
