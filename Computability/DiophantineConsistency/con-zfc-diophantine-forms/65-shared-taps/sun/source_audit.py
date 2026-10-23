"""Independent shared-tap coefficient audit extracted from its verifier."""
from pathlib import Path
from collections import defaultdict
import copy,itertools,json
R=Path(__file__).resolve().parent

def require(p,msg):
    if not p:raise ValueError(msg)

def add(a,b,sign=1):
    c=dict(a)
    for m,v in b.items():c[m]=c.get(m,0)+sign*v
    return {m:v for m,v in c.items() if v}

def mul(a,b):
    c=defaultdict(int)
    for m,v in a.items():
        for n,t in b.items():c[tuple(i+j for i,j in zip(m,n))]+=v*t
    return {m:v for m,v in c.items() if v}

def source_rows():
    src=json.loads((R/'data/source_system65.json').read_text());names=src['variables']+src['constants'];n=31;z=(0,)*35
    env={s:{tuple(int(j==i) for j in range(35)):1} for i,s in enumerate(names)}
    def get(v):return ({z:v} if v else {}) if type(v) is int else env[v]
    for name,op,a,b in src['source']:env[name]=mul(get(a),get(b)) if op=='*' else add(get(a),get(b),-1 if op=='-' else 1)
    rows=[add(get(a),get(b),-1) for a,b in src['comparisons']]
    original=copy.deepcopy(rows);rows[13]=add(rows[13],rows[1]);rows[14]=add(rows[14],rows[2])
    require(add(rows[13],rows[1],-1)==original[13] and add(rows[14],rows[2],-1)==original[14],'inverse row operations')
    out=[]
    for row in rows:
        block=defaultdict(dict)
        for mon,c in row.items():
            p=tuple(i for i,e in enumerate(mon[:n]) for _ in range(e));require(len(p)<=2,'quadratic source')
            fac=2 if len(p)!=2 or p[0]==p[1] else 1
            block[p][mon[n:]]=c*fac
        out.append(dict(block))
    return out

def audit_source(layout,kerneldata):
    rows=source_rows();w=layout['weights'];qmap=dict(zip(layout['order'],layout['targets']))
    require(len(w)==31 and len(set(w))==31 and min(w)>0,'positive distinct positions')
    require(sorted(qmap)==list(range(1,23)) and len(set(qmap.values()))==22,'target numbering')
    kernels=[]
    for d,layer in enumerate(kerneldata['kernels']):
        require(layer['degree']==d,'layer order')
        k={t['exponent']:{tuple(c['powers']):c['coefficient'] for c in t['coefficient']} for t in layer['terms']}
        require(len(k)==len(layer['terms']) and min(k)>=0,'kernel positions');kernels.append(k)
    mons=[[()],[(i,) for i in range(31)],list(itertools.combinations_with_replacement(range(31),2))]
    checks=0
    for r,q in qmap.items():
        for d in range(3):
            for mon in mons[d]:
                got=kernels[d].get(q-sum(w[i] for i in mon),{});wanted=rows[r-1].get(mon,{})
                require(got==wanted,f'exact target coefficient row={r} monomial={mon}');checks+=1
    owners=[defaultdict(list) for _ in range(3)]
    for r,q in qmap.items():
        for mon in rows[r-1]:owners[len(mon)][q-sum(w[i] for i in mon)].append([r,list(mon)])
    require(all(set(kernels[d])==set(owners[d]) for d in range(3)),'no unowned coefficient taps')
    deg=[max(k) for k in kernels];W=max(w);H=max(deg[d]+d*W for d in range(3));Q=max(qmap.values())
    require(deg==layout['kernel_degrees'] and H==layout['convolution_height'] and W==layout['max_weight'] and Q==layout['maximum_target'],'source degrees')
    require(kernels[2][deg[2]]=={(0,0,0,0):1},'positive quadratic leader')
    require(deg[2]+W-deg[1]>=18 and deg[2]+2*W-deg[0]>=442,'unconditional source positivity gaps')
    require(H-Q>=32,'sparse target headroom')
    bits=[1064921,1070004,1064921,1064922]
    maxbound=max(sum(abs(c)*(1<<sum(e*b for e,b in zip(mon,bits))) for mon,c in co.items()) for k in kernels for co in k.values())
    require(maxbound.bit_length()==2134927,'coefficient bound')
    share=[{'degree':d,'exponent':e,'owners':v} for d,layer in enumerate(owners) for e,v in layer.items() if len(v)>1]
    return {'source_rows':22,'target_identities':22,'coefficient_checks':checks,'weighted_source_records':sum(len(x) for x in rows),'unique_taps':sum(len(k) for k in kernels),'shared_taps':share,'W':W,'H':H,'Q':Q,'kernel_degrees':deg}

