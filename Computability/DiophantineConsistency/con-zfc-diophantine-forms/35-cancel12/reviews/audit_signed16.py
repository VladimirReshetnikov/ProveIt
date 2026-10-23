"""Independent review checks for the signed16 proposal.

Reads delivered arithmetic as inert JSON; does not import its generator.
The unbounded claims are reviewed in SIGNED16_INDEPENDENT_REVIEW.md.
"""
import hashlib,itertools,json,math,random
from collections import Counter
from pathlib import Path

HERE=Path(__file__).resolve().parent
WORK=HERE.parent/'integers'
SOURCE=WORK/'upstream'

def require(ok,why):
    if not ok:raise AssertionError(why)

def quadratic_ring_product(X,S,C,a0,a1,w1,w2):
    rad=[C,a0,a1]
    def mul(a,b):
        c=[0]*8
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                factor=1
                for k,r in enumerate(rad):
                    if i&j&(1<<k):factor*=r
                c[i^j]+=x*y*factor
        return c
    total=[1]+[0]*7
    for e0,e1,e2 in itertools.product((-1,1),repeat=3):
        term=[X,-S*e0,-S*e1*w1,0,-S*e2*w2,0,0,0]
        total=mul(total,term)
    require(total[1:]==[0]*7,'Did not descend')
    return total[0]

def norm_formula(X,S,C,a0,a1,w1,w2):
    A0=S*S*C;A1=S*S*w1*w1*a0;A2=S*S*w2*w2*a1
    V=X*X+A2-A0-A1;W=V*V+4*X*X*A2-4*A0*A1
    return W*W-16*V*V*X*X*A2

def dag_audit(path):
    p=json.loads(path.read_text());nodes=p['nodes'];counts=Counter()
    leaves=[];live=set();todo=[p['output']]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i);r=nodes[i]
        if r['kind'] in ('add','sub','mul'):todo.extend([r['left'],r['right']])
    require(len(live)==len(nodes),'Dead DAG node')
    degrees=[]
    for i,r in enumerate(nodes):
        k=r['kind'];counts[k]+=1
        if k=='variable':leaves.append(r['name']);degrees.append(1)
        elif k in ('fixed','literal'):degrees.append(0)
        else:
            require(r['left']<i and r['right']<i,'DAG not topological')
            a,b=degrees[r['left']],degrees[r['right']]
            degrees.append(a+b if k=='mul' else max(a,b))
    require(len(leaves)==len(set(leaves))==16,'Variable count')
    require('epsilon' not in leaves and 'radix_root' in leaves,'Radix coordinate not replaced')
    require(sum(counts[k] for k in ('add','sub','mul'))==1865,'Operation count')
    require(degrees[p['output']]==813056*5**32+10024,'Degree upper bound')
    fixed=sorted(r['name'] for r in nodes if r['kind']=='fixed')
    require('b_scale' in fixed and 'y_index' not in fixed,'Wrong fixed-radix leaf')
    return {'variables':leaves,'operations':{k:counts[k] for k in ('add','sub','mul')},
            'all_nodes_live':True,'degree_upper_bound':degrees[p['output']],
            'b_scale_leaf_present':True,'y_index_leaf_absent':True}

def main():
    rng=random.Random(161063);n=300
    for _ in range(n):
        args=[rng.randrange(-7,8) for _ in range(7)]
        require(norm_formula(*args)==quadratic_ring_product(*args),'Signed norm identity')
    for _ in range(n):
        xs=[rng.randrange(-4,6) for _ in range(5)]
        margin=rng.randrange(-4,6);zs=[rng.choice([-3,-2,-1,1,2,3]) for _ in range(6)]
        stack=1;factors=[]
        for d,z in zip([3*x+2 for x in xs]+[3*margin-1],zs):
            factor=1+4*d*stack*stack*z*z
            require(factor%4==1 and abs(factor)>=3 and math.gcd(factor,stack)==1,'Guard factor facts')
            stack*=factor;factors.append(factor)
        require(abs(stack)>=3**6,'Stack magnitude')
        if stack>=0 and math.isqrt(stack)**2==stack:
            require(min(xs)>=0 and margin>0,'Guard soundness example')
    files=[WORK/'signed_section.tex',WORK/'build_signed.py',WORK/'generated/signed16.json',
        SOURCE/'Lean/Master3.lean',SOURCE/'Lean/NineReduce.lean',SOURCE/'Lean/NineRatio.lean',
        SOURCE/'29-simpler-forms/signed17/SIGNED17_PROOF.md']
    receipt={'status':'PASS','scope':'Independent mathematical review plus finite arithmetic diagnostics; no Lean rebuild.',
        'cofinal_radix_review':'PASS: constructive Master3 bounds are cofinal; NineReduce preserves b; NineRatio accepts chosen b.',
        'signed_separator_review':'PASS: |Cstar|>=3^6 follows before radical recovery; signed/zero/dependent radicands handled.',
        'arbitrary_signed_radicand_norm_cases':n,'guard_cases':n,
        'dag':dag_audit(WORK/'generated/signed16.json'),
        'reviewed_sha256':{str(p.relative_to(HERE.parent)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
    (HERE/'SIGNED16_INDEPENDENT_REVIEW.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='reviewed_sha256'},indent=2))

if __name__=='__main__':main()
