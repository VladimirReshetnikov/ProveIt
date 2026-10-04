#!/usr/bin/env python3
"""Supplementary independent-index/dense-residue checks, never giant integers.

Modular arithmetic here is verification, not the claimed literal source. Synthetic
occurrence values deliberately test the factorization for independent T symbols.
"""
import argparse, hashlib, json, pathlib, random, sys
from array import array
sys.dont_write_bytecode=True
import fusion_source as f

class Eval:
    def __init__(self,p,inputs):self.p=p;self.inputs=dict(inputs,one=1,three=3%p);self.values=array('q');self.n=0;self.M=0;self.A=0
    def val(self,x):return self.values[x] if type(x)is int else self.inputs[x]
    def gate(self,op,a,b):
        x,y=self.val(a),self.val(b);r=(x*y if op=='*' else x+y if op=='+' else x-y)%self.p
        out=self.n;self.n+=1;self.values.append(r)
        if op=='*':self.M+=1
        else:self.A+=1
        return out
    def power(self,a,n):
        if n==0:return 'one'
        out=a
        for bit in bin(n)[3:]:
            out=self.gate('*',out,out)
            if bit=='1':out=self.gate('*',out,a)
        return out

def exponent_check():
    count=0
    for phase in (0,f.S//2):
        for s in range(957):
            for dx in range(1200):
                b=0 if dx<=50 else 1 if dx<=650 else 2
                r=50+600*b-dx;k=(480-b-s-phase//600)%960
                lhs=(288650-phase-600*(s+1)-dx)%576000
                rhs=600*k+r
                assert 0<=r<600 and 0<=rhs<576000 and lhs==rhs
                count+=1
    return {'status':'PASS_EXACT_NONNEGATIVE_EXPONENT_IDENTITIES','checked':count}

def block_check(profiles,receipt):
    counts={};checked=0
    for name,arr in profiles.items():
        counts[name]={}
        for phase in (0,f.S//2):
            groups=receipt['block_array_identities'][name][str(phase)]['blocks'];covered=set()
            for g in groups:
                k=g['positions'][0]
                ref=tuple(arr[(288650-600*k-r-phase)%f.S] for r in range(600))
                assert hashlib.sha256(json.dumps(ref,separators=(',',':')).encode()).hexdigest()==g['mask_tuple_sha256']
                expanded=[a+i for a,n in g['runs'] for i in range(n)]
                assert expanded==g['positions']
                for k in g['positions']:
                    assert k not in covered;covered.add(k)
                    for r,v in enumerate(ref):
                        assert v==arr[(288650-600*k-r-phase)%f.S];checked+=1
            assert covered==set(range(960));counts[name][phase]=len(groups)
    return {'status':'PASS_EXACT_ARRAY_PARTITIONS','mask_entries_checked':checked,'block_counts':counts}

def mask_evaluator(p):
    powers=[pow(3,i,p) for i in range(400)];cache={0:0}
    def value(mask):
        if mask not in cache:
            m=mask;v=0
            while m:
                bit=m&-m;v=(v+powers[bit.bit_length()-1])%p;m-=bit
            cache[mask]=v
        return cache[mask]
    return value

def modular_case(profiles,q,p,w,seed):
    rand=random.Random(seed);tvals={name:[rand.randrange(p) for _ in range(957)] for name in f.KINDS}
    inputs={'W':w%p};occ={}
    for name in f.KINDS:
        occ[name]=[]
        for s,t in enumerate(tvals[name]):
            key=f'T:{name}:{s}';inputs[key]=t;occ[name].append(key)
    d=Eval(p,inputs);zero=d.gate('-','one','one');minus=d.gate('-',zero,'one');pf=f.Profiles(d,zero,minus)
    for name,width in [('H',400),('B',400),('F',400),('Hlow',25),('Hhigh',375)]:
        for v in profiles[name]:pf.get(width,v)
    for name in f.KINDS:
        for pair in q[name]:pf.get(400,*pair)
    z=d.power('three',400);_,g=f.geometric(d,z,f.R)
    powers={e:d.power('three',e) for e in [375,f.V-425,f.V-400,f.V-25,f.U-25]}
    prepared={'labels':{'0':zero},'pf':pf,'occ':occ,'Z':z,'G':g,'powers':powers}
    before=d.n;tile,first,stats=f.Fusion(d,'W',prepared,profiles,q).build()
    assert d.n-before==92107
    actual=d.val(tile),d.val(first)
    # Independent dense pointwise coefficient construction modulo p.
    value=mask_evaluator(p);dense={name:[value(m) for m in profiles[name]] for name in ['H','B','F','Hlow','Hhigh']}
    corr=[0]*f.S
    for name in f.KINDS:
        nonzero=[(dx,(value(a)-value(b))%p) for dx,(a,b) in enumerate(q[name]) if a or b]
        for s,t in enumerate(tvals[name]):
            offset=600*(s+1)
            for dx,a in nonzero:
                x=(offset+dx)%f.S;corr[x]=(corr[x]+t*a)%p
    # Compute G independently by modular binary geometric composition.
    gn=0;pn=1;zv=pow(3,400,p)
    for bit in bin(f.R)[2:]:
        gn=gn*(1+pn)%p;pn=pn*pn%p
        if bit=='1':gn=(gn+pn)%p;pn=pn*zv%p
    assert gn==d.val(g)
    bulk=[(dense['B'][x]*gn+corr[x])%p for x in range(f.S)]
    sh={e:pow(3,e,p) for e in powers}
    tv=fv=0
    for j in range(f.S-1,-1,-1):
        x=(288650-j)%f.S;y=(x-f.S//2)%f.S
        full=(dense['H'][y]+zv*bulk[y]+sh[f.V-400]*dense['F'][y])%p
        cut=(dense['Hhigh'][x]+sh[375]*bulk[x]+sh[f.V-425]*dense['F'][x])%p
        coefficient=(cut+sh[f.V-25]*full+sh[f.U-25]*dense['Hlow'][x])%p
        tv=(tv*w+coefficient)%p;fv=(fv*w+profiles['first'][x])%p
    assert actual==(tv,fv),(p,w,actual,(tv,fv))
    return {'status':'PASS_DENSE_MODULAR_DIFFERENTIAL','prime':p,'W':w,'seed':seed,'synthetic_independent_occurrences':3828,'tile_residue':tv,'first_residue':fv,'fused_gate_count':d.n-before}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True);args=ap.parse_args()
    f.pins();profiles,q=f.load_profiles();receipt=json.loads((f.ROOT/'fused-receipt.json').read_text())
    result={'exact_exponents':exponent_check(),'exact_block_arrays':block_check(profiles,receipt),'modular_cases':[]}
    for p,w,seed in [(1000003,0,10),(1000003,1,11),(1000003,-1,12),(1000003,2,13),(1000033,17,14),(2,1,15),(3,2,16)]:
        r=modular_case(profiles,q,p,w,seed);result['modular_cases'].append(r);print(json.dumps(r),flush=True)
    result['status']='PASS_ALL_FUSION_CHECKS';result['checks_sha256']=f.sha(pathlib.Path(__file__));result['fusion_source_sha256']=f.sha(f.ROOT/'fusion_source.py')
    with pathlib.Path(args.out).open('x') as o:json.dump(result,o,indent=2);o.write('\n')

if __name__=='__main__':main()
