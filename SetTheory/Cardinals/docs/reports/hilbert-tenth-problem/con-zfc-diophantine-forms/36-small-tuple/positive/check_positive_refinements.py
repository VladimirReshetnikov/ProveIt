#!/usr/bin/env python3
"""Independent finite arithmetic checks; no claim to prove the compiler."""
from pathlib import Path
import json, random, hashlib
from build_positive_refinements import build, VARS, PORTS
HERE=Path(__file__).resolve().parent

def evaluate(c,values,mod=None):
    e=dict(values)
    for name,op,l,r in c['source']:
        l=l if isinstance(l,int) else e[l]
        r=r if isinstance(r,int) else e[r]
        v=l+r if op=='+' else l-r if op=='-' else l*r
        e[name]=v if mod is None else v%mod
    return e

def direct_norm(e,mod=None):
    """Multiply all 8 factors in Z[g,tau,f]/(g²-G,tau²-A,f²-D)."""
    rad=[e['G'],e['A'],e['D']]
    def mul(a,b):
        out=[0]*8
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                z=x*y
                for k in range(3):
                    if (i&j)&(1<<k): z*=rad[k]
                out[i^j]+=z
        return out if mod is None else [x%mod for x in out]
    one=[1]+[0]*7
    B=2*e['Q']*e['c']*e['T']*e['b']
    hs=e['H']**2
    ev=e['P']+e['U']-1
    for sg in (-1,1):
        for st in (-1,1):
            for sf in (-1,1):
                x=[e['W'],-sg*e['L'],-st*e['HM'],0,0,0,0,0]
                factor=[e['d']*v for v in mul(x,x)]
                factor[0]-=hs*ev; factor[4]+=sf*hs*B
                one=mul(one,factor)
    if any(one[1:]): raise ValueError('Norm did not descend')
    return one[0]

def ntt(a,invert,p):
    n=len(a);j=0
    for i in range(1,n):
        bit=n>>1
        while j&bit: j^=bit;bit>>=1
        j^=bit
        if i<j:a[i],a[j]=a[j],a[i]
    length=2
    while length<=n:
        root=pow(3,(p-1)//length,p)
        if invert:root=pow(root,p-2,p)
        half=length//2
        for start in range(0,n,length):
            w=1
            for j in range(start,start+half):
                u=a[j];v=a[j+half]*w%p
                a[j]=(u+v)%p;a[j+half]=(u-v)%p;w=w*root%p
        length*=2
    if invert:
        inv=pow(n,p-2,p)
        for i in range(n):a[i]=a[i]*inv%p

def poly_mul(a,b,p):
    if len(a)*len(b)<1024:
        c=[0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b): c[i+j]=(c[i+j]+x*y)%p
    else:
        size=1
        while size<len(a)+len(b)-1:size*=2
        aa=a+[0]*(size-len(a));bb=b+[0]*(size-len(b))
        ntt(aa,False,p);ntt(bb,False,p)
        c=[x*y%p for x,y in zip(aa,bb)];ntt(c,True,p)
        c=c[:len(a)+len(b)-1]
    while len(c)>1 and not c[-1]:c.pop()
    return c

def degree_test(c,p,seed):
    rng=random.Random(seed)
    e={v:[0,rng.randrange(1,p)] for v in VARS}
    e.update({v:[rng.randrange(1,p)] for v in PORTS})
    for name,op,l,r in c['source']:
        a=[l%p] if isinstance(l,int) else e[l]
        b=[r%p] if isinstance(r,int) else e[r]
        if op=='*': v=poly_mul(a,b,p)
        else:
            v=[((a[i] if i<len(a) else 0)+(1 if op=='+' else -1)*(b[i] if i<len(b) else 0))%p for i in range(max(len(a),len(b)))]
            while len(v)>1 and v[-1]==0:v.pop()
        e[name]=v
    degree=len(e[c['output']])-1
    if degree!=c['exact_degree']:raise ValueError(('Degree mismatch',degree,c['exact_degree']))
    return {'prime':p,'seed':seed,'degree':degree,'leading_coefficient':e[c['output']][-1]}

def main():
    rng=random.Random(20261023)
    data={'scope':'Finite arithmetic evidence, not a semantic compiler certificate','variants':[]}
    source=HERE/'upstream/positive12_product.original30.json'
    old=json.loads(source.read_text())
    tightold=json.loads((HERE/'upstream/positive12_product.original24.json').read_text())
    for weight in ('short','tight'):
        c=build(weight)
        for j in range(48):
            values={v:rng.randrange(-3,5) for v in VARS+PORTS}
            e=evaluate(c,values)
            expected=direct_norm(e)
            if e['N']!=expected:raise ValueError(('Norm identity failed',weight,j))
            if e['N']%4 not in (0,1):raise ValueError(('Parity failed',weight,j))
            if weight=='short':
                oe=evaluate(old,values)
                if e[c['output']]!=oe[old['output']]:raise ValueError('Old polynomial mismatch')
            else:
                oldvalues=dict(values,r=values['t'])
                oe=evaluate(tightold,oldvalues)
                if e[c['output']]!=oe[tightold['output']]:raise ValueError('Old tight polynomial mismatch')
            shifted=build(weight,True,True)
            se=evaluate(shifted,values)
            oldvalues=dict(values,z=values['z']+1)
            ue=evaluate(build(weight,True,False),oldvalues)
            if se['NtLeft']-se['NtRight'] != ue['Nt']-1:raise ValueError('Transport identity')
            if se['NormRight']-se['NormLeft'] != e['N']:raise ValueError('System norm identity')
        checks=[degree_test(c,p,seed) for p,seed in [(998244353,215),(1004535809,216)]]
        data['variants'].append({'weight':weight,'exact_signed_norm_cases':48,'same_as_old_symbolic_template':True,
             'degree_diagnostics':checks,'product':c['ledger'],
             'unshifted_system':build(weight,True,False)['ledger'],'shifted_system':build(weight,True,True)['ledger']})
        for system,shift in ((False,False),(True,False),(True,True)):
            packet=build(weight,system,shift)
            names=set(VARS+PORTS)
            for name,op,l,r in packet['source']:
                if name in names or op not in ('+','-','*'):raise ValueError('Malformed gate')
                for x in (l,r):
                    if not isinstance(x,int) and x not in names:raise ValueError('Forward/unknown input')
                names.add(name)
            outputs=[packet['output']] if 'output' in packet else [x for pair in packet['comparisons'] for x in pair]
            live={x for x in outputs if isinstance(x,str)}
            for name,op,l,r in reversed(packet['source']):
                if name not in live:raise ValueError('Dead gate')
                live.update(x for x in (l,r) if isinstance(x,str))
            if not set(VARS+PORTS)<=live:raise ValueError('Unused supplied port')
            if len(packet['source'])!=packet['ledger']['operations']:raise ValueError('Count mismatch')
            saved=json.loads((HERE/'circuits'/(packet['name']+'.json')).read_text())
            if saved!=packet:raise ValueError('Saved circuit differs from emitter')
    (HERE/'CHECK_RESULTS.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))

if __name__=='__main__':main()
