"""Independent finite arithmetic/degree checks, not a compiler proof."""
import json, random
from pathlib import Path
from build_new import build, evaluate, WITNESSES, PORTS

HERE=Path(__file__).resolve().parent
def need(v,msg):
    if not v:raise AssertionError(msg)

def norm_independent(d):
    """Product of all conjugates in a rank-eight multiquadratic algebra."""
    G,A,D=d['G'],d['A'],d['D']
    def mul(x,y):
        z=[0]*8
        for i,v in enumerate(x):
            for k,w in enumerate(y):
                fac=(G if i&k&1 else 1)*(A if i&k&2 else 1)*(D if i&k&4 else 1)
                z[i^k]+=fac*v*w
        return z
    H2=d['H']**2
    ee=d['Q']*(d['D']*d['c']**2*d['T']**2+d['b']**2)-1
    B=2*d['Q']*d['c']*d['T']*d['b']
    out=[1]+[0]*7
    for sg in [-1,1]:
        for sa in [-1,1]:
            for sf in [-1,1]:
                root=[d['W'],-sg*d['L'],-sa*d['HM'],0,0,0,0,0]
                f=[d['d']*x for x in mul(root,root)]
                f[0]-=H2*ee;f[4]+=sf*H2*B
                out=mul(out,f)
    need(not any(out[1:]),'Conjugate product did not descend')
    return out[0]

def univariate(p,coeff,pr):
    """Full coefficient lists, including cancellations, over F_pr[t]."""
    def trim(x):
        while len(x)>1 and x[-1]==0:x.pop()
        return x
    def add(x,y,sgn):
        z=[0]*max(len(x),len(y))
        for i,a in enumerate(x):z[i]=a
        for i,b in enumerate(y):z[i]=(z[i]+sgn*b)%pr
        return trim(z)
    def mul(x,y):
        z=[0]*(len(x)+len(y)-1)
        for i,a in enumerate(x):
            if a:
                for j,b in enumerate(y):z[i+j]=(z[i+j]+a*b)%pr
        return trim(z)
    vals={k:[0,coeff[k]%pr] for k in WITNESSES}
    vals.update({k:[coeff[k]%pr] for k in PORTS})
    for n,o,l,r in p['source']:
        l=[l%pr] if isinstance(l,int) else vals[l]
        r=[r%pr] if isinstance(r,int) else vals[r]
        vals[n]=mul(l,r) if o=='*' else add(l,r,1 if o=='+' else -1)
    return {k:(len(v)-1,v[-1]) for k,v in vals.items()}

def check_leading(w,pr,seed):
    rng=random.Random(seed);coeff={k:rng.randrange(1,20) for k in WITNESSES}
    coeff.update(dict(zip(PORTS,[31,127,10,45])))
    val=univariate(build(w),coeff,pr)
    q0=31*coeff['J'];k0=coeff['eta']+coeff['zeta']
    if w=='economical':
        degree=1072;factor=2**32;wp=80;qp=656
    else:
        degree=1056;factor=2**46;wp=74;qp=646
    nlead=(factor*coeff['i']**48*k0**96*coeff['w']**wp*coeff['s']**176*q0**qp*(q0-coeff['F'])**16)%pr
    plead=nlead*(-coeff['h']*coeff['w']*coeff['s']*q0**4)*(coeff['w']*(q0-coeff['F']-coeff['alpha'])-coeff['z']*q0)%pr
    need(nlead!=0 and plead!=0,'Degenerate test assignment')
    need(val['N']==(degree,nlead),'Wrong full norm degree or leading coefficient: '+repr(val['N']))
    need(val['polynomial']==(degree+9,plead),'Wrong full product degree/leading coefficient')
    return {'prime':pr,'seed':seed,'norm':list(val['N']),'product':list(val['polynomial'])}

def structure(p):
    known=set(WITNESSES+PORTS)
    for n,o,a,b in p['source']:
        need(n not in known and o in '+-*','Invalid gate')
        need(all(isinstance(x,int) or x in known for x in (a,b)),'Invalid input')
        known.add(n)
    live=set([p['output']] if 'output'in p else [x for row in p['comparisons'] for x in row if isinstance(x,str)])
    for n,o,a,b in reversed(p['source']):
        if n in live:live.update(x for x in (a,b) if isinstance(x,str))
    need(known<=live,'Dead port or gate: '+repr(known-live))

def main():
    rng=random.Random(1065108);receipts=[]
    for weight in ['economical','cancellation1065']:
        p=build(weight);ps=build(weight,'shifted_system')
        for kind in ['product','system','shifted_system']:structure(build(weight,kind))
        for _ in range(50):
            v={n:rng.randrange(-3,5) for n in WITNESSES+PORTS};d=evaluate(p,v)
            need(d['N']==norm_independent(d),'Independent norm mismatch')
            need(d['N']%4 in (0,1),'Norm parity mismatch')
            shifted=evaluate(ps,v);old=evaluate(p,dict(v,z=v['z']+1))
            need(old['Nt']-1==shifted['trans0']-shifted['transport_rhs'],'Transport shift mismatch')
        receipts.append({'variant':weight,'exact_conjugate_products':50,'parity_cases':50,
            'transport_shift_cases':50,'all_gates_live':True,'full_univariate_degrees':[
                check_leading(weight,1000000007,43),check_leading(weight,1000000009,47)]})
    result={'checks':receipts,'scope':'Finite algebraic diagnostics; unbounded proof is separate.'}
    (HERE/'CHECK_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
