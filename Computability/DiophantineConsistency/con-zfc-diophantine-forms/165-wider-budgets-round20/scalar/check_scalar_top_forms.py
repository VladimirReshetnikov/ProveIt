#!/usr/bin/env python3
"""Independent highest-form check against the literal Round 20 scalar DAGs.

No producer/checker imports. Sparse integer arithmetic, with all six ports
formal degree-zero indeterminates. Any unresolved leading cancellation is
an explicit failure, not a guessed degree.
"""
from pathlib import Path
import argparse, hashlib, json

VARIABLES=['j','C','z','h','r','v','w','T','c','n','s']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
NAMES=VARIABLES+PORTS
ZERO=(0,)*len(NAMES)

def add(a,b,sign=1):
    out=a.copy()
    for m,c in b.items(): out[m]=out.get(m,0)+sign*c
    return {m:c for m,c in out.items() if c}

def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            e=tuple(x+y for x,y in zip(m,n))
            out[e]=out.get(e,0)+c*d
    return {m:c for m,c in out.items() if c}

def scale(a,c): return {m:c*v for m,v in a.items() if c*v}
def power(a,k):
    out={ZERO:1}
    for _ in range(k): out=mul(out,a)
    return out
def variable(n):
    m=list(ZERO);m[NAMES.index(n)]=1
    return {tuple(m):1}
def degree(a): return max((sum(m[:len(VARIABLES)]) for m in a),default=-1)
def need(ok,msg):
    if not ok: raise ValueError(msg)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--graph',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    raw=args.graph.read_bytes();graph=json.loads(raw);nodes=graph['nodes'];memo={}
    def top(i):
        if i in memo:return memo[i]
        node=nodes[i];op=node[0]
        if op in ('variable','coefficient'):out=variable(node[1])
        elif op=='integer':out={ZERO:node[1]} if node[1] else {}
        else:
            a,b=top(node[1]),top(node[2])
            if op=='mul':out=mul(a,b)
            else:
                need(op in ('add','sub'),'known operation')
                da,db=degree(a),degree(b)
                if da>db:out=a
                elif db>da:out=b if op=='add' else scale(b,-1)
                else:
                    out=add(a,b,1 if op=='add' else -1)
                    need(bool(out) or not(a or b),'unresolved leading cancellation at '+str(i))
        memo[i]=out;return out
    vv={n:variable(n) for n in NAMES}
    q0=scale(mul(vv['beta'],vv['j']),6);w0=scale(vv['w'],12)
    x0=mul(q0,w0);a0=mul(x0,vv['v']);ell0=mul(x0,power(vv['v'],2))
    f0=add(mul(w0,vv['C']),mul(vv['z'],q0),-1)
    r0=scale(mul(power(q0,3),f0),-1)
    k0=add(r0,mul(vv['h'],ell0)) if graph['rebased'] else r0
    def product(*xs):
        out={ZERO:1}
        for x in xs:out=mul(out,x)
        return out
    r,c,t,s=[vv[n] for n in ('r','c','T','s')]
    qstar=product(r,power(a0,7),power(c,6))
    vstar=scale(product(power(r,2),power(a0,8),power(c,10),t),4)
    pstar=product(power(q0,4),power(ell0,2),power(k0,3),s)
    sstar=scale(product(s,r,a0,power(q0,15)),128)
    t0=add(add(power(product(vv['cone_A'],vv['v'],f0),2),power(scale(product(q0,power(vv['v'],2)),2),2)),power(q0,6))
    guard=scale(product(power(k0,2),t0 if graph['rebased'] else power(q0,8)),-1)
    ptop=scale(product(power(ell0,4),power(k0,6),power(s,2),t0),-1) if graph['rebased'] else scale(power(pstar,2),-1)
    zc0=add(scale(product(a0,power(q0,3),t),8),scale(product(power(q0,3),power(x0,2)),4),-1)
    expected={
      'q':q0,'W':w0,'X':x0,'a':a0,'F':f0,'R':r0,'k':k0,
      'A':a0,'Delta':power(a0,2),'Dm':product(power(a0,2),power(c,2)),
      'B':product(r,power(a0,3),power(c,2)),
      'U':product(r,power(a0,2),power(c,4)),
      'Df':product(r,power(a0,5),power(c,6)),
      'Q':qstar,'delta':qstar,'V':vstar,'Cy':product(qstar,power(vstar,2)),
      'Dt':product(power(ell0,2),power(k0,2)),
      'Budget':guard,
      'P':ptop,'S':sstar,'zc':zc0,'Ac':power(zc0,5)
    }
    results=[]
    for name,form in expected.items():
        actual=top(graph['named_registers'][name]);need(actual==form,'highest homogeneous form '+name)
        results.append({'register':name,'degree':degree(form),'highest_support':len(form)})
    receipt={'status':'pass','graph_sha256':hashlib.sha256(raw).hexdigest(),
      'method':'independent sparse highest-homogeneous arithmetic; no unresolved cancellation',
      'registers':results,'P_highest_is_negative_sum_of_squares':True,'rebased':graph['rebased'],
      'scope':'Finite leading-form inputs to fixed-frame degree-floor proof, not its logical calibration.'}
    args.output.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))

if __name__=='__main__':main()
