#!/usr/bin/env python3
"""Literal 11-positive-variable consistency equations; finite data only.

Arithmetic follows the paper in this package.  All four fixed leaves are
bound to one unchanged ProveIt package-31 tuple.  This emitter is not an
end-to-end formal proof of the imported machine/compiler calibration.
"""
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
VARIABLES = ['J','F','alpha','z','i','T','s','w','eta','zeta','t']
PORTS = ['beta','K0','MC','MF']

class Circuit:
    def __init__(self):
        self.rows = []
    def op(self, op, x, y, name=None):
        name = name or 'r' + str(len(self.rows)+1)
        self.rows.append([name,op,x,y])
        return name
    def add(self,x,y,name=None): return self.op('+',x,y,name)
    def sub(self,x,y,name=None): return self.op('-',x,y,name)
    def mul(self,x,y,name=None): return self.op('*',x,y,name)
    def sq(self,x,name=None): return self.mul(x,x,name)

def build(presentation='product', carrier='midpoint'):
    C=Circuit(); add,sub,mul,sq=C.add,C.sub,C.mul,C.sq
    qm1=mul('beta','J','qm1'); q=add(qm1,1,'q')
    q2=sq(q,'q2'); q3=mul(q,q2,'q3'); q4=sq(q2,'q4')
    U=mul(4,q4,'U')
    X=mul('w',q,'X'); Y=mul('s',q3,'Y'); E=mul(X,Y,'E')
    k=add('eta','zeta','k'); kY=mul(k,Y,'kY'); ell=mul(E,kY,'ell')
    A=add(mul(ell,add(ell,k)),1,'A')
    c=add(kY,'eta','c'); a=add(E,Y,'a'); ac=mul(a,c,'ac'); b0=add(X,ac,'b0')
    H=add(mul(4,a),3,'H'); Delta=add(sq(a),H,'Delta')
    c2=sq(c,'c2'); G=add(mul(Delta,c2),1,'G')
    qF=sub(q,'F','qF'); Cw=sub(qF,'alpha','Cw')
    R=add(mul(add(mul(qm1,qF),'alpha'),sub(q2,1)),
          mul(add('MC',mul(q,'MF')),'J'),'R')
    left=mul(add('K0','w'),Cw,'transport_left'); zq=mul('z',qm1,'zq')
    if presentation=='shifted_system':
        right=add('F',zq,'transport_right')
    else:
        Nt=sub(add(left,qF),zq,'Nt')
    I=mul('i',c2,'I'); I2=sq(I,'I2'); Dm1=mul(Delta,I2,'Dm1')
    D=add(Dm1,1,'D'); Q=mul(Delta,Dm1,'Q'); d=sub(Q,1,'d')
    v=mul(c,'T','v'); v2=sq(v,'v2'); b=add(c,mul(R,D),'b')
    IT=mul(I,'T','IT'); residue=sub(sub(k,R),1,'residue')
    if carrier=='midpoint':
        halfU=mul(2,q4,'halfU'); S=mul(U,H,'S')
        L=add(U,mul(S,IT),'L')
        W=add(mul(U,add(b0,mul(H,add('t',add(b,ell))))),
              mul(H,sub(mul(halfU,k),residue)),'W')
        normdegree=952
    elif carrier=='full':
        K=add(IT,1,'K'); S=mul(U,H,'S')
        L=add(U,mul(S,K),'L')
        delta=sub(mul(add(a,2),c),ell,'delta')
        W=sub(mul(U,add(b0,mul(H,add('t',add(b,delta))))),mul(H,residue),'W')
        normdegree=956
    else:
        raise ValueError(carrier)
    S2=sq(S,'S2'); dn=mul(d,mul(S2,A),'dn'); SQ=mul(S2,Q,'SQ')
    HP=mul(SQ,mul(D,v2),'HP'); HU=mul(SQ,sq(b),'HU')
    He=sub(add(HP,HU),S2,'He'); j=mul(4,mul(HP,HU),'j')
    W2=sq(W,'W2'); L2G=mul(sq(L),G,'L2G')
    Trace=mul(2,mul(d,add(W2,L2G)),'Trace')
    Knorm=sq(mul(d,sub(W2,L2G)),'Knorm')
    AA=mul(2,add(dn,He),'AA'); constant=sub(sq(sub(dn,He)),j,'constant')
    at=sub(Trace,AA,'at'); bt=sub(constant,Knorm,'bt')
    vbar=sub(mul(16,mul(dn,j)),mul(at,add(mul(at,Trace),mul(2,bt))),'vbar')
    ur=sub(sq(bt),mul(sq(at),Knorm),'ur')
    term1=mul(ur,sub(mul(Trace,vbar),ur),'term1'); term2=mul(Knorm,sq(vbar),'term2')
    p={'name':'eleven_'+carrier+'_'+presentation,
       'domain':'strictly positive integers','witnesses':VARIABLES,'fixed_numerals':PORTS,
       'source':C.rows,'carrier':carrier,'presentation':presentation,
       'paths_relative_to':'this generated JSON file',
       'coefficient_binding':'../../coefficients/ports.json',
       'proof':['../../report.tex','../PROOF.md'],
       'base_commit':'124c07c0b77a9e20e84676514d8b1ff78536ea3f'}
    if presentation in ('system','shifted_system'):
        p['comparisons']=[[left,right] if presentation=='shifted_system' else [Nt,1],[term1,term2]]
        p['residual_exact_degrees']=[2,normdegree];p['exact_degree']=normdegree
    else:
        N=sub(term2,term1,'N')
        if presentation=='product':
            p['output']=sub(mul(Nt,add(N,1)),1,'polynomial');p['exact_degree']=normdegree+2
        elif presentation=='sos':
            p['output']=add(sq(sub(Nt,1)),sq(N),'polynomial');p['exact_degree']=2*normdegree
        else: raise ValueError(presentation)
    audit(p)
    return p

def audit(p):
    known=set(VARIABLES+PORTS); degrees={v:1 for v in VARIABLES};degrees.update({v:0 for v in PORTS})
    for n,op,x,y in p['source']:
        if n in known or op not in ('+','-','*'): raise ValueError('invalid gate '+n)
        for u in (x,y):
            if not isinstance(u,int) and u not in known: raise ValueError('unbound '+u)
        dx=0 if isinstance(x,int) else degrees[x];dy=0 if isinstance(y,int) else degrees[y]
        degrees[n]=dx+dy if op=='*' else max(dx,dy);known.add(n)
    outputs=[p['output']] if 'output' in p else sum(p['comparisons'],[])
    live={x for x in outputs if isinstance(x,str)}
    for n,op,x,y in reversed(p['source']):
        if n not in live: raise ValueError('dead gate '+n)
        live.update(u for u in (x,y) if isinstance(u,str))
    if not set(VARIABLES+PORTS)<=live: raise ValueError('dead input')
    counts=Counter(r[1] for r in p['source'])
    p['ledger']={'operations':len(p['source']),'multiplications':counts['*'],
                 'additions_subtractions':counts['+']+counts['-'],'all_gates_and_inputs_live':True}
    p['syntactic_degree_bound']=max(degrees[x] if isinstance(x,str) else 0 for x in outputs)

def load_ports():
    path=HERE.parent/'coefficients'/'ports.json'
    binding=json.loads(path.read_text());out={}
    for entry in binding['ports']:
        packed=(path.parent/entry['file']).read_bytes();raw=gzip.decompress(packed)
        if hashlib.sha256(packed).hexdigest()!=entry['gzip_sha256']: raise ValueError('gzip hash')
        if hashlib.sha256(raw).hexdigest()!=entry['sha256']: raise ValueError('payload hash')
        if len(raw)!=entry['bytes']: raise ValueError('payload size')
        out[entry['port']]=int.from_bytes(raw,'little')
    return out

def evaluate(p,values,modulus=None):
    env=dict(values)
    for name,op,x,y in p['source']:
        x=x if isinstance(x,int) else env[x];y=y if isinstance(y,int) else env[y]
        result=x+y if op=='+' else x-y if op=='-' else x*y
        env[name]=result if modulus is None else result%modulus
    return env

def main():
    load_ports();out=HERE/'generated';out.mkdir(exist_ok=True);metrics=[]
    for car in ('midpoint','full'):
        for pres in ('product','system','shifted_system'):
            p=build(pres,car);(out/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
            metrics.append({k:p[k] for k in ('name','ledger','exact_degree','syntactic_degree_bound')})
    (out/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n')
    print(json.dumps(metrics,indent=2))

if __name__=='__main__': main()
