#!/usr/bin/env python3
"""Quadratic batching -> an explicit nine-natural-variable polynomial.

New source packing: Sidon weights and simultaneous zero-digit tests.
The Pell ratio and completed-square finalizer are transcribed from ProveIt
package 37 (MIT-0), commit 22e75dd6b87b1b199bb08c778d7cf075ae5aae08.
This finite circuit builder is not an end-to-end formal proof.
"""
from pathlib import Path
from itertools import product, combinations_with_replacement
from math import comb, factorial
from collections import defaultdict, Counter
import json

ROOT = Path(__file__).resolve().parent

def shifted_equations(parent):
    n = len(parent['variables'])
    result = []
    for eq in parent['equations']:
        out = defaultdict(int)
        for term in eq['terms']:
            a, c = term['powers'], term['coefficient']
            active = [(i,e) for i,e in enumerate(a[:n]) if e]
            for choices in product(*(range(e+1) for _,e in active)):
                b = [0]*n + a[n:]
                cc = c
                for (i,e),f in zip(active,choices):
                    b[i] = f
                    cc *= comb(e,f)
                out[tuple(b)] += cc
        result.append({a:c for a,c in out.items() if c})
    return result

def prepare_source(parent, weights):
    n = len(parent['variables'])
    assert len(weights)==n+1 and weights[0]==0
    assert len({weights[i]+weights[j] for i,j in combinations_with_replacement(range(n+1),2)}) == (n+1)*(n+2)//2
    a, M = weights[1:], max(weights)
    D = 4*M+1
    rows = shifted_equations(parent)
    recipes = {}
    data = []
    bound = defaultdict(int)
    for j,row in enumerate(rows):
        grouped = defaultdict(lambda: defaultdict(int))
        for powers,c in row.items():
            ex, pp = powers[:n], powers[n:]
            fac = factorial(2-sum(ex))
            for e in ex: fac *= factorial(e)
            pos = 2*M-sum(x*y for x,y in zip(a,ex))
            assert pos>=0
            grouped[pos][pp] += c*fac
        encoded=[]
        for exponent,recipe in sorted(grouped.items()):
            terms = tuple(sorted((p,c) for p,c in recipe.items() if c))
            for pp,c in terms: bound[pp] += abs(c)
            if len(terms)==1 and not any(terms[0][0]):
                leaf=terms[0][1]
            else:
                if terms not in recipes: recipes[terms]='c%03d'%len(recipes)
                leaf=recipes[terms]
            encoded.append({'exponent':exponent,'coefficient':leaf})
        data.append({'row':j,'shift':j*D,'target':j*D+2*M,'terms':encoded})
    return {'n':n,'m':len(rows),'M':M,'stride':D,'length':len(rows)*D,
            'weights':weights,'rows':data,
            'fixed_recipes':{name:[{'powers':list(pp),'coefficient':c} for pp,c in terms] for terms,name in recipes.items()},
            'coefficient_bound_C':{'constant':1,'positive_terms':[{'powers':list(pp),'coefficient':c} for pp,c in sorted(bound.items())]},
            'radix_multiplier':'kappa = 2^bit_length(2048*C), hence kappa > 2048*C',
            'parent_variables':parent['variables'],'parent_ports':parent['constants']}

class DAG:
    def __init__(self):
        self.nodes=[]; self.cache={}; self.known={}; self.pows={}; self.names={}
    def node(self,obj):
        key=tuple(obj.items())
        if key not in self.cache:
            self.cache[key]=len(self.nodes); self.nodes.append(obj)
        return self.cache[key]
    def const(self,v):
        i=self.node({'kind':'literal','value':v}); self.known[i]=v; return i
    def fixed(self,n): return self.node({'kind':'fixed','name':n})
    def var(self,n): return self.node({'kind':'variable','name':n})
    def op(self,k,a,b):
        x,y=self.known.get(a),self.known.get(b)
        if x is not None and y is not None:
            return self.const({'add':lambda:x+y,'sub':lambda:x-y,'mul':lambda:x*y}[k]())
        if k=='add':
            if x==0:return b
            if y==0:return a
        if k=='sub':
            if y==0:return a
            if a==b:return self.const(0)
        if k=='mul':
            if x==0 or y==0:return self.const(0)
            if x==1:return b
            if y==1:return a
        if k in ('add','mul') and a>b:a,b=b,a
        return self.node({'kind':k,'left':a,'right':b})
    def add(self,*args):
        a=self.const(0)
        for b in args:a=self.op('add',a,b)
        return a
    def mul(self,*args):
        a=self.const(1)
        for b in args:a=self.op('mul',a,b)
        return a
    def sub(self,a,b):return self.op('sub',a,b)
    def pow(self,a,e):
        assert isinstance(e,int) and e>=0
        if (a,e) not in self.pows:
            if e==0:r=self.const(1)
            elif e==1:r=a
            else:
                h=self.pow(a,e//2); r=self.mul(h,h)
                if e%2:r=self.mul(r,a)
            self.pows[a,e]=r
        return self.pows[a,e]
    def geom(self,a,n):
        if n==0:return self.const(0)
        if n==1:return self.const(1)
        h=n//2
        r=self.mul(self.geom(a,h),self.add(self.const(1),self.pow(a,h)))
        return self.add(r,self.pow(a,2*h)) if n%2 else r
    def save(self,n,a):self.names[n]=a; return a
    def finish(self,root,variables,domain):
        live=set(); todo=[root]
        while todo:
            i=todo.pop()
            if i in live:continue
            live.add(i); x=self.nodes[i]
            if x['kind'] in ('add','sub','mul'):todo.extend((x['left'],x['right']))
        ids={old:new for new,old in enumerate(sorted(live))}
        nodes=[]
        for i in sorted(live):
            x=dict(self.nodes[i])
            if x['kind'] in ('add','sub','mul'):x['left'],x['right']=ids[x['left']],ids[x['right']]
            nodes.append(x)
        counts=Counter(x['kind'] for x in nodes)
        return {'variables':variables,'domain':domain,'nodes':nodes,'output':ids[root],
                'named_nodes':{n:ids[i] for n,i in self.names.items() if i in ids},
                'operations':sum(counts[k] for k in ('add','sub','mul')),
                'operation_counts':{k:counts[k] for k in ('add','sub','mul')},
                'model':'Binary +,-,*; each fixed-coefficient multiplication and squaring is charged. Fixed recipes have degree zero.'}

def source_body(d, source, b, g):
    A,M,S,P,c = d.add,d.mul,d.sub,d.pow,d.const
    mx,dl,n = source['M'],source['stride'],source['length']
    B=d.save('B',M(d.fixed('kappa'),P(b,2)))
    Q=d.save('code_block',P(B,mx+1))
    ell=d.save('ell',A(*(P(B,e) for e in source['weights'][1:])))
    stage=P(B,dl)
    rowvalues=[]
    for row in source['rows']:
        # Sparse Horner within each quadratic-coefficient block.
        terms=row['terms']
        v=c(0); previous=terms[-1]['exponent']
        for term in reversed(terms):
            e=term['exponent']; leaf=term['coefficient']
            v=A(M(v,P(B,previous-e)),c(leaf) if isinstance(leaf,int) else d.fixed(leaf))
            previous=e
        rowvalues.append(M(v,P(B,previous)))
    e=c(0)
    for value in reversed(rowvalues):e=A(value,M(stage,e))
    e=d.save('coefficient_kernel',e)
    lam=d.save('background',d.geom(B,n))
    zm=d.save('zero_mask',M(P(B,2*mx),d.geom(stage,source['m'])))
    s0=d.save('S0',A(M(c(2),P(A(c(1),g),2),e),M(B,lam)))
    ss=d.save('S',A(g,M(Q,s0)))
    tt=d.save('T',A(S(S(Q,c(1)),M(S(b,c(1)),ell)),M(Q,S(B,c(2)),zm)))
    nn=d.save('N',P(B,n+mx+2))
    rr=d.save('R',A(M(ss,S(P(nn,2),nn)),M(A(tt,c(1)),S(P(nn,2),c(1)))))
    cap=d.save('Gcap',M(c(32),b,P(B,mx)))
    return rr,nn,cap

def make_nine(source, positive=False, certificate=False):
    d=DAG(); A,M,S,P,c=d.add,d.mul,d.sub,d.pow,d.const
    names=(['epsilon_plus','g','h','s','w','phi_plus','i','j','n_plus'] if positive else
           ['epsilon','g0','h0','s0','w0','phi','i0','j0','n'])
    v=[d.var(n) for n in names]
    b=d.save('b',A(v[0],c(1 if positive else 2)))
    g,h,s,w,ii,jj=[v[k] if positive else A(v[k],c(1)) for k in (1,2,3,4,6,7)]
    phi=S(v[5],c(1)) if positive else v[5]
    nv=S(v[8],c(1)) if positive else v[8]
    R,N,Gcap=source_body(d,source,b,g)
    U=d.save('U',M(P(N,2),w)); Y=d.save('Y',M(P(N,2),s))
    MM=M(R,Y); PP=d.save('P',M(c(2),P(MM,2),U))
    K=d.save('K',A(R,c(1),M(h,S(PP,c(1)))))
    AA=d.save('A',M(MM,A(U,c(1))))
    bp=A(M(c(2),R),c(1)); ww=d.save('Wsmall',M(b,w))
    CC=d.save('C',A(bp,ww,phi)); JJ=d.save('J',S(M(c(4),AA),c(5)))
    QQ=d.save('Q',S(M(c(3),ww,CC),M(c(2),S(P(ww,2),c(1)))))
    DD=d.save('D',A(M(S(P(AA,2),c(1)),P(CC,2)),c(1)))
    EE=d.save('E',M(ii,JJ,DD,P(CC,2)))
    FF=d.save('F',A(M(S(P(AA,2),c(1)),P(EE,2)),c(1)))
    GP=d.save('Gp',A(AA,M(FF,S(A(M(CC,DD),c(1)),AA))))
    HH=d.save('H',A(bp,M(jj,CC)))
    II=d.save('I',A(M(S(P(GP,2),c(1)),P(HH,2)),c(1)))
    a0=d.save('a0',A(S(P(M(PP,K),2),P(K,2)),c(1)))
    a1=d.save('a1',M(DD,FF,II))
    u=d.save('divisor',M(JJ,FF)); vv=d.save('dividend',A(M(QQ,FF),M(JJ,S(HH,CC))))
    md=d.save('division_bound',A(P(QQ,2),P(S(HH,CC),2),c(1)))
    margin=d.save('margin',S(S(M(P(K,2),Gcap),M(c(4),P(S(CC,M(K,Y)),2),Gcap)),M(c(8),g,P(K,2))))
    r=d.save('r_positive',A(ww,phi)); sigma=d.save('sigma',M(Y,A(U,c(1))))
    MD=d.save('majorant_D',A(M(AA,CC),M(sigma,P(A(r,c(1)),2)),c(1)))
    MF=d.save('majorant_F',A(M(AA,EE),c(1)))
    CH=A(M(CC,HH),P(r,2))
    MI=d.save('majorant_I',A(S(M(FF,A(M(DD,CH),M(c(2),P(HH,2)),P(AA,2))),P(AA,2)),c(1)))
    V0=d.save('V0',A(M(PP,K),c(1))); V1=d.save('V1',A(M(MD,MF,MI),c(1)))
    omg=d.save('Omega',M(u,S(M(c(2),margin),c(1))))
    theta=d.save('Theta',S(A(M(u,A(nv,md)),vv),M(omg,A(M(c(2),md),M(V0,V1)))))
    if certificate:
        t=M(sigma,P(A(r,c(1)),2))
        deltaD=d.save('deltaD',A(M(c(2),AA,CC,t),P(t,2),M(c(2),AA,CC),M(c(2),t),P(CC,2)))
        deltaF=d.save('deltaF',A(M(c(2),AA,EE),P(EE,2)))
        deltaG=d.save('MI_minus_GH',A(M(FF,DD,P(r,2)),M(c(2),FF,P(HH,2)),M(S(FF,c(1)),P(AA,2)),c(1),S(c(0),M(FF,HH)),M(AA,S(FF,c(1)),HH)))
        deltaI=d.save('deltaI',S(A(M(deltaG,A(MI,M(GP,HH))),P(HH,2)),c(1)))
        deltaV=d.save('deltaV',A(M(deltaD,P(MF,2),P(MI,2)),M(DD,deltaF,P(MI,2)),M(DD,FF,deltaI),M(c(2),MD,MF,MI),c(1)))
        e0=d.save('E0',S(A(M(u,A(nv,md)),vv),M(c(2),omg,md)))
        inner=d.save('inner',S(A(P(e0,2),S(c(0),M(c(2),e0,omg,V0,V1)),M(P(omg,2),P(V0,2),deltaV)),M(P(omg,2),a0)))
    else:
        inner=d.save('inner',S(P(theta,2),M(P(omg,2),A(a0,M(P(V0,2),a1)))))
    out=d.save('output',S(P(inner,2),M(c(4),P(omg,4),P(V0,2),a0,a1)))
    result=d.finish(out,names,'positive integers' if positive else 'nonnegative integers')
    result['construction']='B2 quadratic batching with 22 coefficient targets; Jones ratio; package37 signed finalizer'
    result['source_parameters']={k:source[k] for k in ('n','m','M','stride','length')}
    result['certificate_expansion']=certificate
    return result

def main():
    parent=json.loads((ROOT/'parent31.json').read_text())
    weights=json.loads((ROOT/'weights.json').read_text())['weights_with_zero']
    source=prepare_source(parent,weights)
    (ROOT/'source_data.json').write_text(json.dumps(source,indent=2)+'\n')
    out=ROOT/'generated';out.mkdir(exist_ok=True)
    for positive in (False,True):
        body=make_nine(source,positive)
        name='nine_positive' if positive else 'nine_natural'
        (out/(name+'.json')).write_text(json.dumps(body,separators=(',',':'))+'\n')
        print(name,body['operations'],body['operation_counts'])
    cert=make_nine(source,False,True)
    (out/'nine_degree_certificate.json').write_text(json.dumps(cert,separators=(',',':'))+'\n')

if __name__=='__main__':main()
