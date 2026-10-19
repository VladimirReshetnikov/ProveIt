#!/usr/bin/env python3
"""Native syntax regressions, not an infinite-schema soundness proof."""
from pathlib import Path
from functools import cache
from math import isqrt
import json
P=lambda a,b:(a+b)*(a+b+1)//2+b
F=('rel',0,0)
I=lambda p,q:('imp',p,q)
Q=lambda i,p:('all',i,p)
N=lambda p:I(p,F)
C=lambda p,q:N(I(p,N(q)))
X=lambda i,p:N(Q(i,N(p)))
R=lambda i,j:('rel',i,j)
def need(b,m):
 if not b:raise ValueError(m)
@cache
def enc(f):
 t,a,b=f
 if t=='rel':return 4*P(a,b)+1
 if t=='eq':return 4*P(a,b)+3
 if t=='imp':return 4*P(enc(a),enc(b))
 if t=='all':return 4*P(a,enc(b))+2
 raise ValueError(t)
def unpair(n):
 s=(isqrt(8*n+1)-1)//2;b=n-s*(s+1)//2
 return s-b,b
@cache
def dec(n):
 if n==0:return I(F,F)
 a,b=unpair(n//4);t=n%4
 if t==0:return I(dec(a),dec(b))
 if t==1:return R(a,b)
 if t==2:return Q(a,dec(b))
 return ('eq',a,b)
@cache
def labels(f):
 if f[0] in ('rel','eq'):return frozenset(f[1:])
 if f[0]=='imp':return labels(f[1])|labels(f[2])
 return frozenset((f[1],))|labels(f[2])
def E(a,b):
 k=4*P(a,b)+3
 def B(p,q):return C(I(p,q),I(q,p))
 return C(Q(k,B(R(k,a),R(k,b))),Q(k,B(R(a,k),R(b,k))))
def tr(f):
 if f==('bot',):return F
 if f[0]=='eq':return E(*f[1:])
 if f[0]=='rel':return f
 if f[0]=='imp':return I(tr(f[1]),tr(f[2]))
 return Q(f[1],tr(f[2]))
def G(a,b,c,f):return X(c,C(Q(a,I(R(a,b),Q(b,I(f,X(b,C(f,R(b,c))))))),Q(b,I(R(b,c),X(a,f)))))
def CP(a,b,c):return X(b,C(Q(a,I(R(a,b),C(X(c,C(Q(b,I(Q(c,I(R(c,b),R(c,a))),R(b,c))),R(c,b))),Q(c,I(R(c,a),R(c,b)))))),R(c,b)))
def names(d,i):
 if d==0:return 2*i+1
 return 2*(d-1) if i==0 else names(d-1,i-1)
def named(f,d=0):
 t=f[0]
 if t=='mem':return R(names(d,f[1]),names(d,f[2]))
 if t=='bot':return F
 if t=='imp':return I(named(f[1],d),named(f[2],d))
 if t=='and':return C(named(f[1],d),named(f[2],d))
 if t=='all':return Q(2*d,named(f[1],d+1))
 if t=='ex':return X(2*d,named(f[1],d+1))
 raise ValueError(t)
need(enc(F)==1,'F is1');need(enc(I(F,F))==16,'explicit identity is16');need(enc(dec(0))==16,'truth alias not inverse')
for n in range(1,65536):need(all(i<n for i in labels(dec(n))),('native freshness',n))
need(tr(CP(2,3,1))==CP(2,3,1),'exact CP unchanged')
irr=Q(0,I(R(0,0),('bot',)))
need(tr(irr)==Q(0,I(F,F)),'IR translates generalized identity')
matrices=[('bot',),('mem',0,1),('imp',('mem',0,1),('mem',1,2)),('all',('mem',0,1)),('ex',('and',('mem',0,1),('mem',1,0)))]
rows=[]
for phi in matrices:
 f=named(phi);p=I(I(f,f),f);c=enc(p);literal=G(1,3,c,p)
 need(c>3 and c not in labels(p),'exact actual output code is fresh')
 need(tr(literal)==literal,'matrix and output code unchanged')
 rows.append({'input':repr(phi),'matrix_code_bit_length':c.bit_length(),'code_gate_and_literal_preservation':True})
r={'valid':True,'positive_native_codes_checked':65535,'F':1,'truth_alias':{'dec0':'Rel00 -> Rel00','enc_dec0':16,'native_imp00':0},'literal_CP_unchanged':True,'IR_translation':'All0(F -> F)','selected_equality_free_GIC':rows,'scope':'Finite regressions; strong-induction freshness and structural translation preservation are proved in AUDIT.md.'}
Path(__file__).with_name('native_edge_results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
