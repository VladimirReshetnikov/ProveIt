#!/usr/bin/env python3
"""Report108 fixture producer. Exact int/Fraction arithmetic; verifier is independent."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
MS=(1,2,3,5,8,16)
RS=('1/5','1/2','2/3','9/10','99/100','1')
DS=(1,2,3,5,9,17)
CS=('1/5','1/2','9/10')
VS=('1','2','17','1024')
CDS=(0,1,2,3,4,5,6,9,17)
PDS=(1,2,3,5,9)
PN=8
CN=16

def txt(x): return str(F(x))

def counts(d):
    state={(0,0):1}; result=[1,1]
    for n in range(2,CN+1):
        nxt=defaultdict(int)
        for (K,L),count in state.items():
            for j in range(K+2): nxt[K+int(j>L-d),j]+=count
        state=nxt; result.append(sum(state.values()))
    return result

def build():
    weak=json.loads((HERE/'weak_fixtures.json').read_text())
    shifted=[]
    for c in weak['frozen_cases']:
        M,r=c['M'],F(c['r']); lam=F(c['lambda']); p=list(map(F,c['p']))
        hc=list(map(F,c['h_scaled'])); cc=F(c['c_scaled'])
        for d in DS:
            h=d-1; rows=[]
            for l in range(M):
                lp=max(l-h,0); m=min(h,l)
                probs=[p[(j-lp)%M] for j in range(M)]
                drift=sum(probs[j]*(1-F((j-lp)%M,M)+F(int(j>=lp)*j,M*(M+int(j>=lp)))+F(m,M)) for j in range(M))
                rows.append({'l':l,'l_prime':lp,'m':m,'normalizer':txt(lam*r**(-m)),
                    'P':list(map(txt,probs)),'poisson_scaled':txt(cc+hc[lp]-hc[l]),'tracker_drift':txt(drift)})
            shifted.append({'M':M,'r':c['r'],'d':d,'rows':rows})
    capped=[]
    for M,d,st,vt in product(MS,DS,CS,VS):
        s,v=F(st),F(vt); h=d-1
        rows=[]
        for l in range(M):
            lp=max(l-h,0)
            rows.append(txt(s**(-l)*((1-s**lp)+v*(s**lp-s**M))/(1-s)))
        capped.append({'M':M,'d':d,'s':st,'v':vt,'row_sums':rows,'bound':txt((s**(-M)+v*s**(-h))/(1-s))})
    crossings=[]
    for M,tt,mode in product((2,3,5),('1/2','9/10'),('stays_capped','time_only','increment_only','combined','q0_successor')):
        P=2*M*(M+1)
        N={'stays_capped':P*(M+2),'time_only':P*(M-1),'increment_only':P*M+P//2,'combined':P*M,'q0_successor':0}[mode]
        L=N if mode=='increment_only' else max(N,P*M)+P
        exponents=[[txt(F((P-min(F(N,M+a),F(P)))*j)) for j in range(M)] for a in (0,1)]
        crossings.append({'M':M,'t':tt,'mode':mode,'p_exponent':P,'old_q_exponent':L,'new_q_exponent':N,'slope_drop_exponents':exponents,'crossing_bound_exponent':P+L-N})
    prefix=[]
    for d,k in product(PDS,range(1,PN+1)):
        all_by=[0]*k; legal_by=[0]*k
        for x in product(*(range(i) for i in range(1,k+1))):
            r=sum(x[i+1]<=x[i]-d for i in range(k-1)); all_by[r]+=1
            if all(x[i]<=1+sum(x[t+1]>x[t]-d for t in range(i-1)) for i in range(1,k)): legal_by[r]+=1
        prefix.append({'d':d,'k':k,'inversion_words_by_r':all_by,'legal_words_by_r':legal_by,'stars_bars':[comb(d*k*(r+1)+k-1,k) for r in range(k)]})
    return {'schema':'report108-sharpened-exact-v1','scope':'Finite integer/rational checks only; no analytic or uniform asymptotic estimate is certified.',
        'inventory':{'M':list(MS),'r':list(RS),'shift_d':list(DS),'cap_s':list(CS),'cap_v':list(VS),'cross_M':[2,3,5],'cross_t':['1/2','9/10'],'cross_modes':['stays_capped','time_only','increment_only','combined','q0_successor'],'count_d':list(CDS),'count_max_n':CN,'prefix_d':list(PDS),'prefix_max_n':PN},
        'shifted_cases':shifted,'capped_cases':capped,'crossing_cases':crossings,'recurrences':[{'d':d,'counts':counts(d)} for d in CDS],'prefix_cases':prefix}

if __name__=='__main__':
    (HERE/'fixtures.json').write_text(json.dumps(build(),indent=2)+'\n')
    print('fixtures.json written')
