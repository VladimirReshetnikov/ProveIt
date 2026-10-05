from functools import lru_cache
from fractions import Fraction
from math import factorial,prod
import json
from pathlib import Path

def shifted(lam):
    a=tuple(x for x in lam if x)
    if any(a[i]<=a[i+1] for i in range(len(a)-1)):return 0
    v=Fraction(factorial(sum(a)),prod(factorial(x) for x in a))
    for i in range(len(a)):
        for j in range(i+1,len(a)):v*=Fraction(a[i]-a[j],a[i]+a[j])
    if v.denominator!=1:raise RuntimeError(('noninteger',lam,v))
    return v.numerator

def graph_paths(m,n):
    @lru_cache(None)
    def count(lam):
        if not any(lam):return 1
        out=0
        for i in range(m):
            if not lam[i]:continue
            x=list(lam);x[i]-=1
            if any(x[j]<x[j+1] for j in range(m-1)):continue
            if any(0<x[j]==x[j+1]<n for j in range(m-1)):continue
            out+=count(tuple(x))
        return out
    total=count((n,)*m)
    def states(prefix,left,maxval):
        if len(prefix)==m:
            if left==0:yield tuple(prefix)
            return
        for a in range(min(maxval,left),-1,-1):
            yield from states(prefix+[a],left-a,a)
    checks=0;middle=0;boundary=0
    for lam in states([],n,n):
        if any(0<lam[j]==lam[j+1]<n for j in range(m-1)):continue
        bar=tuple(n-x for x in lam[::-1]);v=count(lam)*count(bar);middle+=v
        if 0<lam[-1] and lam[0]<n:
            if count(lam)!=shifted(lam) or count(bar)!=shifted(bar):raise RuntimeError(('hook mismatch',m,n,lam))
            checks+=1
        else:boundary+=v
    if middle!=total:raise RuntimeError(('branching',m,n,middle,total))
    return total,checks,boundary
known=[1,1,16,985,141696,36372976,14083834704,7372392431849,4848332563899256,3808369342900073856,3447336241467721584256,3503140094024746011745456,3918646197894288330216058576,4753102567048482059557067412816,6178133154985813161258658378449616]
known4=[1,1,8,169,6392,352184,25097600,2152061145,212012802584,23263015359672,2781709560836960,356806123331844056,48516442013911012288,6930091952294051922080,1032505514388962439665280]
rows=[]
for m in range(2,6):
    for n in range(1,16):
        a,c,b=graph_paths(m,n)
        if m==5 and a!=known[n-1]:raise RuntimeError(('OEIS181199',n,a,known[n-1]))
        if m==4 and a!=known4[n-1]:raise RuntimeError(('OEIS181198',n,a,known4[n-1]))
        rows.append({'m':m,'n':n,'count':a,'interior_hook_checks':c,'boundary_through_count':b})
result={'passed':True,'instances':len(rows),'OEIS_terms':len(known)+len(known4),'interior_hook_checks':sum(x['interior_hook_checks'] for x in rows),'records':rows}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print({k:v for k,v in result.items() if k!='records'})
