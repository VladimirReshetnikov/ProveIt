#!/usr/bin/env python3
"""Independent exact 13-group replay and complete three-stage schedule audit.

Standard library, explicit exceptions, exhaustive 132^3 support triples.
The support traversal differs from the producing checker's BFS order.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations,permutations
from math import lcm,isqrt
import json,time

def require(ok,msg):
    if not ok:raise RuntimeError(msg)

root=Path(__file__).resolve().parent
data=json.loads((root/'anchored_thirteen_certificate.json').read_text())
a,o,e=Q(321333,1000000),Q(2371553,1000000),Q(1,1000000)
c=(o-1)/2
k0,k1=Q(11,20),Q(3,5)
y0,y1=Q(2066134,1000000)+e,Q(2092631,1000000)+e
slope=(y1-y0)/(k1-k0)
k=(1+c-y0+slope*k0)/(slope-c)
A=1+c*(1+k)
require(k0<k<k1 and A==y0+slope*(k-k0),'interpolated anchor')
w=(A-2-e)/(k-a);v=1+e-a*w;d=1+e/2
require(0<w<v<1<d and 0<c<1,'sorted support coefficients')
L=lcm(d.denominator,v.denominator,w.denominator,c.denominator)
triples=sorted(set(permutations((int(d*L),int(d*L),0)))|
               set(permutations((L,int(v*L),int(w*L))))|
               set(permutations((L,int(c*L),int(c*L)))))
require(L==data['scale'] and list(map(list,triples))==data['triples'],'coefficient data')
require(list(map(str,(d,v,w,c)))==data['coefficients'],'coefficient fractions')
pp=[[[0,1,2,3,4],[5,6,7,8],[9,10,11,12]],
    [[12,10,1,6,4],[9,0,3,8],[5,2,7,11]],
    [[0,8,11,12,1],[7,10,4,3],[5,2,6,9]]]
require(pp==data['plans'],'inherited thirteen-group plans')
edges=list(combinations(range(13),2));menus=[]
for plan in pp:
    operations=[]
    for block in plan:
        stack=[(block,False)]
        while stack:
            b,ready=stack.pop()
            if len(b)==1:continue
            cut=len(b)//2;left,right=b[:cut],b[cut:]
            if not ready:stack.extend([(b,True),(right,False),(left,False)])
            else:operations.append([left,right,[x for x in range(13) if x not in b]])
    operations.append(plan);rows=[]
    for op in operations:
        labels=[next(j for j,part in enumerate(op) if x in part) for x in range(13)]
        for triple in triples:
            coeff={(0,1):triple[0],(0,2):triple[1],(1,2):triple[2]}
            rows.append(tuple(0 if labels[x]==labels[y] else coeff[tuple(sorted((labels[x],labels[y])))] for x,y in edges))
    require(len(rows)==132,'support count');menus.append(rows)

def norm(u):return sum(x*x for x in u)
n=[[norm(u) for u in menu] for menu in menus]
cross={}
for i,j in combinations(range(3),2):
    cross[i,j]=[[norm(tuple(x+y for x,y in zip(u,z)))-n[i][a]-n[j][b]
                 for b,z in enumerate(menus[j])] for a,u in enumerate(menus[i])]
M=-1;chosen=None;ties=0;checks=0;start=time.time()
for ia in range(132):
    for ib in range(132):
        base=n[0][ia]+n[1][ib]+cross[0,1][ia][ib]
        for ic in range(132):
            value=base+n[2][ic]+cross[0,2][ia][ic]+cross[1,2][ib][ic]
            checks+=1
            if value>M:M,chosen,ties=value,(ia,ib,ic),1
            elif value==M:ties+=1
require(checks==132**3==data['choices_checked'],'all triples checked')
require(M==data['maximum_squared_norm'] and ties==data['maximizer_count'],'exact maximum')
require(norm(tuple(sum(menus[i][b][j] for i,b in enumerate(chosen)) for j in range(78)))==M,'direct witness')
beta13=Q(2*M,L*L*9*169)
require(beta13==Q(57151369949899,169000000000000) and str(beta13)==data['beta_squared'],'thirteen-stage fraction')

eta0,eta1,eta2,q=Q(301,20000),Q(119,10000),Q(1549,324000),Q(4,9)
require(eta0+eta1+eta2/(1-q)==Q(8,225),'total retained fraction')
require(10**1000<2**3322 and 13**1000<2**3701 and 7**100<2**281,'strict log upper bounds')
gaps=[1-Q(9,10)-2*eta0*Q(3322,1000),
      1-Q(9,10)-(eta0+eta1)*Q(3701,1000),
      1-Q(9,10)-Q(8,225)*Q(281,100)]
require(gaps==[Q(39,5000000),Q(5161,20000000),Q(1,11250)],'packing margins')
require(Q(8,225)*(1+2*Q(3701,1000))<1,'fresh-side and packet gates')
require(9**3<4**3*3**4,'positive depth taper exponent')
require(Q(3,4)>Q(632,1225),'unchanged seven-group tail dominance')

def arctan(d,n):
    s=sum((Q((-1)**j,(2*j+1)*d**(2*j+1)) for j in range(n)),Q(0))
    t=s+Q((-1)**n,(2*n+1)*d**(2*n+1))
    return min(s,t),max(s,t)
pa,pb=arctan(5,30);pc,pd=arctan(239,10)
pi=(16*pa-4*pd,16*pb-4*pc)
ll=sum((Q(2,(2*j+1)*3**(2*j+1)) for j in range(60)),Q(0))
ln=(ll,ll+Q(2,121*3**121)*Q(9,8))
def root_interval(x):
    den=10**30;r=isqrt(x.numerator*den*den//x.denominator)
    require(Q(r*r,den*den)<=x<Q((r+1)**2,den*den),'sqrt interval')
    return Q(r,den),Q(r+1,den)
def coefficient(rs):
    roots=[root_interval(x) for x in rs]
    return pi[0]/ln[1]*sum((x[0] for x in roots),Q(0)),pi[1]/ln[0]*sum((x[1] for x in roots),Q(0))
beta10=Q(5835847444309,18750000000000)
C0=coefficient([2*beta10/eta0])
C1=coefficient([Q(7200,301),2*beta13/(25*eta1)])
Ci=coefficient([Q(7200,301),Q(19200,20111),Q(77760,261781)])
old=coefficient([2*Q(15952347164548384057,49000000000000000000)/eta0])
require(C0[0]>C1[1] and C0[0]>Ci[1],'root controls complete recurrence')
require(C0[1]<Q(29149,1000),'safe eventual coefficient29.149')
require(C0[0]>Q(29148921,1000000) and C0[1]<Q(29148922,1000000),'narrow root interval')
require(old[0]>C0[1],'strict baseline comparison')
out={'status':'PASS','support_count':396,'support_triples_checked':checks,
     'support_order':'independent postorder traversal','own_witness':chosen,'maximum_squared_norm':M,
     'maximizer_count':ties,'beta13_squared':str(beta13),'beta10_squared':str(beta10),
     'packing_margins':list(map(str,gaps)),
     'coefficient_intervals':{k:list(map(str,b)) for k,b in [('root',C0),('depth_one',C1),('tail',Ci),('old_root',old)]},
     'coefficient_displays':{k:float(b[0]) for k,b in [('root',C0),('depth_one',C1),('tail',Ci),('old_root',old)]},
     'safe_eventual_time_and_space_coefficient':'29.149','elapsed_seconds':time.time()-start,
     'scope':'Independent finite support and schedule audit; imported analytic and arithmetic algorithms remain dependencies.'}
(root/'independent_thirteen_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='coefficient_intervals'},indent=2))
