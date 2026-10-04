#!/usr/bin/env python3
"""Fresh exact algebra only. No trajectory, event selection, or old imports.

This file proves polynomial identities in an explicit polynomial ring and checks
finite rational matrix fixtures. It never advances a physical configuration.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

NV = 5  # v, a, b, S, t
class P:
    def __init__(self, x=0):
        if isinstance(x, P): self.d = dict(x.d)
        elif isinstance(x, dict): self.d = {m: Q(c) for m,c in x.items() if c}
        else: self.d = {(0,)*NV:Q(x)} if x else {}
    def __add__(self, y):
        d=dict(self.d)
        for m,c in P(y).d.items(): d[m]=d.get(m,Q(0))+c
        return P(d)
    __radd__=__add__
    def __neg__(self): return P({m:-c for m,c in self.d.items()})
    def __sub__(self,y): return self+-P(y)
    def __rsub__(self,y): return P(y)+-self
    def __mul__(self,y):
        d={}
        for m,c in self.d.items():
            for n,e in P(y).d.items():
                k=tuple(i+j for i,j in zip(m,n));d[k]=d.get(k,Q(0))+c*e
        return P(d)
    __rmul__=__mul__
    def __truediv__(self,y): return self*Q(1,Q(y))
    def __eq__(self,y): return self.d==P(y).d
    def evaluate(self, vals):
        return sum((c*prod(v**e for v,e in zip(vals,m)) for m,c in self.d.items()),Q(0))
    def terms(self): return [{"powers":list(m),"coefficient":str(c)} for m,c in sorted(self.d.items())]

def prod(xs):
    r=Q(1)
    for x in xs:r*=x
    return r

def var(i):
    m=[0]*NV;m[i]=1;return P({tuple(m):1})
v,a,b,S,t=[var(i) for i in range(NV)]
one=P(1); zero=P(0)
def row(*x): return [P(i) for i in x]
def add(x,y): return [i+j for i,j in zip(x,y)]
def sub(x,y): return [i-j for i,j in zip(x,y)]
def scale(c,x): return [c*i for i in x]
def mm(A,B): return [[sum((A[i][k]*B[k][j] for k in range(len(B))),P(0)) for j in range(len(B[0]))] for i in range(len(A))]
def eye(n):return [[P(int(i==j)) for j in range(n)] for i in range(n)]
def det2(A):return A[0][0]*A[1][1]-A[0][1]*A[1][0]
def det3(A):return sum(((-1)**j*A[0][j]*det2([[A[i][k] for k in range(3) if k!=j] for i in (1,2)]) for j in range(3)),P(0))
def assert_eq(x,y,label):
    assert x==y,label
    checks.append(label)
checks=[]
D=row(1,0,0);X=row(0,1,0);Y=row(0,0,1); Z=row(0,0,0)
d=add(scale(v,D),scale(1-v,Y));s=(v+2)/3
# All rows are in (D,x,y). These are declared contact equations, not a run.
times=[Z,X,Y,D,sub(scale(2,D),Y),sub(scale(v+2,D),scale(v+1,Y)),sub(scale(2*(v+1),D),scale(2*v+1,Y)),sub(sub(scale(2*(v+1),D),scale(2*v,Y)),X),sub(scale(2*(v+1),D),scale(2*v,Y))]
pos=[Z,X,Y,D,Y,d,Y,X,Z]
vel=[1,1,1,-1,1,-1,-1,-1]
diffs=[X,sub(Y,X),sub(D,Y),sub(D,Y),scale(v,sub(D,Y)),scale(v,sub(D,Y)),sub(Y,X),X]
for i in range(8):
    dt=sub(times[i+1],times[i])
    assert_eq(dt,diffs[i],f'outer positive-flight identity {i+1}')
    assert_eq(sub(pos[i+1],pos[i]),scale(vel[i],dt),f'outer messenger line identity {i+1}')
assert_eq(scale(v+1,sub(d,D)),scale(v-1,sub(times[5],times[3])),'moving D launch to restoration')
assert_eq(sub(d,Y),scale(v,sub(D,Y)),'restored outer gap')
assert_eq(times[-1],scale(2,sub(scale(1+v,D),scale(v,Y))),'outer total duration')
G=sub(d,scale(s,Y))
assert_eq(G,row(v,0,(1-4*v)/3),'single extra endpoint guard')
assert_eq(G[0]+G[1]/3+G[2]*Q(2,3),(v+2)/9,'center strict extra guard')
# Centered homogeneous algebra with all denominators cleared symbolically.
N=[[s,zero,1-v],[zero,s,(v-1)/3],[zero,zero,v]]
CtoP=[[one,zero,zero],[P(Q(1,3)),one,zero],[P(Q(2,3)),zero,one]]
PtoC=[[one,zero,zero],[P(Q(-1,3)),one,zero],[P(Q(-2,3)),zero,one]]
Nphysical=[[v,zero,1-v],[zero,s,zero],[zero,zero,s]]
assert_eq(mm(mm(PtoC,Nphysical),CtoP),N,'centered conjugacy')
assert_eq(det3(N),s*s*v,'raw determinant')
Hscaled=[[v,zero,zero],[zero,v,(1-v)/3],[zero,zero,s]]
assert_eq(mm(Hscaled,N),[[s*v,zero,v*(1-v)],[zero,s*v,zero],[zero,zero,s*v]],'compensated scale shear after denominator clearing')
B=[[b,-a],[a,b]];Badj=[[b,a],[-a,b]];beta=a*a+b*b
assert_eq(det2(B),beta,'positive conjugator determinant')
assert_eq(mm(Badj,B),[[beta,zero],[zero,beta]],'conjugator inverse numerator')
E=[[one,zero,one],[zero,one,zero],[zero,zero,one]]
FB=[[one,zero,zero],[zero,b,-a],[zero,a,b]]
FBinvScaled=[[beta,zero,zero],[zero,b,a],[zero,-a,b]]
assert_eq(mm(mm(FBinvScaled,E),FB),[[beta,beta*a,beta*b],[zero,beta,zero],[zero,zero,beta]],'all rational row shears by conjugation')
# The 44-event example. v times its physical return is Nphysical.
cinv=[row(1,0,Q(-3,2))]
assert_eq(mm(cinv,Nphysical),[scale(v,cinv[0])],'mixed-clock invariant D-3y/2')
assert_eq(v-s,2*(v-1)/3,'one minus r relation')
# The next guard on the closed form orbit D_n=c+3yt/2, y_n=yt,
# where t=r^n, multiplied by v, has row v*c+(s/2)*y*t.
Dn=row(1,0,Q(-3,2)+Q(3,2)*t); Yn=scale(t,Y)
assert_eq(sub(scale(v,Dn),scale(v-1+s,Yn)),add(scale(v,cinv[0]),scale(s*t/2,Y)),'mixed-clock nth guard')
clock_v=add(add(scale(2*v,sub(scale(1+v,D),scale(v,Y))),scale(2*v*(1+s),add(X,Y))),scale(2*(v+1),add(scale(s,add(X,Y)),d)))
assert_eq(clock_v[0],4*v*(v+1),'mixed-clock duration D coefficient')
assert_eq(clock_v[1],2*v+4*v*s+2*s,'mixed-clock duration x coefficient')
assert_eq(clock_v[2],2*v+4*v*s+2*s+2-4*v*v,'mixed-clock duration y coefficient')
# A positive-cone compatible matrix with no rational eigenray.
Pg=[[P(i) for i in rr] for rr in [[1,1,1],[1,2,1],[1,1,3]]]
lam=var(3)
char=det3([[lam*int(i==j)-Pg[i][j] for j in range(3)] for i in range(3)])
assert_eq(char,lam*lam*lam-6*lam*lam+8*lam-2,'positive matrix irreducible cubic')
for q in (1,-1,2,-2): assert char.evaluate([0,0,0,Q(q),0])!=0
checks.append('rational-root candidates excluded')
# Fresh rational arithmetic fixtures for parameter recovery and centered shear.
def qmm(A,B):return [[sum((A[i][k]*B[k][j] for k in range(len(B))),Q(0)) for j in range(len(B[0]))] for i in range(len(A))]
fixtures=[]
for vv in [Q(1,100),Q(1,4),Q(1,2),Q(4,7),Q(1),Q(8,5),Q(2),Q(10),Q(100)]:
    ss=(vv+2)/3;kk=3*(1-vv)/(vv+2)
    NN=[[ss,0,1-vv],[0,ss,(vv-1)/3],[0,0,vv]]
    HH=[[1/ss,0,0],[0,1/ss,(1-vv)/(3*ss*vv)],[0,0,1/vv]]
    assert qmm(HH,NN)==[[1,0,kk],[0,1,0],[0,0,1]]
    assert (3-2*kk)/(3+kk)==vv
    assert Q(-3)<kk<Q(3,2)
    fixtures.append({'v':str(vv),'s':str(ss),'k':str(kk),'center_margin':str((vv+2)/9)})
# k subdivision checks are arithmetic and contain no physical execution.
for kk in [Q(-100),Q(-3),Q(-1,2),Q(0),Q(3,2),Q(100,3)]:
    nn=max(1,(abs(kk).numerator+abs(kk).denominator-1)//abs(kk).denominator)
    delta=kk/nn;vv=(3-2*delta)/(3+delta)
    assert -1<=delta<=1 and vv>0 and nn*(3*(1-vv)/(vv+2))==kk
checks.append('all subdivision fixtures')
root=Path(__file__).resolve().parent
result={'scope':'Exact polynomial and rational matrix algebra only; no simulator or saved schedule executed.','symbolic_checks':checks,'symbolic_check_count':len(checks),'outer_flight_positive_rows':[ [p.terms() for p in rr] for rr in diffs], 'fixtures':fixtures,'mixed_clock_duration_times_v':[p.terms() for p in clock_v], 'sha256_checker':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(root/'evidence'/'static_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'symbolic_checks':len(checks),'rational_parameter_fixtures':len(fixtures)}))

# Compile, but do not execute, the declared 44-rule grammar. The strings h, p,
# and -h stand for fixed label speeds after selecting one rational v>1.
# Each tuple is (stationary role or temporary input, output, outgoing Q speed).
raw=[('X','X',1),('Y','Y',1),('R','R_outer',-1),('Y','Y',1),('R_outer','R',-1),('Y','Y',-1),('X','X',-1),('L','L',1)]
def scale_grammar(target,temp,inner):
    return ([(z,z,1) for z in inner]+[(target,temp,-1)]+
            [(z,z,-1) for z in reversed(inner)]+[('L','L',1)]+
            [(z,z,1) for z in inner]+[(temp,target,-1)]+
            [(z,z,-1) for z in reversed(inner)]+[('L','L',1)])
grammar=(raw+scale_grammar('Y','Y_inner',['X'])+
         scale_grammar('X','X_inner',[])+scale_grammar('X','X_global',[])+
         scale_grammar('Y','Y_global',['X'])+scale_grammar('R','R_global',['X','Y']))
assert len(grammar)==44 and grammar[-1][2]==1
q_speeds=[1]+[qout for _,_,qout in grammar[:-1]]
marker_speeds={**{z:'0' for z in ['L','X','Y','R']},'R_outer':'h','Y_inner':'p','X_inner':'p','X_global':'-h','Y_global':'-h','R_global':'-h'}
rules=[]
for j,(zin,zout,qout) in enumerate(grammar):
    nxt=(j+1)%44
    assert q_speeds[nxt]==qout
    rules.append({'event':j+1,'input':[f'Q{j}',zin],'output':[f'Q{nxt}',zout]})
assert len({tuple(sorted(r['input'])) for r in rules})==44
ruleset={'scope':'Declared finite rule table only; never executed as a physical schedule.','parameter':'v rational and v>1','speed_parameters':{'h':'(v-1)/(v+1)','p':'(v-1)/(v+5)'},'meta_signal_speeds':{**{f'Q{j}':str(q_speeds[j]) for j in range(44)},**marker_speeds},'rules':rules,'completion':'Every other input set with pairwise distinct speeds has identical output.','counts':{'events':44,'meta_signals':54,'temporary_marker_labels':6,'live_signals':5}}
(root/'RULES44.json').write_text(json.dumps(ruleset,indent=2)+'\n')
section={'coordinates':['D','x','y'],'initial':'L and Q0 at 0 outgoing; stationary X at x, Y at y, R at D','parameter':'v rational >1','guards':['x>0','y-x>0','D-y>0','3*v*D+(1-4*v)*y>0'],'r':'(v+2)/(3*v)','return':[['1','0','-(v-1)/v'],['0','r','0'],['0','0','r']],'infinite_validity':'0<x<y<D and D>=3*y/2','zeno':'0<x<y<D and D=3*y/2','non_zeno_valid':'0<x<y<D and D>3*y/2'}
(root/'SECTION44_AND_GUARDS.json').write_text(json.dumps(section,indent=2)+'\n')
print(json.dumps({'declared_rules':44,'unique_input_sets':44,'meta_signals':54,'physical_execution':False}))
