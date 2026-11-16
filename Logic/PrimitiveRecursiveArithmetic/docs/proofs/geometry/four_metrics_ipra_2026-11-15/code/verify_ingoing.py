#!/usr/bin/env python3
"""Exact check of the horizon-regular Kerr-Newman chart.

Uses the standard-library polynomial arithmetic from verify_stdlib.py.
Unlike the Boyer-Lindquist formula, no input denominator contains Delta.
All tensor components are recomputed, including at the algebraic locus Delta=0.
"""
import json
import time
from pathlib import Path
import verify_stdlib as v

r,x,a,m,q = [v.Rat(p) for p in (v.P_R,v.P_X,v.P_A,v.P_M,v.P_Q)]
S,D,s = v.Rat(v.P_S),v.Rat(v.P_D),v.Rat(v.P_s)
iS,is_ = v.Rat(1,(0,1,0,0)),v.Rat(1,(0,0,0,1))
half=v.Rat(1,(1,0,0,0)); quarter=half*half
P=r*r+a*a; L=2*m*r-q*q
g,gi=v.matrix(),v.matrix()
g[0][0]=-1+L*iS
g[0][1]=g[1][0]=v.Rat(1)
g[0][3]=g[3][0]=-a*s*L*iS
g[1][3]=g[3][1]=-a*s
g[2][2]=S*is_
g[3][3]=P*s+a*a*s*s*L*iS
gi[0][0]=a*a*s*iS
gi[0][1]=gi[1][0]=P*iS
gi[0][3]=gi[3][0]=a*iS
gi[1][1]=D*iS
gi[1][3]=gi[3][1]=a*iS
gi[2][2]=s*iS
gi[3][3]=iS*is_
v.check('ingoing_inverse',(sum(g[i][k]*gi[k][j] for k in range(4))-int(i==j) for i in range(4) for j in range(4)))
det=v.Rat(0)
for p in v.permutations(range(4)):
 term=v.Rat((-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4)))
 for i in range(4): term=term*g[i][p[i]]
 det=det+term
v.check('ingoing_determinant',[det+S*S])
G=[[[half*sum(gi[k][l]*(g[l][j].diff(i)+g[l][i].diff(j)-g[i][j].diff(l)) for l in range(4)) for j in range(4)] for i in range(4)] for k in range(4)]
trace=[sum(G[k][i][k] for k in range(4)) for i in range(4)]
v.check('ingoing_trace',(trace[i]-S.diff(i)*iS for i in range(4)))
Ric=[[sum(G[k][i][j].diff(k)+G[k][i][j]*trace[k] for k in range(4))-trace[i].diff(j)-sum(G[k][i][l]*G[l][j][k] for k in range(4) for l in range(4)) for j in range(4)] for i in range(4)]
A=[-q*r*iS,v.Rat(0),v.Rat(0),q*r*a*s*iS]
F=[[A[j].diff(i)-A[i].diff(j) for j in range(4)] for i in range(4)]
Fu=v.mmul(v.mmul(gi,F),gi)
I=sum(F[i][j]*Fu[i][j] for i in range(4) for j in range(4))
T=v.mmul(v.mmul(F,gi),v.transpose(F))
v.check('ingoing_maxwell',(sum((S*Fu[i][j]).diff(i) for i in range(4)) for j in range(4)))
v.check('ingoing_dF',(F[j][k].diff(i)+F[k][i].diff(j)+F[i][j].diff(k) for i in range(4) for j in range(i+1,4) for k in range(j+1,4)))
v.check('ingoing_einstein_maxwell',(Ric[i][j]-2*(T[i][j]-quarter*g[i][j]*I) for i in range(4) for j in range(4)))
v.check('ingoing_scalar_curvature',[sum(gi[i][j]*Ric[i][j] for i in range(4) for j in range(4))])
all_objects=v.flatten(g)+v.flatten(gi)+v.flatten(Ric)+v.flatten(F)+v.flatten(Fu)
if any(z.d[2] for z in all_objects):
 raise ValueError('A Delta denominator survived in the regular chart')
# Direct tensor transformation from the BL chart on its overlap.
iD=v.Rat(1,(0,0,1,0))
gb=v.matrix()
gb[0][0]=(-D+a*a*s)*iS
gb[0][3]=gb[3][0]=a*s*(D-P)*iS
gb[1][1]=S*iD; gb[2][2]=S*is_
gb[3][3]=s*(P*P-a*a*D*s)*iS
J=[[v.Rat(int(i==j)) for j in range(4)] for i in range(4)]
J[0][1]=-P*iD; J[3][1]=-a*iD
pull=v.mmul(v.mmul(v.transpose(J),gb),J)
v.check('coordinate_overlap',(pull[i][j]-g[i][j] for i in range(4) for j in range(4)))
# Pullback A differs only by (q r / Delta) dr, whose exterior derivative is zero.
pull_A=[sum(A[i]*J[i][j] for i in range(4)) for j in range(4)]
v.check('potential_overlap',(pull_A[i]-A[i]-(q*r*iD if i==1 else 0) for i in range(4)))
result={'status':'PASS','engine':'Python standard library','coordinate_order':['v','r','x','psi'],
 'domain':'S != 0 and s != 0; Delta may be zero',
 'all_metric_curvature_and_field_components_have_no_Delta_denominator':True,
 'checks':v.CHECKS,'arithmetic_counters':v.COUNTS,'seconds':round(time.monotonic()-v.START,3)}
path=Path(__file__).resolve().parents[1]/'certificates'/'ingoing_results.json'
path.write_text(json.dumps(result,indent=2)+'\n')
v.announce('PASS: horizon-regular chart')
