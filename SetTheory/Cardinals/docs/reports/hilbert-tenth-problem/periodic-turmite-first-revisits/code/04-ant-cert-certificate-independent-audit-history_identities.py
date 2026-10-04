#!/usr/bin/env python3
"""Fresh recovery: independent equation transcription, data-only historical DAG."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,os
import sympy as s
R=Path(os.environ.get('ANT_CERTIFICATE_ROOT','/workspace/shared/complete-ant-certificate-recovered-20261004-v2')).resolve()
H=Path(__file__).resolve().parent
d=json.loads((R/'history/history174.json').read_text());names=d['parameters']+d['witnesses'];z=dict(zip(names,s.symbols(' '.join(names))));e=dict(z)
def val(x):return s.Integer(x) if type(x)is int else e[x]
for out,op,a,b in d['nodes']:
 if out in e:raise ValueError('duplicate node')
 a,b=val(a),val(b);e[out]=a+b if op=='+' else a-b if op=='-' else a*b
q,Q,W,Gt,Gy,K,Wp=(z[n] for n in ['q','Q','W','Gt','Gy','K','Wp'])
I,FMem,FSign=(z[n]-1 for n in ['InitialMemoryPlus','FinalMemoryPlus','FinalSignPlus'])
A,B,GE,GW,GN,GS,D,E,F,G,Z,SW,SN=(z[n+'Plus']-1 for n in ['A','B','GE','GW','GN','GS','D','E','F','G','Z','SW','SN'])
C=GE+GW+GN+GS;Zp=GW+GN;Odd=3*K;VH=Gt*z['HeightEven'];North=Gt*z['WidthOdd'];South=z['uW']*(3*North+Gt)
forbidden=[Odd+Wp*VH,Odd+VH,K+North,K+South]
fields=[A,B,C,D,E,F,G,GE,GW,GN,GS]+[v+b for v,b in zip([GE,GW,GN,GS],forbidden)]
NC=3*GE+SW+SN+W*GS;NZ=SW+W*GS
r=[q-Q*z['uQ'],Q-W*z['uW'],q-1-Gt*(Q-1),Q-1-Gy*(W-1),W-8*z['WidthOdd']-3,Gy-(W+1)*z['HeightEven'],q-1-8*K,W-3*Wp,I+z['BoundInitial']-Q,z['InitialHead']+z['BoundHead']-Q,q-z['InitialHead']*z['HeadQuot'],z['InitialHead']-z['HeadRoot']**2,C-D-E,A+E-B-D,D-F-G,Z+G-Zp-F,3*SW-GW,W*SN-GN,C+q*z['FinalHead']-z['InitialHead']-Q*NC,Z+q*FSign-Q*NZ,A+q*FMem-I-Q*B]
fn=['A','B','C','D','E','F','G','GE','GW','GN','GS','TestE','TestW','TestN','TestS','Z'];r += [f+z['Bound'+n]-q for f,n in zip(fields+[Z],fn)]
Packed=sum(v*q**i for i,v in enumerate(fields+[D]));D0=9*q**16;p=z;U=p['w']*D0;Y=p['s']*D0;EE=U*Y;PP=U*Y**2;Delta=(p['a']+3)**2-1;RR=p['i']*p['c']**2;uu=2*p['r']+1+p['j']*p['c'];yy=p['y_aux']
r += [p['r']-(D0-3*Packed-1),PP*(PP+1)*p['k']**2-p['tau']*(p['tau']+1),p['c']-Y*p['k']-p['eta'],p['k']-p['eta']-p['zeta'],p['k']-p['r']-1-p['h']*EE,p['a']-Y*(U+1),p['d']-U-p['a']*p['c']-p['ga']*(6*p['a']+8),p['d']**2-1-Delta*p['c']**2,RR**2-Delta*(p['f']**2-1),Delta*(p['f']**2-1)*(uu**2-yy**2)-(1-yy**2),uu-p['c']-p['o']*p['f']]
if len(r)!=48:raise ValueError('source equation count')
degrees=[];leaders=[]
for i,((a,b),want) in enumerate(zip(d['equalities'],r,strict=True)):
 actual=s.expand(val(a)-val(b));correction=r[45]*(uu**2-yy**2) if i==46 else 0
 if s.expand(actual-want-correction)!=0:raise ValueError('source mismatch '+str(i))
 poly=s.Poly(actual,*z.values());deg=int(poly.total_degree());degrees.append(deg)
 if deg==104:leaders.append({'index':i,'terms':[{'coefficient':int(c),'powers':{n:int(k) for n,k in zip(names,m) if k}} for m,c in poly.terms() if sum(m)==104]})
if max(degrees)!=104 or leaders!=[{'index':38,'terms':[{'coefficient':531441,'powers':{'q':96,'k':2,'s':4,'w':2}}]}]:raise ValueError('degree leader')
result={'status':'PASS_FRESH_INDEPENDENT_HISTORY_IDENTITIES','recovery':'Reconstructed audit implementation; fresh polynomial checks, no old audit-byte identity claim','source_sha256':hashlib.sha256((R/'history/history174.json').read_bytes()).hexdigest(),'exact_residuals':48,'triangular_replacement_index':46,'replacement_uses_previous_residual_index':45,'degrees':degrees,'leader':leaders,'no_upstream_code_or_schedule_execution':True,'physical_simulation':False}
(H/'history-receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
