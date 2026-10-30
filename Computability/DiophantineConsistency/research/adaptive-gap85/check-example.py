"""Evaluate an artificial small-parameter gap85 example exactly in integers."""
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent/'candidate.json';raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()=='c2c2e1bbb267bdc155536c5b3df9641f8faff97dab4b549a1d514d671ebdea00';j=json.loads(raw)
v=dict(J=1,F=2,C=2,f=1,i=1,T=1,X=1,Y=8,r=16,eta=1,zeta=1,y=1,gamma=1,beta=1,K0=2,MC=0,MF=0);assert all(v[n]>0 for n in j['witnesses'])
for n,op,a,b in j['source']:
 x=a if isinstance(a,int) else v[a];y=b if isinstance(b,int) else v[b];v[n]=x+y if op=='+' else x-y if op=='-' else x*y
assert (v['q'],v['F']+v['C'],v['F0'],v['F1'],v['Fa'],v['Fs'],v['P13'])==(2,4,1,36270938,1,83522,3029421283635)
print(json.dumps({'ports':[1,2,0,0],'witnesses':[v[n] for n in j['witnesses']],'q':v['q'],'F_plus_C':v['F']+v['C'],'first_factor':v['F0'],'main_factor':v['F1'],'auxiliary_factor':v['Fa'],'strong_factor':v['Fs'],'full_polynomial':v['P13'],'scope':'Artificial ports, first and auxiliary factors only; full candidate is not zero.'},indent=2))
