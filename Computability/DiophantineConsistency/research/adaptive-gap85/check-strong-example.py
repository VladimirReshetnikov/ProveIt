"""Exact first+strong weak-system example; no full candidate zero."""
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent/'candidate.json';raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()=='c2c2e1bbb267bdc155536c5b3df9641f8faff97dab4b549a1d514d671ebdea00';j=json.loads(raw)
# (x,s)=(18+sqrt(323))^289; its ordinate is exactly divisible by 17².
x,s=1,0
for _ in range(289):x,s=18*x+323*s,x+18*s
assert x*x-323*s*s==1 and s%289==0
v=dict(J=1,F=2,C=2,f=x,i=323*(s//289),T=1,X=1,Y=8,r=16,eta=1,zeta=1,y=1,gamma=1,beta=1,K0=2,MC=0,MF=1);assert all(v[n]>0 for n in j['witnesses'])
for n,op,a,b in j['source']:
 a=a if isinstance(a,int) else v[a];b=b if isinstance(b,int) else v[b];v[n]=a+b if op=='+' else a-b if op=='-' else a*b
assert (v['q'],v['F']+v['C'],v['F0'],v['Fs'],v['F1'])==(2,4,1,1,39366338)
assert abs(v['Fa'])!=1 and v['P13']!=0
h=lambda n:hashlib.sha256(str(n).encode()).hexdigest()
print(json.dumps({'ports':[1,2,0,1],'fixed_witnesses':'J=1,F=C=2,T=X=eta=zeta=y=gamma=1,Y=8,r=16','f_and_i':'(f,s)=(18+sqrt(323))^289; i=323*s/289','f_digits':len(str(x)),'i_digits':len(str(v['i'])),'f_sha256_decimal':h(x),'i_sha256_decimal':h(v['i']),'q':v['q'],'F_plus_C':v['F']+v['C'],'first_factor':v['F0'],'strong_factor':v['Fs'],'main_factor':v['F1'],'auxiliary_factor_decimal_sha256':h(v['Fa']),'full_polynomial_decimal_sha256':h(v['P13']),'full_nonzero':True,'scope':'Artificial ports; first and strong factors only. Full candidate is not zero.'},indent=2))
