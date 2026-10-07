from fractions import Fraction as F
from pathlib import Path
import json
from certified_interval import IV,S,PREC,expminus,binary_product,polynomial
P=Path(__file__).resolve().parent;N=2**24;a=[0]*(N+1);a[1]=1
for k in range(1,N):
 value=a[k]
 for j in range(k+1,N+1,k):a[j]+=value
 if k in [2**20,2**22,2**23]:print('coefficient sieve',k,flush=True)
if a[100]!=30151 or a[1000000]!=8184152587975867792854523048658024440903218:raise RuntimeError('exact coefficient regression')
print('sieve complete',flush=True)
rows=[]
for t in [F(9,2**21),F(3,2**19)]:
 q=expminus(t);finite=polynomial(a,q);Hfinite=q*finite/binary_product(t)
 tail=14*expminus(t*N/2)/(1-expminus(t/2))
 H=Hfinite+IV(0,tail.hi)
 row={'t':str(t),'N':N,'H':H.decimal(40),'H_integer_bounds':H.integer_bounds(),'tail':tail.decimal(40),'tail_integer_bounds':tail.integer_bounds(),'finite_H':Hfinite.decimal(40)}
 rows.append(row);print(row,flush=True)
receipt={'status':'RADIAL_VALUES_ENCLOSED','global14_reference':'GLOBAL_BOUND_CERTIFICATE.json','precision_bits':PREC,'N':N,'endpoint_exact_aN':str(a[N]),'rows':rows,'no_nonconstancy_claim':True}
(P/'RADIAL_VALUE_CERTIFICATE.json').write_text(json.dumps(receipt,indent=2)+'\n')
