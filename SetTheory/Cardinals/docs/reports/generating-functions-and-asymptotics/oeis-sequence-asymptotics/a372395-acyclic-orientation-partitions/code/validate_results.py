"""Recheck exact overlaps, OEIS initial data, asymptotic and inverse residuals."""
import json
from pathlib import Path
import mpmath as m
root=Path(__file__).parent
m.mp.dps=60
v=json.loads((root/'exact_values_300.json').read_text())
w=json.loads((root/'exact_values_150.json').read_text())
a=json.loads((root/'generic_second_correction.json').read_text())
expected={
 'unrestricted':[1,1,3,11,65,411,3535,31081,337185,3846557,50329253,691740489,10725769171,172411994899,3050277039465,56428854605627,1124781474310649,23349607769846667,518744693882444419,11949343411110856153,291921874093876965453],
 'distinct':[1,1,1,5,9,63,509,2959,22453,247949,3080991,28988331,407320739,5122243495,82583577967,1430027615585,22556817627789,395098668828675,7979894546677853,154786744386253387,3355612019167352821]}
out={}
for key,C,A,p in [
 ('unrestricted','2.1587520056577855317373573144047825723165259312102','0.16481752396442050396187672134838365614759460482904',1),
 ('distinct','0.90572982172019901788916250016056881567900117572326','0.21799921291820252233936031170847439858780754258368',m.mpf('.75'))]:
 assert v[key][:151]==w[key]
 assert list(map(int,v[key][:len(expected[key])]))==expected[key]
 C=m.mpf(C);A=m.mpf(A);a1=m.mpf(a[key]['a1']);a2=m.mpf(a[key]['a2'])
 alpha=m.mpf('.5')-p;d0=m.log(A*m.sqrt(2*m.pi)); rows=[]
 for n in [40,60,80,100,150,200,250,300]:
  Y=m.mpf(v[key][n]); ratio=Y/m.factorial(n)*n**p*m.exp(-C*m.sqrt(n))/A
  L=m.log(Y);N=L/m.lambertw(L/m.e);ell=m.log(N)
  ra=-C/ell
  rb=-alpha-d0/ell+C*C/(2*ell**2)-C*C/(2*ell**3)
  rc=-((ra+C/2)*rb-ra**3/6-C*ra**2/8+alpha*ra+a1)/ell
  XI=N+m.sqrt(N)*ra+rb;XI1=XI+rc/m.sqrt(N)
  rows.append({'n':n,'ratio':str(ratio),
    'n_residual1':str((ratio-1-a1/m.sqrt(n))*n),
    'n_3_over_2_residual2':str((ratio-1-a1/m.sqrt(n)-a2/n)*n**m.mpf('1.5')),
    'inverse_I_error':str(XI-n),
    'inverse_I_scaled_error':str((XI-n)*m.sqrt(N)*ell),
    'inverse_next_error':str(XI1-n),
    'inverse_next_scaled_error':str((XI1-n)*N*ell)})
 out[key]=rows
 print(key, 'n=300 scaled residual',rows[-1]['n_3_over_2_residual2'])
 print('inverse error',rows[-1]['inverse_I_error'],'next',rows[-1]['inverse_next_error'])
(root/'validation_300.json').write_text(json.dumps({'known_oeis_terms_match':True,'n150_n300_overlap_match':True,'rows':out},indent=2))
print('PASS: exact OEIS initials and independent overlap')
