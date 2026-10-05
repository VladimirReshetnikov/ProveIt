import json,mpmath as m
from pathlib import Path
BASE=Path(__file__).resolve().parent;m.mp.dps=80
a=m.airyaizero(1)
source=json.load(open(BASE/'exact_dp_3000.json'))['samples']
result={'disclaimer':'Exact integer DP; the following high-precision evaluation and extrapolation are numerical, not certified bounds.','inverse_errors':[],'extrapolated_gamma':{}}
for sample in source:
 if sample['n'] not in (100,200,500,1000,2000,3000):continue
 n=m.mpf(sample['n']);out={'n':int(n)}
 for kind,alpha in [('R',m.mpf(1)),('C',m.mpf(3)/4)]:
  Y=m.mpf(sample[kind]['logu'])+m.loggamma(n+1)+n*m.log(4)+3*a*n**(m.mpf(1)/3)+alpha*m.log(n)
  u=Y/m.lambertw(4*Y/m.e);L=m.log(4*u)
  z=u-(3*a*u**(m.mpf(1)/3)+(alpha+m.mpf('.5'))*m.log(u)+m.log(2*m.pi)/2)/L
  out[kind]=m.nstr(z-n,40)
 result['inverse_errors'].append(out)
zz=[j for j in source if j['n']>=1600]
for kind in 'RC':
 result['extrapolated_gamma'][kind]=[]
 for count in (7,9,11,13,15):
  ss=zz[-count:]
  mat=m.matrix([[m.mpf(1)]+[m.mpf(q['n'])**(-m.mpf(j)/3) for j in range(7,6+count)] for q in ss])
  rhs=m.matrix([m.log(m.mpf(q[kind]['gamma_corrected_0_to_6'][6])) for q in ss])
  estimate=m.exp(m.lu_solve(mat,rhs)[0])
  result['extrapolated_gamma'][kind].append({'sample_count':count,'first_n':ss[0]['n'],'last_n':ss[-1]['n'],'value':m.nstr(estimate,55)})
json.dump(result,open(BASE/'numerical_analysis.json','w'),indent=2)
print(json.dumps(result,indent=2))
