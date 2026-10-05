"""Exact integer counts, followed by non-certified floating-point diagnostics.
No tail enclosure or certified amplitude value is claimed.
"""
import math, time
from scipy.special import ai_zeros, gammaln
a=float(ai_zeros(1)[0][0])
c=[1, 53*a*a/90, a*(5618*a**3+46725)/32400,
   (8337112*a**6+200508660*a**3+191198475)/244944000,
   a*a*(220933468*a**6+10228873860*a**3+53801804475)/44089920000]
prev2=[1] # row -1
prev1=[1] # row 0
start=time.monotonic()
print('a_1=',repr(a),' c_1,...,c_4=',c[1:],flush=True)
for n in range(1,3001):
    row=[1]
    for m in range(1,n+1):
        row.append(2*row[-1]+(m+1)*(prev1[m] if m<len(prev1) else 0)-m*(prev2[m-1] if m-1<len(prev2) else 0))
    prev2,prev1=prev1,row
    if n in [20,50,100,250,500,1000,2000,3000]:
        raw=math.exp(math.log(row[-1])-float(gammaln(n+1))-n*math.log(8)-3*a*n**(1/3)-.875*math.log(n))
        corr=[raw/sum(c[j]*n**(-j/3) for j in range(depth+1)) for depth in range(5)]
        print(n,'raw and depth-1..4 corrected amplitude ratios:',*[f'{v:.12g}' for v in corr],flush=True)
print('Elapsed',time.monotonic()-start,flush=True)
