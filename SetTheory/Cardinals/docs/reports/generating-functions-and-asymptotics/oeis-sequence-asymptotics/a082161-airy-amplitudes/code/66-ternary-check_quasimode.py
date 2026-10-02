import numpy as np
from scipy.special import airy, ai_zeros
import json
A=float(ai_zeros(1)[0][0])

def omega(j): return 1+(1/3+np.power(-.5,j)/6)/(j+1)
def profile(i, maxheight):
    j=np.arange(i%3,min(i,maxheight)+1,3,dtype=int)
    e=i**(-1/3)
    x=e*(j+1)
    f=airy(A+x)[0]
    v=(1-e*(5*x*x/12+A*x/6))*f
    # Numerical check uses a distant hard cutoff at x=30, whose omitted tail is negligible here.
    N=np.sqrt(np.dot(omega(j),v*v))
    return j,v,N

def check(i):
    maxheight=int(30*i**(1/3))
    jo,vo,No=profile(i-1,maxheight+5)
    j,v,N=profile(i,maxheight+5)
    xold=np.zeros(max(i,maxheight)+5) if i<maxheight else np.zeros(maxheight+12)
    xold[jo]=vo/No
    got=np.zeros(len(j))
    ok=j>=1
    got[ok]=4*(i-j[ok]+3)/(2*i+j[ok])*xold[j[ok]-1]
    got+=xold[j+2]
    s=3*(1+A*i**(-2/3)+2.5/i)*N/No
    fw=np.sqrt(np.dot(omega(j),(got/s-v/N)**2))
    arr=np.zeros(maxheight+12)
    arr[j]=v/N
    ad=4*(i-(jo+1)+3)/(2*i+(jo+1))*omega(jo+1)*arr[jo+1]
    ok=jo>=2
    ad[ok]+=omega(jo[ok]-2)*arr[jo[ok]-2]
    ad/=omega(jo)
    bw=np.sqrt(np.dot(omega(jo),(ad/s-vo/No)**2))
    return {'i':i,'forward_norm':fw,'forward_times_i4third':fw*i**(4/3),'adjoint_norm':bw,'adjoint_times_i':bw*i,'norm_ratio':N/No}
print(json.dumps({'airy_zero':A,'checks':[check(i) for i in [300,301,302,3000,3001,3002,30000,30001,30002,300000,300001,300002]]},indent=2))
