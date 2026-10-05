import mpmath as m
m.mp.dps=40
for b in [3,5,7,9]:
 b=m.mpf(b);K=m.exp(b);t=b/K
 f=lambda x:m.log1p(x*m.exp(-t*x))
 I=m.quad(f,[0,1,K/2,K,K+K/b,2*K,m.inf])
 hi=int(m.ceil((b+80)/t))
 L=sum(f(k) for k in range(1,hi+1))
 c=m.log(2*m.pi)/2-1
 print('b',b,'sum-integral',m.nstr(L-I,22),'constant error',m.nstr(L-I-c,12),flush=True)
