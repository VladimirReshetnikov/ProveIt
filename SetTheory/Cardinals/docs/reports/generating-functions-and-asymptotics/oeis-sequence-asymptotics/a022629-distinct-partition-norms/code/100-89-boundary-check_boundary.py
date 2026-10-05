import mpmath as m
m.mp.dps=35
for a in (1,2,3):
 a=m.mpf(a)
 if a==1:
  C=m.log(2*m.pi)/2-1;C1=m.mpf(7)/12-m.euler
 elif a==2:
  C=m.log1p(-m.exp(-2*m.pi));C1=m.mpf(1)/12-m.re(m.digamma(1+1j))
 else:
  C=a*m.log(2*m.pi)/2+m.nsum(lambda k:m.log1p(k**(-a)),[1,m.inf])-m.pi/m.sin(m.pi/a)
  C1=m.mpf(1)/12+m.nsum(lambda k:k/(1+k**a),[1,m.inf])-m.pi/a/m.sin(2*m.pi/a)
 for b in (4,6,8):
  b=m.mpf(b);K=m.exp(b);t=a*b/K
  f=lambda x:m.log1p(x**a*m.exp(-t*x))
  I=m.quad(f,[0,1,K/2,K,K+K/b,2*K,m.inf])
  hi=int(m.ceil((a*b+90)/t))
  S=m.fsum(f(k) for k in range(1,hi+1))
  print('a,b',int(a),int(b),'C',m.nstr(C,14),'C1',m.nstr(C1,14),'derivative approx',m.nstr((S-I-C)/t,14),'next scaled',m.nstr((S-I-C-C1*t)/t**2,10),flush=True)
