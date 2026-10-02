import mpmath as m
m.mp.dps=70
for n in (20,50,100,200,500,1000,5000,10000):
 x=m.sqrt(m.mpf(n)/2)
 def psi(t):return (n-2*t+1)*m.log(t)-t*t+m.loggamma(t)
 def dp(t):return (n+1)/t-2*m.log(t)-2-2*t+m.digamma(t)
 s=m.findroot(dp,(x*.8,x))
 H=(n+1)/s**2+2/s+2-m.polygamma(1,s)
 l3=2*(n+1)/s**3+2/s**2+m.polygamma(2,s)
 amp=m.sqrt(2*m.pi/H)/m.pi*m.exp(-m.pi**2/(2*H))
 f=lambda t:m.exp(psi(t)-psi(s))*m.sin(m.pi*t)/m.pi if t>0 else m.mpf(0)
 lo=max(m.mpf(0),s-20);hi=s+20
 pts=[lo]+[s+k for k in range(-19,20) if lo<s+k<hi]+[hi]
 exact=m.quad(f,pts)/amp
 lead=m.sin(m.pi*s)
 corr=l3*(m.pi/(2*H**2)-m.pi**3/(6*H**3))*m.cos(m.pi*s)
 print(n,'sigma',m.nstr(s,12),'normalizedJ',m.nstr(exact,12),'e0',m.nstr(exact-lead,8),'e1',m.nstr(exact-lead-corr,8),'e1sigma2',m.nstr((exact-lead-corr)*s*s,8),flush=True)
