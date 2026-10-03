import mpmath as m, json, pathlib
m.mp.dps=60
p=pathlib.Path(__file__).parent

def constants(b):
 L=m.log(b);a=m.log(2)
 return m.pi**2*b/(12*(b-1)),a/(2*L),-a/(2*L)*m.log(2*m.pi)-a/4+a*a/(4*L),m.mpf(1)/(24*(b-1))
def coeff(b,k):
 s=2j*m.pi*k/m.log(b)
 return m.gamma(s)*m.zeta(1+s)*m.zeta(s)*(1-m.exp(-s*m.log(2)))/m.log(b)
def periodic(b,u,order=0):
 return 2*m.re(sum(coeff(b,k)*(2j*m.pi*k/m.log(b))**order*m.exp(2j*m.pi*k*u) for k in range(1,25)))
def logf(b,t):
 # Direct positive-real product evaluated by a fast convergent eta identity at small t.
 def ld(t):
  if t<1:
   # log distinct partition product = pi²/(12t)-log2/2+t/24 + logP(e^(-4pi²/t))-logP(e^(-2pi²/t))
   # P(e^-x)=prod(1-e^-kx)^-1
   return m.pi**2/(12*t)-m.log(2)/2+t/24+lp(4*m.pi**2/t)-lp(2*m.pi**2/t)
  return sum(m.log1p(m.exp(-k*t)) for k in range(1,int(m.ceil(150/t))+1))
 def lp(x):return sum(-m.log1p(-m.exp(-k*x)) for k in range(1,int(m.ceil(150/x))+1))
 val=0
 while t<150:
  val+=ld(t);t*=b
 return val
if __name__ == "__main__":
 out={}
 for b in [2,3,4,8,16]:
  A,beta,C,d=constants(b);c=coeff(b,1)
  rows=[]
  for u in [m.mpf('0'),m.mpf('.25'),m.mpf('.5'),m.mpf('.75')]:
   t=m.power(b,-8-u);P=periodic(b,u)
   rows.append({'u':str(u),'P':str(P),'H':str(m.exp(P)),'direct_logF_remainder':str(logf(b,t)-(A/t+beta*m.log(t)+C+P-d*t))})
  out[str(b)]={'A':str(A),'beta':str(beta),'C':str(C),'d':str(d),'P_first_fourier_coefficient':str(c),'twice_abs_first':str(2*abs(c)),'phase_checks':rows}
 (p/'mellin-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
