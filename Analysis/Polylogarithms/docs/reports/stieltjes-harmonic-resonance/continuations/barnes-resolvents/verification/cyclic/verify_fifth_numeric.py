"""Independent Mellin and local-series diagnostics for fifth cyclic jets.
Not interval certificates. The exact analytic proof is separate.
"""
from pathlib import Path
import json,sys,time
import mpmath as mp

def main():
    mp.mp.dps=70
    sys.path.insert(0,str(Path(__file__).resolve().parent))
    import tornheim_mellin as mod
    mp.mp.dps=70;mod.K=62;mod.N=155
    start=time.time()
    L=mp.log(2*mp.pi);g=mp.euler;q=mp.zeta(2);q4=mp.zeta(4)
    z=[mp.zeta(0,derivative=j) for j in range(6)]
    y=[mp.zeta(-1,derivative=j) for j in range(6)]
    K=65;N=155
    ak=[(-1)**k*mp.zeta(-k,derivative=1)/mp.factorial(k) for k in range(K+1)]
    bk=[(-1)**k*mp.zeta(-k,derivative=2)/mp.factorial(k) for k in range(K+1)]
    def M(r,v):return mp.fsum(mp.binomial(r,j)*g**(r-j)*(-1)**j*mp.factorial(j)/mp.mpf(v)**(j+1) for j in range(r+1))
    I1=mp.fsum(ak[k]*(M(3,k-1)+q*M(1,k-1))+bk[k]*(mp.mpf('1.5')*M(2,k-1)+q*M(0,k-1)/2) for k in range(2,K+1))
    I1+=mp.fsum(bk[j]*bk[k]/(4*(j+k))+bk[j]*ak[k]*(g/(j+k)-mp.mpf(1)/(j+k)**2) for j in range(K+1) for k in range(K+1) if j+k)
    I2=mp.mpf(0)
    for k in range(4,N+1):
     u=mp.fsum(mp.log(j)**2*mp.log(k-j)**2 for j in range(2,k-1))
     v=mp.fsum(mp.log(j)**2*mp.log(k-j) for j in range(2,k-1))
     tail=mp.diff(lambda t:mp.gammainc(t,k,mp.inf)*mp.power(k,-t),0)+g*mp.e1(k)
     I2+=u*mp.e1(k)/4-v*tail
    E0=-(10*g**4+20*g**3+12*g*g*q+30*g*g+12*g*q+30*g+2*q*q+6*q+15)/16
    E=E0+(-g**4-2*g*g*q+q*q+2*q4)*y[1]/4-g*(g*g+q)*y[2]/2
    E-=(g**3+3*g*g+6*g+6+(g+1)*q)*z[1]
    E-=(3*g*g+6*g+6+q)*z[2]/2
    E+=(g*g-q)*z[1]*z[2]/2+g*z[2]**2/4
    chi=I1+I2+E
    out={'qualification':'Uncertified high-precision diagnostics; truncated local and exponential series.', 'dps':mp.mp.dps,'K':K,'N':N,'I_small':mp.nstr(I1,60),'I_large':mp.nstr(I2,60),'elementary_correction':mp.nstr(E,60),'chi':mp.nstr(chi,60)}
    print(json.dumps(out,indent=2),flush=True)
    # Symmetric fifth derivative after subtracting the first and third jets.
    omega3=mp.mpf('86.6578666011000736529032768587621836100797302472')
    # Use Mellin first+third approximations to avoid inheriting approximate omega3.
    def oddjets(raw):
     a,b,c=map(mp.mpf,raw)
     first=mod.prediction(a,b,c)[1]
     xs=[];ys=[]
     for j in range(8):
      h=mp.mpf('0.0015')/2**j
      odd=(mod.tornheim(a*h,b*h,c*h)-mod.tornheim(-a*h,-b*h,-c*h)-2*h*first)/(2*h**3)
      xs.append(h*h);ys.append(odd)
     # interpolate values ys on x=h², constant third/6, linear fifth/120.
     third=6*mod.extrapolate_zero(xs,ys)
     slope=mp.fsum(yi*mp.fsum(mp.fprod(-xs[k] for k in range(len(xs)) if k!=i and k!=j)/mp.fprod(xs[i]-xs[k] for k in range(len(xs)) if k!=i) for j in range(len(xs)) if j!=i) for i,yi in enumerate(ys))
     return third,120*slope
    omega3_num,omega5=oddjets((1,1,1))
    print('omega5',mp.nstr(omega5,55),flush=True)
    rows=[]
    for raw in [(1,2,3),(1,1,2),(1,-2,3)]:
     a,b,c=map(mp.mpf,raw);s1=a+b+c;s2=a*b+b*c+c*a;s3=a*b*c;d=s1*s1-3*s2;p2=s1*s1-2*s2
     vals=[oddjets(v)[1] for v in [raw,(raw[1],raw[2],raw[0]),(raw[2],raw[0],raw[1])]]
     actual=mp.fsum(vals)
     pred=s3*p2*omega5-120*s3*d*chi
     pred+=(-5*(s1*s2-3*s3)*d)*L*z[4]
     pred+=20*(s1*s2*s2-4*s1*s1*s3+3*s2*s3)*z[2]*z[3]
     pred+=(-2*s1**5+5*s1**3*s2-5*s1*s2*s2+47*s1*s1*s3-69*s2*s3)*z[5]
     row={'slopes':raw,'direct':mp.nstr(actual,50),'formula':mp.nstr(pred,50),'absolute_error':mp.nstr(abs(actual-pred),8)}
     print(row,flush=True);rows.append(row)
     assert abs(actual-pred)<mp.mpf('1e-28')
    out.update({'status':'passed','omega5':mp.nstr(omega5,55),'omega3_error':mp.nstr(abs(omega3_num-omega3),8),'rows':rows,'elapsed_seconds':time.time()-start})
    output=Path(__file__).resolve().parent/'generated_results'
    output.mkdir(exist_ok=True)
    (output/'fifth_numeric.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')


if __name__ == '__main__':
    main()
