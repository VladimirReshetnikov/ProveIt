from pathlib import Path
import json, math, time
import mpmath as mp
mp.mp.dps=75
rows=[]

def data(x,m):
    q=mp.exp(-x);nmax=45
    nodes=[-mp.log(n) for n in range(1,nmax+1)]
    R=[1+u*u/(2*mp.pi) for u in nodes];Q=nodes
    def psi(e,der=0):
        out=[]
        for n,u,r,v in zip(range(1,nmax+1),nodes,R,Q):
            weight=(-1)**(n-1)*mp.power(n,-m-e)*q**(n-1)
            im=mp.sin(mp.pi*e)*r+mp.cos(mp.pi*e)*v
            re=mp.cos(mp.pi*e)*r-mp.sin(mp.pi*e)*v
            out.append(weight*(im if der==0 else u*im+mp.pi*re if der==1 else (n-1)*im))
        return mp.fsum(out)
    e=mp.findroot(psi,-mp.log(2)*q/(mp.pi*2**m),tol=mp.mpf('1e-70'))
    ex=psi(e,2)/psi(e,1)
    c=(-1)**m*q*mp.fsum((-1)**(n-1)*mp.power(n,-m-e)*q**(n-1)*
       (mp.cos(mp.pi*e)*r-mp.sin(mp.pi*e)*v)
       for n,r,v in zip(range(1,nmax+1),R,Q))
    return m+e,ex,c,abs(psi(e))

def jets(x,s,nmax=96):
    # Direct Cauchy extraction of the entire exact completion; no tiny-step
    # differentiation of PolyLog near integer order.
    a=mp.mpf('.5')+1j*x/(2*mp.pi);radius=mp.mpf('.18')
    vals=[]
    for k in range(nmax):
        z=mp.exp(2j*mp.pi*k/nmax);t=s+radius*z
        L=-(2*mp.pi)**t*mp.exp(-.5j*mp.pi*t)*mp.rgamma(t)*mp.zeta(1-t,a)
        vals.append((z,L))
    return [mp.factorial(j)*mp.fsum(v/z**j for z,v in vals)/(nmax*radius**j) for j in range(4)]

def physical(x,m,samples=96):
    s,ex,c,res=data(x,m);js=jets(x,s,samples)
    return mp.re((1+mp.pi/2)*js[0]+js[2]/(2*mp.pi))-c

def physical_jet(x,s,j):
    # Absolutely convergent completion series, differentiated in order.
    q=mp.exp(-x)
    return mp.fsum((-1)**(n-1)*mp.power(n,-s)*q**n*
      (-mp.log(n)-1j*mp.pi)**j*mp.exp(-1j*mp.pi*s) for n in range(1,46))

for m in [0,1,2]:
    for w in [10,20]:
        started=time.time();w=mp.mpf(w);s,sx,c,res=data(w,m)
        js=jets(w,s);jm=jets(w,s-1)
        ps=mp.re((1+mp.pi/2)*(js[1]-physical_jet(w,s,1))+
                    (js[3]-physical_jet(w,s,3))/(2*mp.pi))
        px=mp.re((1+mp.pi/2)*(jm[0]-physical_jet(w,s-1,0))+
                    (jm[2]-physical_jet(w,s-1,2))/(2*mp.pi))
        deriv=px+sx*ps;pred=c/deriv
        L=mp.re((1+mp.pi/2)*js[0]+js[2]/(2*mp.pi))
        def residual(t): return (physical(w+t*pred,m)-L)/c
        ratio=mp.findroot(residual,(mp.mpf('.99'),mp.mpf('1.01')),tol=mp.mpf('1e-45'))
        refinement=abs(physical(w,m,64)-physical(w,m,96))
        leading=mp.pi*w*mp.exp(-w)/mp.log(w) if m==0 else (-1)**m*2*mp.pi*mp.factorial(m-1)*w**(1-m)*mp.exp(-w)/mp.log(w)**2
        assert deriv>0 and abs(ratio-1)<mp.mpf('.001')
        assert refinement<mp.mpf('1e-45') and res<mp.mpf('1e-65')
        row=dict(m=m,N=1,w=str(w),displacement=mp.nstr(ratio*pred,48),
          exact_derivative_prediction=mp.nstr(pred,48),ratio=mp.nstr(ratio,48),
          leading_asymptotic_ratio=mp.nstr(ratio*pred/leading,40),
          moving_order_derivative=mp.nstr(sx*ps,40),
          neutral_residual=mp.nstr(res,10),cauchy_refinement_error=mp.nstr(refinement,10),
          scaled_inverse_residual=mp.nstr(abs(residual(ratio)),10),seconds=time.time()-started)
        rows.append(row);print(json.dumps(row),flush=True)
Path(__file__).with_name('neutral-inverse-experiment.json').write_text(json.dumps(dict(status='passed',dps=75,scope='Non-interval numerical diagnostics, N=1 only',records=rows),indent=2)+'\n')
