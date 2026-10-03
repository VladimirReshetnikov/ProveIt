"""First correction from Euler--Maclaurin, Fourier saddle and Gamma tilt."""
import json
from pathlib import Path
import mpmath as mp
mp.mp.dps=60
out={}
for eta in [1,-1]: # +1 Bose, -1 Fermi
    rho=lambda x,c:1/(mp.exp(c*x+x*x/2)-eta)
    c=mp.findroot(lambda c:mp.quad(lambda x:x*rho(x,c),[0,1,mp.inf])-1,mp.mpf('.76') if eta==1 else mp.mpf('-.32'))
    def cumulant(x,j):
        r=rho(x,c)
        if j==1:return r
        if j==2:return r*(1+eta*r)
        if j==3:return r*(1+eta*r)*(1+2*eta*r)
        if j==4:return r*(1+eta*r)*(1+6*eta*r+6*r*r)
    def integ(j,k):return mp.quad(lambda x:x**k*cumulant(x,j),[0,1,mp.inf])
    M={k:integ(1,k) for k in range(1,5)}
    V={k:integ(2,k) for k in range(2,7)}
    W={k:integ(3,k) for k in range(3,6)}
    J4=integ(4,4); J3=-W[3]; variance=V[2]
    alpha=M[2]/2
    # E over Z~N(alpha,1), implemented exactly for polynomials up to degree 3.
    Ez=[1,alpha,1+alpha**2,alpha**3+3*alpha]
    boundary= -c/24-5/(24*c) if eta==1 else c/24
    H1=[boundary+3*M[2]/4-3*M[4]/8+V[2]/8-V[4]/6+V[6]/18,
        -M[1]/2+2*M[3]/3+V[3]/4-V[5]/6,
        -M[2]/2+V[4]/8]
    dp=1/(2*c) if eta==1 else 0
    dpp=-1/(2*c*c) if eta==1 else 0
    # A'/A=l0+l1*z and (log A)''=m0+m1*z.
    l0=dp-V[2]/2+V[4]/3; l1=-V[3]/2
    m0=dpp+W[3]/2-W[5]/3; m1=W[4]/2
    D=[-(m0+l0*l0)/(2*variance)+J3*l0/(2*variance**2)+J4/(8*variance**2)-5*J3**2/(24*variance**3),
       -(m1+2*l0*l1)/(2*variance)+J3*l1/(2*variance**2),
       -l1*l1/(2*variance)]
    a1=sum((H1[j]+D[j])*Ez[j] for j in range(3))+Ez[3]/3
    kind='unrestricted' if eta==1 else 'distinct'
    out[kind]={"c":str(c),"a1":str(a1),"H1":list(map(str,H1)),"D":list(map(str,D)),"M":{str(k):str(v) for k,v in M.items()},"V":{str(k):str(v) for k,v in V.items()},"W":{str(k):str(v) for k,v in W.items()},"J4":str(J4)}
    print(kind,'a1 =',mp.nstr(a1,50))
    for name,p in [('Euler-Maclaurin/Stirling',H1),('Fourier saddle',D)]:print(name,mp.nstr(sum(p[j]*Ez[j] for j in range(3)),30))
    print('Gamma correction',mp.nstr(Ez[3]/3,30))
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2))
