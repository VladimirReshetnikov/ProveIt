#!/usr/bin/env python3
"""Exact polynomial proof cuts and source pins for the eleven-integer proof."""
from pathlib import Path
import sys,json,hashlib,gzip
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'guard'))
from exact_polynomial import Ring

def require(ok,message):
    if not ok:raise ValueError(message)
def eq(a,b,name):require(not (a-b).terms,name)
def residue(p,m):return type(p)(p.ring,{e:c%m for e,c in p.terms.items() if c%m})
def main():
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for x in pins['sources']:
        b=(ROOT/x['path']).read_bytes()
        require(len(b)==x['bytes'] and hashlib.sha256(b).hexdigest()==x['sha256'],'source pin '+x['path'])
    ports=json.loads((ROOT.parent/'guard/coefficients/BINDING.json').read_text())['payloads']
    for name,x in ports.items():
        active=gzip.decompress((ROOT.parent/'guard/coefficients'/x['file']).read_bytes())
        for old in ['centered17','centered18']:
            require(active==gzip.decompress((ROOT/'provenance'/old/'coefficients'/(name+'.bin.gz')).read_bytes()),'tuple mismatch '+name)
    r=Ring(['u','H','D']);u,H,D=(r.var(n) for n in r.names)
    A=u**5+10*u**3*D+5*u*D**2+32*H**2*(u**3+3*u*D)+H**3*(u**2+D)+31*H**4*u+31*H**5
    B=5*u**4+10*u*u*D+D*D+32*H*H*(3*u*u+D)+2*H**3*u+31*H**4
    Q0=u*u+D+31*H*H;Q1=2*u
    C0=u**3+3*u*D+H*H*u+H**3;C1=3*u*u+D+H*H
    eq(A,Q0*C0+Q1*C1*D,'quintic even coefficient')
    eq(B,Q0*C1+Q1*C0,'quintic odd coefficient')
    eq(B,5*u**4+10*u*u*D+D*D+32*H*H*D+95*H*H*u*u+H*H*(u+H)**2+30*H**4,'positive odd-coefficient identity')
    r=Ring(['q','w','Y','c','T']);q0,w0,Y,c,T=(r.var(n) for n in r.names)
    q=3*q0+2;W=3*w0+1;X=residue(q*W,3)
    a=residue((X+1)*Y,3);H=residue(4*a+3,3);Delta=residue(a*a+H,3)
    b0=residue(X+a*c,3);u=residue(H*T-b0,3);Dm=residue(1+Delta*c*c,3)
    eq(H,r.scalar(0),'H is zero modulo 3')
    eq(u,r.scalar(1),'u is one modulo 3')
    eq(Dm,r.scalar(1),'Dm is one modulo 3')
    Amod=residue(u**5+10*u**3*Dm+5*u*Dm**2,3)
    eq(Amod,r.scalar(1),'A is one modulo 3')
    r=Ring(['D','s','r','c','T','R','Q','V','L','k','P','x','Y'])
    D,s,rr,c,T,R,Q,V,L,k,P,x,Y=(r.var(n) for n in r.names)
    I=2*s*rr*c*c;Df=1+D*I*I;b=c-R+4*I*T;Vactual=Df*b-c
    jaux=4*D*s*s*rr*rr*c**3*(c-R)+8*s*rr*c*Df*T
    eq(c*jaux-Vactual-R,r.scalar(0),'correct even-I auxiliary packing')
    eq(residue(Df,4),r.scalar(1),'Df odd')
    Qactual=D*D*I*I;delta=Qactual-1;Cy=Qactual*V*V-1;Da=delta*Cy
    eq(residue(Da,4),r.scalar(1),'Da one modulo 4')
    Dg=4*(3*P-4)*s*s+1
    eq(residue(Dg,4),r.scalar(1),'Dg one modulo 4')
    ell=8*x*Y*Y;Dt=1+ell*(ell+1)*k*k
    eq(residue(Dt,8),r.scalar(1),'Dt one modulo 8')
    Da=(Q-1)*(Q*V*V-1)
    eq(4*Da-((2*Q-1)*V)**2,-V*V-4*Q+4,'auxiliary centering correction')
    Dt=1+L*(L+k)
    eq(16*Dt-(4*L)**2,16*L*k+16,'first-Pell centering correction')
    result={'status':'PASS','source_files_authenticated':len(pins['sources']),
      'same_six_source34_coefficients':True,'exact_quintic_identities':3,
      'modulo_3_main_root_obstruction':True,'four_odd_radicand_certificates':True,
      'even_strong_auxiliary_packing':True,'exact_centering_identities':2,
      'boundary':'Exact proof-cut diagnostics, not a verification of the inherited unbounded native/compiler calibration.'}
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
