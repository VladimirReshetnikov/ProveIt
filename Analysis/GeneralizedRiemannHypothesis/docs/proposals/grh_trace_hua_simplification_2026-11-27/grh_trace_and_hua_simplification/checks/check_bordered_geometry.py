#!/usr/bin/env python3
"""Independent exact source-shaped geometry checks for the bordered-Hua proposal.
These finite examples are not a proof or a Lean build. Requires SymPy.
"""
import argparse
import json
from pathlib import Path
import sympy as s

Q=s.Rational
checks=0
records=[]

def require(condition,label):
    global checks
    checks+=1
    if not bool(condition):raise AssertionError(label)

def eq(A,B):
    if isinstance(A,s.MatrixBase):return all(s.cancel(x)==0 for x in A-B)
    return s.cancel(A-B)==0

def setup(m,k):
    n=2*m+k+1; z=m+k
    J=s.zeros(n)
    for a in range(m):J[a,m+k+1+a]=J[m+k+1+a,a]=1
    for x in range(k):J[m+x,m+x]=1
    J[z,z]=-1
    F=s.eye(n)[:,list(range(m))+[z]]
    X=s.eye(n)[:,list(range(m,m+k))]
    return J,F,X,z

def unipotent(m,k,A):
    n=2*m+k+1; N=s.eye(n); start=m+k+1
    N[:m,m:m+k]=-A
    N[m:m+k,start:]=A.T
    N[:m,start:]=-A*A.T/2
    return N

def boost(m,k,c,t):
    n=2*m+k+1; z=m+k
    B=s.eye(n)
    B[m,m]=B[z,z]=c; B[m,z]=B[z,m]=t
    return B

def swap(m,k,i):
    P=s.eye(2*m+k+1); start=m+k+1
    for a in range(i):
        P[a,a]=P[start+a,start+a]=0
        P[a,start+a]=P[start+a,a]=1
    return P

def geometry(m,k,i,top=False):
    J,F,X,z=setup(m,k)
    y=unipotent(m,k,s.Matrix(m,k,lambda a,b:Q(a+b+1,3)))*boost(m,k,Q(5,3),Q(4,3))
    gamma=swap(m,k,i)
    if top:gamma=boost(m,k,Q(13,5),Q(12,5))*gamma
    require(eq(y.T*J*y,J),'y is J-unitary')
    require(eq(gamma.T*J*gamma,J),'gamma is J-unitary')
    E=s.eye(m+1)[:,list(range(i))+[m]]
    M=((s.eye(J.rows)-J)*F).T*y.inv()*F
    Py=M.inv()*((s.eye(J.rows)-J)*F).T*y.inv()
    Z=F.T*J*gamma*F; B=E.T*Z*E; D=Z*E*B.inv()
    Omega=J*Py.T*D; P=gamma*F*E*B.inv()
    H=-Omega.T*J*Omega; V=X.T*(P-Omega)
    W=y.inv()*Omega; C=y.inv()*F*E
    N=Py*gamma*F; K=Omega.T*J*P
    nu=abs(N.det()); delta=abs(B.det()); r=i+1
    require(eq(Py*F,s.eye(m+1)),'frame left inverse')
    require(eq(F.T*J*Omega,D),'canonical frame pairing')
    require(eq(E.T*D,s.eye(r)),'subframe duality')
    require(eq(F.T*J*P,D),'image frame pairing')
    require(eq(J*W,-W),'negative eigenspace')
    require(eq(C.T*W,-s.eye(r)),'negative dual cross Gram')
    require(eq(H,W.T*W),'positive Gram matrix')
    require(all(H[:j,:j].det()>0 for j in range(1,r+1)),'H positive definite')
    require(eq(V.T*V,(P-Omega).T*J*(P-Omega)),'definite coordinates preserve Gram')
    require(eq(nu,abs((D.T*N*E).det())),'direct frame determinant reduction')
    require(eq(K,D.T*N*E*B.inv()),'pairing determinant factorization')
    require(eq(abs(K.det()),nu/delta),'delta normalization')
    require(eq(-K-K.T-(H+V.T*V),-P.T*J*P),'Ostrowski hypothesis identity')
    require(nu>=delta*(H+V.T*V).det()/2**r,'desired lower volume bound')
    require((C.T*C).det()*H.det()>=1,'determinant Cauchy-Schwarz')
    fullC=y.inv()*F
    rho2=max((fullC.T*fullC)[a,a] for a in range(m+1))
    require(1/H.det()<=rho2**r,'rho factor without normalized L')
    h=H[i,i]; v=V[:,i]
    a=s.cancel(h+(v.T*v)[0])
    if not top:
        require(eq(a,1),'lower-level energy exactly one')
    else:
        require(eq(D,s.eye(m+1)),'top-level D=I')
        theta2=sum(t*t for t in y) # ||y||_F^2, which bounds ||y||_op^2.
        require(h*theta2>=1,'top-level theta pairing bound with u=I')
        require(a*theta2>=1,'top-level bordered energy bound')
    # A physical Bessel translate, not just an abstract matrix perturbation.
    A=s.zeros(m,k)
    for aa in range(i):
        for bb in range(k):A[aa,bb]=Q(2*aa-bb+1,4)
    gamma2=unipotent(m,k,A)*gamma
    require(eq(F.T*J*gamma2*F,Z),'translated frame products unchanged')
    P2=gamma2*F*E*B.inv(); V2=X.T*(P2-Omega)
    predicted=V.copy(); predicted[:,:i]+=A[:i,:].T
    require(eq(V2,predicted),'actual affine shift V+[A*,0]')
    require(eq(V2[:,i],v),'last column fixed under source translation')
    records.append({'m':m,'k':k,'i':i,'level':'top' if top else 'lower',
                    'detH':str(H.det()),'last_energy':str(a),'delta':str(delta),
                    'nu':str(nu),'volume_lower_bound':str(delta*(H+V.T*V).det()/2**r)})

def main():
    for m,k in [(1,1),(2,2),(2,7)]:
        for i in range(m+1):geometry(m,k,i)
        geometry(m,k,m,top=True)
    return {'status':'PASS','assertion_count':checks,'case_count':len(records),
            'sympy_version':s.__version__,
            'scope':'Exact rational J-unitary, canonical-frame, volume, rho/energy, and physical unipotent-shift regressions, including i=0 and k=7. Not a proof or Lean build.',
            'cases':records}

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    result=main()
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='cases'},indent=2))
