#!/usr/bin/env python3
"""Finite accepting/rejecting controls for packed positivity translation."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
def check(ok,label):
    if not ok:raise ValueError(label)
def main():
    # Raw positive equations p1+p2=5 and p1*p2=6. Here p_i=n_i+1.
    # w=(0,1,3), E=(6,13), reversed factorial-weighted residuals:
    # r1=p1+p2-5; r2=6-p1*p2.
    b=4;B=1024*b*b;M=19
    ell=B+B**3
    D=B**5+B**3-10*B**6+12*B**13-B**9
    N0=B**4;N1=4*B**20;N=N0*N1
    mask=N0-1-(b-1)*ell
    Q=(B-2)*(B**6+B**13)
    T=mask+Q*N0
    accepted=[];tested=0
    for n1 in range(b):
        for n2 in range(b):
            g=n1*B+n2*B**3
            J=2*(1+g+ell)**2*D+sum(B**(i+1) for i in range(M+1))
            S=g+J*N0
            truth=(n1+1)+(n2+1)==5 and (n1+1)*(n2+1)==6
            check((J&Q==0)==truth,'High target mask')
            check((S&T==0)==truth,'Combined mask')
            check(0<=S<N and 0<=T<N,'Broad block range')
            if truth:accepted.append([n1,n2])
            # A forbidden bit in the unselected B^2 block must reject.
            badg=g+B**2
            badJ=2*(1+badg+ell)**2*D+sum(B**(i+1) for i in range(M+1))
            badS=badg+badJ*N0
            check(badS&T!=0,'Invalid digit position rejected')
            tested+=1
    check(accepted==[[1,2],[2,1]],'Expected nonempty accepting control')
    receipt={'status':'PASS','test':'Raw positive equations with packed successor translation',
      'valid_digit_cases':tested,'accepting_digit_vectors':accepted,
      'rejecting_valid_digit_vectors':tested-len(accepted),'forbidden_position_cases':tested,
      'scope':'Finite toy controls; not tests of consistency.'}
    (ROOT/'certificates/toy.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
