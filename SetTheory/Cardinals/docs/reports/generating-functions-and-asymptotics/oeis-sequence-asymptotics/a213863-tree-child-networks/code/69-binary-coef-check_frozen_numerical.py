#!/usr/bin/env python3
"""Independent numerical check using only the exact Jacobi matrix."""
import json
from pathlib import Path
import numpy as np
from scipy.linalg import eigh_tridiagonal
from scipy.special import ai_zeros

z=float(ai_zeros(1)[0][0]); ell=z*(2/3)**(2/3)
rows=[]
for N in (200,500,1000,2000,5000,10000,20000):
    e=N**(-1/3)
    # Edge b_(N,k), k=1,...,N+1; sites 0,...,N+1.
    k=np.arange(1,N+2,dtype=float)
    b=np.sqrt((3*N+k-2)/(3*(N+k)))
    vals,vec=eigh_tridiagonal(np.zeros(N+2),b,select='i',select_range=(N+1,N+1),tol=1e-14)
    val=float(vals[0]); endpoint=abs(float(vec[0,0]))
    approx=2+ell*e**2-e**3/3+3*ell**2*e**4/4+ell*e**5/18+(1143*ell**3-940)*e**6/2520
    normend=endpoint/(np.sqrt(2/3)*e**1.5)
    row={'N':N,'lambda':val,'lambda_remainder_over_e7':(val-approx)/e**7,'endpoint_ratio':normend,'endpoint_remainder_over_e4':(normend-1-ell*e**2-e**3/3)/e**4}
    rows.append(row);print(row)
Path(__file__).with_name('frozen-numerical.json').write_text(json.dumps({'z':z,'ell':ell,'rows':rows},indent=2)+'\n')
