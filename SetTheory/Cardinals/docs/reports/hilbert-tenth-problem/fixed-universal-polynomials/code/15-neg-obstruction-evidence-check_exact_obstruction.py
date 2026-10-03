#!/usr/bin/env python3
"""Own exact arithmetic checks. Reads upstream JSON as data; never runs its schedule."""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import argparse,hashlib,json,math
ROOT=Path(__file__).resolve().parent


def require(condition, message):
    """Keep every check active under normal Python and python -O alike."""
    if not condition:
        raise RuntimeError("Check failed: " + str(message))


def identical(left, right):
    """Compare receipt JSON values including their exact Python types."""
    if type(left) is not type(right):
        return False
    if isinstance(left, dict):
        return left.keys() == right.keys() and all(identical(left[k], right[k]) for k in left)
    if isinstance(left, list):
        return len(left) == len(right) and all(identical(a, b) for a, b in zip(left, right))
    return left == right


def pell(A,n,mod=None):
    require(A >= 2 and n >= 0, 'A >= 2 and n >= 0')
    D=A*A-1
    def mul(x,y):
        a,b=x; c,d=y
        z=(a*c+D*b*d,a*d+b*c)
        return tuple(v%mod for v in z) if mod else z
    z=(1,0); x=(A,1)
    while n:
        if n&1:z=mul(z,x)
        x=mul(x,x);n//=2
    return z


def authenticate():
    m=json.loads((ROOT/'source_manifest.json').read_text())
    for x in m['files']:
        b=(ROOT/'sources'/x['file']).read_bytes()
        require(len(b) == x['bytes'], "len(b) == x['bytes']")
        require(hashlib.sha256(b).hexdigest() == x['sha256'], "hashlib.sha256(b).hexdigest() == x['sha256']")
        require(hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\x00' + b).hexdigest() == x['git_blob_sha1'], "hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\\x00' + b).hexdigest() == x['git_blob_sha1']")
    return len(m['files'])


def source_inventory():
    # Static text/data correspondence only: not a schedule interpreter.
    doc=json.loads((ROOT/'sources/complete74_nonlinear_index_projection_scout.json').read_text())
    lists={
      'raw30':'C F Jrep W Z a alpha c d delta eta f ga h i j k kappa mu o phi q rho s tau w y_aux zeta zquot'.split(),
      'positive22':'Jrep F alpha zquot f h i j o s w tau eta zeta ga y_aux Z W delta phi rho'.split()}
    out=[]
    for form in doc['forms']:
        p=form['packet']; mode=p['mode']
        if mode not in lists:continue
        require(p['witnesses'] == lists[mode], "p['witnesses'] == lists[mode]")
        rows={r[0]:r[1:] for r in p['source']}
        require(rows['restored_r'] == ['-', 'index_partial', 1], "rows['restored_r'] == ['-', 'index_partial', 1]")
        require(rows['index_partial'] == ['-', p['actual_k_port'], 'hpm1'], "rows['index_partial'] == ['-', p['actual_k_port'], 'hpm1']")
        require(rows['marked_rhs'] == ['+', 'Z', 'W'], "rows['marked_rhs'] == ['+', 'Z', 'W']")
        require(rows['gam'] == ['*', 'ga', 'a4m5'], "rows['gam'] == ['*', 'ga', 'a4m5']")
        require(rows['mask'] == ['*', 'mask_factor', 'Jrep'], "rows['mask'] == ['*', 'mask_factor', 'Jrep']")
        require(['restored_r', 'r_lhs'] in p['comparisons'], "['restored_r', 'r_lhs'] in p['comparisons']")
        require(['innerC', 'local_rhs_sum'] in p['comparisons'], "['innerC', 'local_rhs_sum'] in p['comparisons']")
        require(['raw_bound', 'q'] in p['comparisons'], "['raw_bound', 'q'] in p['comparisons']")
        require(len(p['comparisons']) == (18 if mode == 'raw30' else 10), "len(p['comparisons']) == (18 if mode == 'raw30' else 10)")
        out.append({'mode':mode,'witnesses':len(p['witnesses']),'comparisons':len(p['comparisons'])})
    return out


def packing_tests():
    count=negative=0
    # General bounded arithmetic fixtures, not actual compiled machines or full zeros.
    for q in range(4,33,2):
      Q=q*q-1
      for M in (1,q+1,Q//2,Q+7):
       for Z in range(1,q):
        for W in (1,2,q//2):
         for K in (1,q*q-1):
          X=q**3
          C=Z+W
          for z in (1,2,q):
           F0=(K+X)*C-z*(q-1)
           if F0<=0:continue
           p=(Z+q*F0-q*q)*Q-M
           count+=1
           if p<=0:continue
           negative+=1
           require((p + M) % Q == 0, '(p + M) % Q == 0')
           N=(p+M)//Q; Z1=N%q;F1=q+(N-Z1)//q
           require((Z1, F1) == (Z, F0), '(Z1, F1) == (Z, F0)')
           require(((K + X) * (Z1 + W) - F1) // (q - 1) == z, '((K + X) * (Z1 + W) - F1) // (q - 1) == z')
           require(-p == (q * q - Z1 - q * F1) * Q + M, '-p == (q * q - Z1 - q * F1) * Q + M')
    return {'arithmetic_fixtures':count,'negative_packing_reconstructions':negative}


def input_tests():
    disc=residue=0
    for A in range(4,40,2):
      D=A*A-1;H=4*A-5
      for u in range(3,18,2):
       for e in (u,u*A):
        kap,mu=None,None
        mu,kap=pell(A,e)
        require((kap - u) % D == 0 and (kap - u) // D > 0, '(kap - u) % D == 0 and (kap - u) // D > 0')
        W=pow(2,e,H)
        require((mu - (A - 2) * kap - W) % H == 0, '(mu - (A - 2) * kap - W) % H == 0')
        require((mu - (A - 2) * kap - W) // H > 0, '(mu - (A - 2) * kap - W) // H > 0')
        require(mu * mu - D * kap * kap == 1, 'mu * mu - D * kap * kap == 1')
        disc+=1
        residue+=1
    # Complete low-index auxiliary tuples for both odd classes. These are auxiliary only.
    aux=[]
    for A,p in ((2,3),(3,3),(2,1),(3,1)):
        D=A*A-1;c=pell(A,p)[1]
        m=c*p if p%4==3 else 2*c*p
        f,s=pell(A,m);T=D*s
        require(T % (c * c) == 0, 'T % (c * c) == 0')
        ell=p+2*m
        root,y=pell(T,ell)
        require(root % T == 0, 'root % T == 0')
        U=root//T
        require((U - p) % c == 0 and (U + c) % f == 0, '(U - p) % c == 0 and (U + c) % f == 0')
        j=(U-p)//c;o=(U+c)//f;i=T//(c*c)
        require(min(i, j, o, f, y) > 0, 'min(i, j, o, f, y) > 0')
        require(T * T == D * (f * f - 1), 'T * T == D * (f * f - 1)')
        require(T * T * (U * U - y * y) == 1 - y * y, 'T * T * (U * U - y * y) == 1 - y * y')
        require(U == j * c + p == o * f - c, 'U == j * c + p == o * f - c')
        aux.append({'A':A,'p':p,'p_mod4':p%4,'m':m,'U_bits':U.bit_length(),
                    'scope':'ordinary strong/auxiliary subsystem only'})
    # Modular divisibility check with genuine p>=13, both mod4 classes, no giant f.
    divisibility=0
    for A in (4,6,18,66):
      for p in (13,15,17,19):
        c=pell(A,p)[1];m=c*p if p%4==3 else 2*c*p
        require(pell(A, m, c * c)[1] == 0, 'pell(A, m, c * c)[1] == 0')
        require((p + 2 * m) % 4 == 1, '(p + 2 * m) % 4 == 1')
        divisibility+=1
    return {'discriminant_cases':disc,'input_residue_cases':residue,'auxiliary_materialized':aux,
            'large_index_auxiliary_divisibility_cases':divisibility}


def add(x,y):return (x[0]+y[0],x[1]+y[1])
def sub(x,y):return (x[0]-y[1],x[1]-y[0])
def scale(x,c):return (x[0]*c,x[1]*c) if c>=0 else (x[1]*c,x[0]*c)
def divpos(x,y):
    require(x[0] > 0 and y[0] > 0, 'x[0] > 0 and y[0] > 0')
    return (x[0]/y[1],x[1]/y[0])


def log_series(z,N):
    require(0 <= z <= F(1, 3), '0 <= z <= F(1, 3)')
    z2=z*z;power=z;s=F(0)
    for j in range(N):
        s+=power/(2*j+1);power*=z2
    lo=2*s;err=2*power/((2*N+1)*(1-z2))
    return lo,lo+err

@lru_cache(maxsize=None)
def log_bounds(r,N=36):
    r=F(r);require(r > 0, 'r > 0')
    if r<1:
        lo,hi=log_bounds(1/r,N);return -hi,-lo
    k=r.numerator.bit_length()-r.denominator.bit_length()
    while F(2)**k>r:k-=1
    while F(2)**(k+1)<=r:k+=1
    t=r/F(2)**k
    z=(t-1)/(t+1)
    return add(scale(log_series(F(1,3),N),k),log_series(z,N))

@lru_cache(maxsize=None)
def window_coefficients(q,w,s):
    X=w*q**3;Y=s*q**3;E=X*Y;A=Y*(X+1)+2;P=2*X*Y*Y+1
    amin=F(2*A*A-1,A);amax=F(4*A*A-1,2*A)
    bmin=F(2*P*P-1,P);bmax=F(4*P*P-1,2*P)
    zA=F(1,(2*A-1)**26);zP=F(1,(2*P-1)**14)
    lrmin=add(log_bounds(F(P*P-1,2*A*P)),(-2*zA,-zA))
    lrmax=add(log_bounds(F(P*A,2*(A*A-1))),(zP,2*zP))
    return X,Y,E,log_bounds(amin),log_bounds(amax),log_bounds(bmin),log_bounds(bmax),lrmin,lrmax


def candidate_window(q,w,s,t):
    X,Y,E,la0,la1,lb0,lb1,lr0,lr1=window_coefficients(q,w,s)
    half=F(t*E+1,2)
    lower=divpos(add(sub(log_bounds(F(Y)),lr1),scale(lb0,half)),add(la1,scale(lb0,F(1,2))))
    upper=divpos(add(sub(log_bounds(F(Y+1)),lr0),scale(lb1,half)),add(la0,scale(lb1,F(1,2))))
    # Widen outwards; strict integer window uses lower[0] and upper[1].
    lo=max(13,math.ceil(F(t*E,3))+1,math.floor(lower[0])+1)
    hi=min(X*q**4-1,(t*E-6)//2,math.ceil(upper[1])-1)
    if lo%2==0:lo+=1
    if hi%2==0:hi-=1
    return lo,hi,upper[1]-lower[0]


def ratio_bound_tests():
    count=0
    for X,Y in ((4,3),(8,5),(16,16),(64,17),(4096,4096)):
      A=Y*(X+1)+2;P=2*X*Y*Y+1
      amin=F(2*A*A-1,A);amax=F(4*A*A-1,2*A)
      bmin=F(2*P*P-1,P);bmax=F(4*P*P-1,2*P)
      rmin=F(P*P-1,2*A*P)*(1-F(1,(2*A-1)**26))
      rmax=F(P*A,2*(A*A-1))/(1-F(1,(2*P-1)**14))
      for p in range(13,30,2):
       for n in range(max(7,(p+1)//2),p):
        ratio=F(pell(A,p)[1],2*pell(P,n)[1])
        require(rmin * amin ** p / bmax ** n < ratio < rmax * amax ** p / bmin ** n, 'rmin * amin ** p / bmax ** n < ratio < rmax * amax ** p / bmin ** n')
        count+=1
    return count


def scale_grid():
    total=empty=0;survivors=[];max_width=F(0)
    # Each grid point checks every permitted s,t, with exact outward rational intervals.
    # This is a relaxed arithmetic scale grid, not an actual compiler slice assertion.
    digest=hashlib.sha256()
    for q in (16,20,32):
     for w in (1,2,3,4):
      for s in range(1,3*q):
       for t in range(1,(3*q-1)//s+1):
        lo,hi,width=candidate_window(q,w,s,t)
        total+=1;max_width=max(max_width,width)
        require(width < F(1, q ** 3) + F(1, q ** 5), 'width < F(1, q ** 3) + F(1, q ** 5)')
        digest.update(f'{q},{w},{s},{t},{lo},{hi}\n'.encode())
        if lo>hi:empty+=1
        else:survivors.append([q,w,s,t,lo,hi])
    require(max_width < F(1, 100000), 'max_width < F(1, 100000)')
    return {'q':[16,20,32],'w':[1,2,3,4],'s':'all 1..3q-1',
      't':'all 1..floor((3q-1)/s)','cases':total,'no_odd_integer_in_necessary_window':empty,
      'surviving_windows':survivors,'maximum_outward_window_width_less_than':str(F(1,100000)),
      'maximum_width_display_only':float(max_width),'case_digest_sha256':digest.hexdigest(),
      'scope':'exact necessary first/main ratio window exclusions; no upstream schedule run and no full negative zero materialized'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,help='Optional receipt output path; default is stdout only')
    parser.add_argument('--expect',type=Path,help='Compare against a frozen expected JSON receipt')
    args=parser.parse_args()
    if args.output is not None:
        destination=args.output.resolve()
        require(destination!=ROOT and ROOT not in destination.parents, '--output must be outside the packet')
        if args.expect is not None:
            require(destination!=args.expect.resolve(), '--output must not overwrite --expect')
    result={'source_files_authenticated':authenticate(),'static_source_inventory':source_inventory(),
      'packing':packing_tests(),'input_and_auxiliary':input_tests(),'exact_Binet_ratio_cases':ratio_bound_tests(),
      'scale_grid':scale_grid(),'scope':'corroboration and explicit finite exclusions, not unbounded sign proof'}
    result['checker_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    encoded=json.dumps(result,sort_keys=True,indent=2,allow_nan=False)+'\n'
    require(identical(result,json.loads(encoded)), 'JSON roundtrip changed receipt types or values')
    if args.expect is not None:
        expected_bytes=args.expect.read_bytes()
        expected=json.loads(expected_bytes)
        require(identical(result,expected), 'Receipt values do not match --expect')
        require(encoded.encode('utf-8')==expected_bytes, 'Canonical receipt bytes do not match --expect')
    if args.output is not None:
        args.output.write_text(encoded)
    print(encoded,end='')


if __name__=='__main__':
    main()
