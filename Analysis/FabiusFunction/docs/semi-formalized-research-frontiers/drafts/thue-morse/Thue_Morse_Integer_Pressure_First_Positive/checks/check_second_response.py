"""Independent exact Fourier calculation of the second normalized eigenfunction jet."""
# ed. (2026-10-01): results are written to <output-dir>/<name>, by default
# data/rerun/ in the package, with LF line endings (as delivered the program
# overwrote its recorded result, with CRLF on Windows). Pass --output-dir
# with the recorded file's directory, on a copy, to regenerate the recorded file.
def _ed_write(name, text):
    import argparse
    from pathlib import Path as _EdPath
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=_EdPath,
                        default=_EdPath(__file__).resolve().parents[1] / 'data' / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))

from pathlib import Path
import json
import sympy as s

def check(m):
    I=list(range(1-m,m));d=len(I)
    def a(j):return s.Rational(s.binomial(2*m,m+j),4**m) if -m<=j<=m else s.S.Zero
    V=s.Matrix(d,d,lambda k,r:2*a(2*I[k]-I[r]))
    B1=s.Matrix(d,d,lambda k,r:-2*(2*I[k]-I[r])*V[k,r])
    B2=s.Matrix(d,d,lambda k,r:(m-2*(2*I[k]-I[r])**2)*V[k,r])
    A=s.eye(d)-V
    assert s.ones(1,d)*A==s.zeros(1,d)
    C=A.copy();C[0,:]=s.ones(1,d)
    def solve(rhs,total):
        b=rhs.copy();b[0]=total
        x=C.inv()*b
        assert A*x==rhs and sum(x)==total
        return x
    h0=solve(s.zeros(d,1),1)
    u1=solve(B1*h0,0) # h1=i*u1
    h2=solve(-B1*u1+B2*h0,0)
    ev=s.Matrix(1,d,[(-1)**abs(r) for r in I])
    R=lambda n:(-1)**(n+1)*(2**(2*n)-1)*2**(2*n)*s.bernoulli(2*n)/s.factorial(2*n)
    assert (ev*h0)[0]==R(m)
    B=(ev*h2)[0]
    C_m=B+s.Rational(2*m,3)*R(m)-s.Rational(m,m+1)*R(m+1)
    assert B>0 and C_m>0
    return dict(m=m,R=str(R(m)),B=str(B),C=str(C_m),C_decimal=str(s.N(C_m,18)))
if __name__=='__main__':
    rows=[check(m)for m in range(2,11)]
    known={2:'376/45',3:'213/28',4:'16978624/3075975'}
    for row in rows:
        if row['m'] in known:assert row['C']==known[row['m']]
    result={'convention':'V_a = L_(atan(a)/pi) / cos(atan(a))^(2m), normalized h_a(0)=1','rows':rows,'source_m2_m3_m4_exactly_matched':True,'all_checks_passed':True}
    # ed. (2026-10-01): written by _ed_write (see above).
    _ed_write('second_response_checks.json', json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
