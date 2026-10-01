"""Independent standard-library validation of every saved parity trace.

This validates baseline vectors, all scalar error recurrences, dimensions,
final interval arithmetic, and exact/full-vector cross-comparisons. The
matrix inverses and per-coordinate rounding are certified in the audited
generator by exact identities and inequalities.
"""
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
from math import comb,factorial,gcd
from functools import reduce
from fractions import Fraction as Q
import gzip,json,sys,hashlib
sys.set_int_max_str_digits(0)
BASE=Path(__file__).resolve().parents[1]/'data'/'certificates'

def read_trace(path):
    opener=gzip.open if path.suffix=='.gz' else open
    with opener(path,'rt') as f:
        header=f.readline().split()
        scale=int(f.readline())
        even=tuple(map(int,f.readline().split()))
        odd=tuple(map(int,f.readline().split()))
        rows=[list(map(int,line.split())) for line in f]
    return header,scale,even,odd,rows

def audit(m):
    p=BASE/f'parity_m{m:03d}.json'
    tp=Path(str(p)+'.trace.gz')
    if not tp.exists():tp=Path(str(p)+'.trace')
    if not p.exists() or not tp.exists():return None
    z=json.loads(p.read_text());head,S,ev,od,rows=read_trace(tp);d=2*m;D=2**(d-1)
    assert head==['TMP1',str(m),str(d),'256']
    assert z['m']==m and z['precision_bits']==256 and z['checked_response_orders']==d
    assert len(rows)==d+1
    assert all(len(row)==m+1-(n%2) for n,row in enumerate(rows))
    e=[1]
    for r in range(2,d):
        e=[(k+1)*(e[k] if k<len(e) else 0)+(r-k)*(e[k-1] if k else 0) for k in range(r)]
    den=factorial(d-1);g=reduce(gcd,e,den);e=[v//g for v in e];den//=g
    assert S==2**256*den**2==int(z['common_denominator'])
    assert rows[0][:-1]==[e[m-1+k]*(S//den) for k in range(m)]
    assert rows[0][-1]==0
    errors=[row[-1] for row in rows]
    for n in range(1,d+1):
        alpha,q=ev if n%2==0 else od
        assert alpha>=0 and q>0
        bound=alpha*D*sum(comb(d,j)*errors[n-j] for j in range(1,n+1))
        round_cost=d-1 if n%2==0 else d-2
        assert errors[n]==(bound+q-1)//q+round_cost
    v=rows[-1][:-1]
    mid=(v[0]+2*sum((-1)**k*v[k] for k in range(1,m)))*(-1)**m
    assert mid-errors[-1]==int(z['H_lower_numerator'])>0
    assert mid+errors[-1]==int(z['H_upper_numerator'])
    assert errors[-1]==int(z['error_radius_numerator'])
    lo,hi=Q(mid-errors[-1],S),Q(mid+errors[-1],S)
    exact=False;full=False
    ep=BASE/f'gmp_m{m:03d}.json'
    if not ep.exists():ep=BASE/f'm{m:03d}.json'
    if ep.exists():
        ex=json.loads(ep.read_text());v=Q(ex['H_boundary_numerator'])/Q(ex['H_boundary_denominator'])
        assert lo<=v<=hi;exact=True
    fp=BASE/f'fixed_m{m:03d}.json'
    if fp.exists():
        old=json.loads(fp.read_text());l=Q(old['H_lower_numerator'])/Q(old['common_denominator']);u=Q(old['H_upper_numerator'])/Q(old['common_denominator'])
        assert max(lo,l)<=min(hi,u);full=True
    return {'m':m,'orders':d,'exact_rational_comparison':exact,
       'full_vector_comparison':full,'positive_margin_bits':mid.bit_length()-errors[-1].bit_length(),
       'json_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
       'trace_sha256':hashlib.sha256(tp.read_bytes()).hexdigest()}

if __name__=='__main__':
    good=[];missing=[]
    for m in range(2,70):
        r=audit(m)
        if r is None:missing.append(m)
        else:good.append(r)
    out={'range':[2,69],'certified_moments':len(good),'checked_response_orders':sum(r['orders'] for r in good),
         'missing':missing,'records':good,'complete':not missing}
    # ed. (2026-10-01): written by _ed_write (see above).
    _ed_write('trace_checks.json', json.dumps(out,indent=2)+'\n')
    print('Verified',len(good),'moment traces;',out['checked_response_orders'],'response orders; missing:',missing)
    # ed. (2026-10-01): an absent trace is reported, not passed over in silence; the exit
    # status is unchanged (as delivered, this audit verifies nothing without the trace archives).
    if missing:print('WARNING: trace audit incomplete:',len(missing),'of 68 trace files absent (complete: false)',flush=True)
