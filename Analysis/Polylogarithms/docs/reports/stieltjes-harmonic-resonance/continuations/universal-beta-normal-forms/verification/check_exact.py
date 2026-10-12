"""Independent exact checks and reproducible coefficient/primitive certificates."""
from __future__ import annotations
import argparse, csv, json, platform
from fractions import Fraction as F
from pathlib import Path
from time import perf_counter
from gamma_coefficients import coefficient, mixed_square
from independent_ibp import hierarchy, norm, prim, dp, add, trim
ROOT=Path(__file__).resolve().parents[1]


def partial(p,j):
    out={}
    for e,c in p.items():
        if j<len(e) and e[j]:
            f=list(e);f[j]-=1;key=trim(f)
            out[key]=out.get(key,F(0))+c*e[j]
    return {e:c for e,c in out.items() if c}


def times_variable(p,j):
    out={}
    for e,c in p.items():
        f=list(e)+[0]*max(0,j+1-len(e));f[j]+=1;key=trim(f)
        out[key]=out.get(key,F(0))+c
    return out


def homotopy(p):
    """Euler homotopy primitive for positive-factor-degree total derivatives."""
    pieces={}
    for e,c in p.items():pieces.setdefault(sum(e),{})[e]=c
    out={}
    for degree,piece in pieces.items():
        if degree==0:
            if piece:raise ValueError("Nonzero scalar has no polynomial primitive.")
            continue
        maximum=max((len(e) for e in piece),default=0)
        for r in range(1,maximum):
            q=partial(piece,r)
            for j in range(r):
                out=add(out,times_variable(q,r-1-j),F((-1)**j,degree))
                q=dp(q)
    return out


def serialize(p):
    return [{"exponents":list(e),"coefficient":str(c)} for e,c in sorted(p.items())]


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--weight',type=int,default=32)
    parser.add_argument('--output',type=Path,default=ROOT/'data')
    args=parser.parse_args()
    if args.weight<14:parser.error('Use --weight >= 14 to include the corruption controls.')
    args.output.mkdir(parents=True,exist_ok=True);start=perf_counter()
    counts=dict(coefficient_comparisons=0,support_sign_checks=0,primitive_identities=0,
                homotopy_comparisons=0,appell_checks=0,mixed_square_checks=0,
                corruption_controls=0)
    rows=[];snapshots={};per_weight=[]
    for m,A in enumerate(hierarchy(args.weight)):
        N=norm(A)
        keys=set(N)|{e for e in A if len(e)<=1 or e[-1]>=2}
        for e in sorted(keys):
            expected,observed=coefficient(e),N.get(e,F(0))
            assert observed==expected,(m,e,observed,expected)
            counts['coefficient_comparisons']+=1
            if len(e)>=2:
                parity=sum(j*e[j] for j in range(1,len(e)))%2
                assert (observed==0)==bool(parity)
                if observed:assert (observed>0)==((len(e)-1)%2==0)
                counts['support_sign_checks']+=1
            rows.append((m,','.join(map(str,e)),str(observed)))
        if m:
            assert partial(N,0)=={e:m*c for e,c in previous.items()}
            counts['appell_checks']+=1
        previous=N
        if m<=28:
            H=prim(A)
            assert A==add(N,dp(H)),('primitive',m)
            counts['primitive_identities']+=1
            if m<=18:
                assert homotopy(add(A,N,-1))==H,('homotopy',m)
                counts['homotopy_comparisons']+=1
            if m in [4,8,11,14,18]:
                snapshots[str(m)]={'A':serialize(A),'N':serialize(N),'H':serialize(H)}
        for r in range(3,8):
            for b in range(6):
                for k in range(7):
                    a=m-2*k-3*b-2*r-2
                    if a<0:continue
                    e=[a,k,b]+[0]*(r-2);e[r]=2
                    assert mixed_square(a,k,b,r)==N.get(trim(e),F(0))
                    counts['mixed_square_checks']+=1
        per_weight.append({'weight':m,'bell_terms':len(A),'normal_terms':len(N),
                           'functional_slots':len(keys)})
        if m%4==0:print('checked weight',m,'slots',counts['coefficient_comparisons'],flush=True)
    # Corrupt the actual normal-form certificates while retaining the original primitive.
    # The independently reconstructed A=N+D H identity must then fail.
    def unpack(rows):
        return {tuple(row['exponents']):F(row['coefficient']) for row in rows}
    for m,e,delta in [(11,(0,0,1,2),F(165,4)),(14,(0,1,0,3),F(1))]:
        snap=snapshots[str(m)]
        A,N,H=unpack(snap['A']),unpack(snap['N']),unpack(snap['H'])
        corrupted=N.copy();corrupted[e]+=delta
        assert A!=add(corrupted,dp(H))
        assert coefficient(e)!=corrupted[e]
        counts['corruption_controls']+=1
    assert coefficient((0,0,1,2))==-55
    assert coefficient((0,1,0,3))==F(-3185,3)
    assert coefficient((0,0,2,2))==-3640
    with (args.output/'normal_coefficients.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['weight','exponents_u0_u1_etc','coefficient']);w.writerows(rows)
    (args.output/'primitive_certificates.json').write_text(json.dumps(snapshots,indent=2)+'\n')
    receipt={'status':'PASS','maximum_weight':args.weight,'counts':counts,
             'per_weight':per_weight,'python':platform.python_version(),
             'elapsed_seconds':round(perf_counter()-start,3),
             'scope':'Finite exact checks; the all-order theorem is proved in article.tex.'}
    (args.output/'exact_checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(counts,indent=2));print('PASS; seconds',receipt['elapsed_seconds'])

if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Verification requires assertions; do not use python -O.')
    main()
