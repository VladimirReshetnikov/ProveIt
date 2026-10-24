#!/usr/bin/env python3
"""Independent small arithmetic/expanded-polynomial checks of the lift variant.

The copied upstream checker is run separately as an explicitly pinned audit.
This file imports neither the generator nor the arithmetic Builder.
"""
from collections import Counter,defaultdict
import hashlib
import itertools
import json
from math import comb,factorial,gcd,prod
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]


def need(ok,text):
    if not ok:raise RuntimeError(text)


def sha(raw):return hashlib.sha256(raw).hexdigest()


def crt(residues,moduli):
    P=prod(moduli)
    return sum(r*(P//d)*pow(P//d,-1,d)for r,d in zip(residues,moduli))%P


def supported_part(F,d):
    part,remaining=1,F
    while (g:=gcd(remaining,d))>1:
        part*=g;remaining//=g
    need(F==part*remaining and gcd(remaining,d)==1,'supported factorial part')
    return part


def lift_controls():
    cases,noncoprime=0,0
    for N in range(1,4):
        for H in range(N,N+3):
            T=factorial(H);ds=[1+(i+1)*T for i in range(N)];B=prod(ds)
            need(all(gcd(d,e)==1 for i,d in enumerate(ds)for e in ds[:i]),'base CRT moduli')
            C=crt(list(range(N)),ds)
            need((1+(C+1)*T)%B==0,'independent index CRT')
            for u in range(7):
                F=factorial(u+1)
                lifted=[d*supported_part(F,d)for d in ds]
                period=prod(lifted)
                need(all(gcd(d,e)==1 for i,d in enumerate(lifted)for e in lifted[:i]),'lifted CRT moduli')
                for ws in itertools.product(range(u+1),repeat=N):
                    A=crt(ws,lifted)+(u+1)*period
                    need(A>u and all((A-w)%d==0 for w,d in zip(ws,lifted)),'positive strengthened CRT column')
                    choose=comb(A,u+1)
                    need(choose%B==0,'factorial-free bound without H>=u+1')
                    need(all((prod(A-r for r in range(u+1)))%(d*supported_part(F,d))==0 for d in ds),'falling numerator valuations')
                    cases+=1
                    if gcd(F,B)>1:noncoprime+=1
    need(comb(1,3)%3==0 and comb(1+3,3)%3!=0,'adding only B is unsafe negative control')
    need(comb(1+9,3)%3==0,'stronger lift restores safe period')
    return dict(total=cases,noncoprime_factorial_cases=noncoprime,
                independent_index_CRT=True,plain_B_shift_negative_control=True)


def equation_check(name):
    directory=HERE/name
    eq=json.loads((directory/'equation.json').read_text())
    polynomial=json.loads((directory/'expanded_polynomial.json').read_text())
    n=len(eq['variables']);result=defaultdict(int);used=set()
    for row in eq['residuals']:
        need(len({tuple(m)for c,m in row['terms']})==len(row['terms']),'row monomial uniqueness')
        for c,m in row['terms']:
            need(type(c)is int and c!=0 and len(m)<=2 and m==sorted(m)and all(type(i)is int and 0<=i<n for i in m),'literal quadratic row')
            used.update(m)
        for a,ma in row['terms']:
            for b,mb in row['terms']:
                result[tuple(sorted(ma+mb))]+=a*b
    expected={m:c for m,c in result.items()if c}
    actual={tuple(m):c for c,m in polynomial['terms']}
    need(expected==actual and len(actual)==len(polynomial['terms']),'exact whole quartic expansion')
    need(used==set(range(n))and max(map(len,actual))==4,'all variables live/exact quartic')
    metrics=eq['metrics']
    need(metrics['variables']==n and metrics['expanded_monomials']==len(actual)and metrics['max_abs_expanded_coefficient']==max(map(abs,actual.values())),'literal metrics')
    return dict(metrics=metrics,equation_sha256=sha((directory/'equation.json').read_bytes()),
                polynomial_sha256=sha((directory/'expanded_polynomial.json').read_bytes()))


def main():
    pins=json.loads((HERE/'SOURCE_PINS.json').read_text())
    archive=REPO/pins['archive']
    need(sha(archive.read_bytes())==pins['archive_sha256'],'original actual ZIP')
    with zipfile.ZipFile(archive)as z:
        for name,item in pins['files'].items():
            original=z.read(item['original_member']);candidate=(HERE/'source'/name).read_bytes()
            need(sha(original)==item['original_sha256']and sha(candidate)==item['candidate_sha256'],'complete source pins')
            if name=='build_equation.py':
                wanted=original.replace(b'    V = b.add(m, U)\n',b'    V = U  # Independent private-coordinate bound; prime-power CRT lift.\n').replace(b'    H = b.sum([ep, fp, t, V, ONE])\n',b'    H = b.sum([ep, fp, t])  # No local factorial cancellation is needed.\n')
                need(wanted==candidate,'only two source changes')
            else:need(original==candidate,'all other source/arithmetic/audit modules unchanged')
    audits=[]
    with tempfile.TemporaryDirectory(prefix='proveit-shared-lift-audit-')as tmp:
        flags=['-O']if sys.flags.optimize else[]
        for variant in ['affine','retained']:
            output=Path(tmp)/(variant+'.json')
            cmd=[sys.executable,'-B',*flags,str(HERE/'source/check_equation.py'),'--directory',str(HERE/'source'),'--equation-directory',str(HERE/variant),'--output',str(output)]
            p=subprocess.run(cmd,text=True,capture_output=True)
            need(p.returncode==0,'pinned upstream arithmetic/positivity/affine audit: '+p.stderr)
            audits.append(json.loads(output.read_text()))
        output=Path(tmp)/'power.json'
        p=subprocess.run([sys.executable,'-B',*flags,str(HERE/'source/audit_power_graph.py'),'--output',str(output)],text=True,capture_output=True)
        need(p.returncode==0,'exact17constraint positive-power audit')
        power=json.loads(output.read_text())
    result=dict(status='PASS',python_optimization=sys.flags.optimize,
                prime_lift_controls=lift_controls(),variants={name:equation_check(name)for name in ['affine','retained']},
                independent_upstream_audits=audits,unchanged_power_identity_audit=power,
                scope='Exact source patch/pins/full quartic expansion, prime-lift controls and pinned arithmetic/affine auditors; ordinary universal proof in PROOF.md. No Lean/internal-ZFC derivation.')
    target=HERE/('CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json')
    target.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS full quartics, exact2line transformation, prime-power lift and arithmetic/affine audits')


if __name__=='__main__':main()
