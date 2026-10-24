#!/usr/bin/env python3
"""Literal quartic and redundant-lower-bound/common-bound arithmetic checks; no Lean."""
from collections import defaultdict
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path
import subprocess
import sys
import tempfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=HERE.parent/'shared-crt-fixed-power-bound'


def need(ok,text):
    if not ok:raise RuntimeError(text)


def sha(raw):return sha256(raw).hexdigest()


def pell(a,j):
    x,y=1,0
    for _ in range(j):x,y=a*x+(a*a-1)*y,x+a*y
    return x,y


def arbitrary_bound_controls():
    cases=0
    for n in range(1,6):
        for k in range(1,6):
            for W in range(max(n,k),n+k+4):
                A,wz=pell(W+1,W)
                need(wz%W==0 and wz//W>=1,'canonical ordinate has positive quotient at arbitrary common bound')
                Z=wz//W;T=2*A*n-n*n-1;X,Y=pell(A,k)
                need(A>W>=n and W>=k,'ordinary subtraction/common-bound license')
                need(n**k<=n**W<(W+1)**W<=A,'cofinal construction power bound')
                need(0<n**k<T,'fresh output gap is natural')
                need((X+Y*n-Y*A-n**k)%T==0,'fresh power congruence')
                need(A*A-((W+1)**2-1)*(W*Z)**2==1,'fresh final norm')
                need(Y>=k and X*X-(A*A-1)*Y*Y==1,'indexed Pell inputs')
                cases+=1
    return dict(cases=cases,all_common_bounds=True,range='1<=n,k<=5; max(n,k)<=W<=n+k+3')


def derived_lower_bound_controls():
    positive_T_cases=0
    for n in range(1,31):
        need(n*n+1-2*n==(n-1)**2,'ordinary square gap identity')
        for A in range(31):
            T=2*A*n-n*n-1
            if T>=1:
                need(A>=2,'positive T forces A>=2')
                positive_T_cases+=1
    norm_order_cases=0
    for A in range(2,11):
        d=A*A-1
        for Y in range(1,31):
            X=isqrt(1+d*Y*Y)
            if X*X!=1+d*Y*Y:continue
            for V in range(Y,101):
                U=isqrt(1+d*V*V)
                if U*U!=1+d*V*V:continue
                need(U>=X>=A>=2 and 0<X-1<U,'retained norm ordering')
                need((X-1)%U!=0,'B=1 and S=1 cannot satisfy S=X mod U')
                norm_order_cases+=1
    positive_multiple_cases=0
    for Y in range(1,31):
        for vd in range(31):
            V=Y*Y*(vd+1)
            need(V-Y==Y*(Y-1)+Y*Y*vd and V>=Y,'retained positive-multiple order')
            positive_multiple_cases+=1
    need(norm_order_cases>0,'nonempty Pell norm controls')
    # Removing T>0 from the isolated A lemma really would be invalid.
    need(2*1*1==0+1*1+1,'zero-T A=1 negative control')
    return dict(positive_T_cases=positive_T_cases,norm_order_cases=norm_order_cases,
                positive_multiple_cases=positive_multiple_cases,zero_T_negative_control=True,
                scope='Finite controls of the exact inequalities; universal proofs in PROOF.md.')


def source_check():
    pins=json.loads((HERE/'SOURCE_PINS.json').read_text())
    need(pins['parent']=='candidates/shared-crt-fixed-power-bound','named frozen parent')
    changed=[]
    for name,item in pins['files'].items():
        raw=(PARENT/'source'/name).read_bytes()
        need(sha(raw)==item['parent_sha256'],'frozen parent source identity')
        transformed=raw.decode()
        for before,after in item['exact_replacements']:
            need(before!=after and transformed.count(before)==1,'unique nonempty exact patch')
            transformed=transformed.replace(before,after)
        candidate=(HERE/'source'/name).read_bytes()
        need(transformed.encode()==candidate and sha(candidate)==item['candidate_sha256'],'complete source patch identity')
        if item['exact_replacements']:changed.append(name)
    need(set(changed)=={'build_equation.py','check_equation.py','audit_power_graph.py'},'only power allocation and matching auditors change')
    text=(HERE/'source/build_equation.py').read_text()
    need(text.count('W = self.add(n, k)')==1,'fixed common bound')
    for old in ['"W", "A", "T", "Z", "X", "Y"','slack.wn','slack.wk','.base_bound','.exponent_bound','.A_at_least_two','slack.a2','.B_at_least_two','slack.b2']:
        need(old not in text,'deleted common-bound coordinates and rows')
    for name,item in pins['copied_files'].items():
        need((HERE/name).read_bytes()==(ROOT/item['source']).read_bytes() and sha((HERE/name).read_bytes())==item['sha256'],'frozen ordinary proof/auditor copy')
    # Authenticate the mathematical sources as text only. No Lean is executed.
    repo=ROOT.parents[1]
    proof_sources={
        '.lake/packages/mathlib/Mathlib/NumberTheory/PellMatiyasevic.lean':'a8ea2ddf5167a9163f3af19309eed96213848b632b58f8e5857535b3a1412341',
        'Computability/DiophantineConsistency/Lean/DiophantineConsistency/PowerRepresentation.lean':'6d8f1dce54132c6824e25d195bb888baf71553e4985183b806ef03e95d2a90b4',
        'Computability/DiophantineConsistency/Lean/DiophantineConsistency/PellRepresentation.lean':'28389a7a799897bf7f2a82f2965e58b14bfc37093ef3751891462e6e72aa1bd8'}
    for name,wanted in proof_sources.items():
        need(sha((repo/name).read_bytes())==wanted,'inert mathematical source pin')
    return dict(exact_changed_files=changed,proof_sources=proof_sources)


def equation_check(name):
    folder=HERE/name;eq=json.loads((folder/'equation.json').read_text())
    expanded=json.loads((folder/'expanded_polynomial.json').read_text())
    n=len(eq['variables']);squares=defaultdict(int);used=set()
    for row in eq['residuals']:
        need(len(set(tuple(m)for c,m in row['terms']))==len(row['terms']),'row monomials distinct')
        for c,m in row['terms']:
            need(type(c)is int and c and len(m)<=2 and m==sorted(m)and all(type(i)is int and 0<=i<n for i in m),'literal quadratic residual')
            used.update(m)
        for a,ma in row['terms']:
            for b,mb in row['terms']:squares[tuple(sorted(ma+mb))]+=a*b
    actual={tuple(m):c for c,m in expanded['terms']}
    need(len(actual)==len(expanded['terms'])and actual=={m:c for m,c in squares.items()if c},'complete exact quartic expansion')
    need(used==set(range(n))and max(map(len,actual))==4,'all variables live and exact degree four')
    metrics=eq['metrics']
    need(metrics['variables']==n and metrics['expanded_monomials']==len(actual)and metrics['max_abs_expanded_coefficient']==max(map(abs,actual.values())),'actual counts and height')
    return dict(metrics=metrics,equation_sha256=sha((folder/'equation.json').read_bytes()),expanded_sha256=sha((folder/'expanded_polynomial.json').read_bytes()))


def run_audits():
    flags=['-O']if sys.flags.optimize else[]
    results={}
    with tempfile.TemporaryDirectory(prefix='proveit-fixed-power-audits-')as tmp:
        for variant in ['affine','retained']:
            output=Path(tmp)/(variant+'.json')
            cmd=[sys.executable,'-B',*flags,str(HERE/'source/check_equation.py'),'--directory',str(HERE/'source'),'--equation-directory',str(HERE/variant),'--output',str(output)]
            p=subprocess.run(cmd,capture_output=True,text=True)
            need(p.returncode==0,'arithmetic/positivity/affine audit: '+p.stderr)
            results[variant]=json.loads(output.read_text())
        output=Path(tmp)/'power.json'
        p=subprocess.run([sys.executable,'-B',*flags,str(HERE/'source/audit_power_graph.py'),'--output',str(output)],capture_output=True,text=True)
        need(p.returncode==0,'exact local power polynomial audit: '+p.stderr)
        results['power']=json.loads(output.read_text())
        need(results['power']['exact_polynomial_constraints']==13 and results['power']['positive_certificate_witnesses']==22,'new exact local dimensions')
        output=Path(tmp)/'majorant.json'
        p=subprocess.run([sys.executable,'-B',*flags,str(HERE/'majorant_audit.py'),'--output',str(output)],capture_output=True,text=True)
        need(p.returncode==0,'exact literal beta-majorant and endpoint audit: '+p.stderr)
        results['majorant']=json.loads(output.read_text())
    return results


def count_call_pairs():
    # Instrument source construction only: no numerical power witness search.
    program=r'''
import importlib.util,json,sys
from collections import Counter
from pathlib import Path
p=Path(sys.argv[1]);sys.path.insert(0,str(p))
s=importlib.util.spec_from_file_location('fixedw',p/'build_equation.py')
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
original=m.Builder.power
calls=[]
def counted(self,n,k):
 calls.append((n,k));return original(self,n,k)
m.Builder.power=counted
b=m.construct(json.loads((p/'wire_eliminated_source.json').read_text()),'mixed13',positive_powers=True)
c=Counter(calls)
print(json.dumps(dict(requests=len(calls),distinct_pairs=len(c),instantiated_graphs=len(b.powers),duplicate_requests=sum(v-1 for v in c.values()))))
'''
    p=subprocess.run([sys.executable,'-B','-c',program,str(HERE/'source')],capture_output=True,text=True)
    need(p.returncode==0,'power call-pair measurement')
    result=json.loads(p.stdout)
    need(result==dict(requests=55,distinct_pairs=55,instantiated_graphs=55,duplicate_requests=0),'all actual memoized call pairs distinct')
    return result


def main():
    result=dict(status='PASS',python_optimization=sys.flags.optimize,source=source_check(),
        arbitrary_common_bound_controls=arbitrary_bound_controls(),derived_lower_bound_controls=derived_lower_bound_controls(),power_call_pair_measurement=count_call_pairs(),
        variants={v:equation_check(v)for v in ['affine','retained']},audits=run_audits(),
        scope='Exact source transformation/full quartic expansion and finite arithmetic controls. Unbounded ordinary proof in PROOF.md; no Lean or internal-ZFC derivation.')
    (HERE/('CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json')).write_text(json.dumps(result,indent=2)+'\n')
    print('PASS reduced-slack whole quartics, 22-witness/13-constraint identity, arbitrary-bound controls and 55 distinct call pairs')


if __name__=='__main__':main()
