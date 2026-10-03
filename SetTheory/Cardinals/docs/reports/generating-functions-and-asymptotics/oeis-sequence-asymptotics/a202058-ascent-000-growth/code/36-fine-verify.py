#!/usr/bin/env python3
"""Replay the supplied checks; --full regenerates all 400 exact and 1000 floating terms."""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, sys, time
import mpmath as mp
P=Path(__file__).resolve().parent
S=P/'support'/'fine-research'
B=P/'.build'/'verification'; B.mkdir(parents=True,exist_ok=True)
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--full',action='store_true')
args=parser.parse_args()
mp.mp.dps=70

def command(cmd, name, cwd=P):
    t=time.monotonic()
    with (B/(name+'.log')).open('w') as out:
        subprocess.run(cmd,cwd=cwd,stdout=out,stderr=subprocess.STDOUT,check=True)
    return round(time.monotonic()-t,3)

def counts(path):
    return {int(a):int(b) for line in path.read_text().splitlines()
            if line.strip() and not line.lstrip().startswith('#')
            for a,b in [line.split()]}

result={'mode':'full' if args.full else 'quick','limitations':['Finite checks corroborate but do not replace the mathematical proof.','Long-double continuation is numerical and not interval-certified.']}
exact=counts(S/'numerics'/'exact-counts-400.txt')
source=counts(S/'numerics'/'oeis-b202058.txt')
assert len(exact)==401 and set(exact)==set(range(401))
assert len(source)==177 and set(source)==set(range(177))
assert all(exact[n]==a for n,a in source.items())
assert exact[0]==exact[1]==1
assert 2*exact[1]**2==exact[0]*exact[2]
assert all((n+1)*exact[n]**2>n*exact[n-1]*exact[n+1] for n in range(2,400))
result['stored_exact_data']={'published_terms_matched':177,'exact_terms':401,'strict_normalized_logconcavity_centers':[2,399]}

checks=[('kernel/verify_padded_barrier.py','residual'),('kernel/verify_continuum_average.py','continuum-average'),('numerics/check_generic_logconcavity.py','suffix-logconcavity'),('literature-checks/check_small_polynomials.py','small-polynomials')]
result['check_seconds']={}
for rel,name in checks:
    result['check_seconds'][name]=command([sys.executable,str(S/rel)],name)
result['check_seconds']['independent-audit']=command([sys.executable,str(P/'audits'/'verify_fine_independently.py')],'independent-audit')
result['residual']=json.loads((S/'kernel'/'verification.json').read_text())
assert result['residual']['all_assertions_passed']
generic=json.loads((S/'numerics'/'generic-logconcavity.json').read_text())
assert generic['failures']==[] and generic['logconcavity_tests']==3060
result['generic_logconcavity']=generic

for script in ['verify_radius.py','verify_root_limit.py']:
    result['check_seconds'][script]=command([sys.executable,script],script[:-3],P/'dependencies'/'frozen-foundation')
prov=json.loads((S/'source-provenance.json').read_text())
foundation=P/'dependencies'/'frozen-foundation'/'a202058-report.tex'
assert hashlib.sha256(foundation.read_bytes()).hexdigest()==prov['frozen_tex_sha256']
result['frozen_foundation_tex_sha256']=prov['frozen_tex_sha256']

cpp=S/'numerics'
result['check_seconds']['compile-exact']=command(['g++','-O3','-std=c++17',str(cpp/'exact_counts.cpp'),'-lgmpxx','-lgmp','-o',str(B/'exact_counts')],'compile-exact')
n=400 if args.full else 176
result['check_seconds']['exact-replay']=command([str(B/'exact_counts'),str(n),str(B/'exact-counts.txt')],'exact-replay')
replay=counts(B/'exact-counts.txt')
assert replay=={k:v for k,v in exact.items() if k<=n}
result['exact_recomputed_through']=n

result['check_seconds']['compile-floating']=command(['g++','-O3','-std=c++17',str(cpp/'floating_counts.cpp'),'-o',str(B/'floating_counts')],'compile-floating')
nf=1000 if args.full else 176
result['check_seconds']['floating-replay']=command([str(B/'floating_counts'),str(nf),str(B/'floating-counts.txt')],'floating-replay')
def floats(path):
    return {int(a):mp.mpf(b) for line in path.read_text().splitlines()
            if line.strip() for a,b in [line.split()]}
stored=floats(cpp/'floating-counts-1000.txt'); fresh=floats(B/'floating-counts.txt')
assert set(fresh)==set(range(nf+1))
max_saved=max(abs(fresh[k]/stored[k]-1) for k in fresh)
mu=mp.mpf(8)/(3*mp.pi**2)
max_exact=max(abs(fresh[k]/(mp.mpf(exact[k])/mp.factorial(k)/mu**k)-1) for k in fresh if k<=400)
# A platform-dependent long double format may change rounding; this tolerance is a
# replay diagnostic only and is not a rigorous error bound on uncomputed terms.
assert max_saved<mp.mpf('2e-12') and max_exact<mp.mpf('2e-12')
result['floating_recomputed_through']=nf
result['floating_max_relative_difference_saved']=mp.nstr(max_saved,20)
result['floating_max_relative_difference_exact_overlap']=mp.nstr(max_exact,20)
result['all_checks_passed']=True
(B/'replay-summary.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
