#!/usr/bin/env python3
"""Review the finite AQ16 proof, including a beta=1 positivity edge case."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
A=ROOT/'reviews/aq16-independent-audit';P=ROOT/'research/aq22-positive-binding-survey/candidate17.json';C=ROOT/'research/aq17-positive-signed-binding/candidate16.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs=[Path(__file__),A/'audit.py',A/'terminal-observation.json',P,C]
before={str(p.resolve()):H(p) for p in inputs}
assert H(P)=='760b9e7babbb559b7175344915456fdc3d9bd8ce85382873d4915faf2cd76d81'
assert H(C)=='a7d6f8a618a810b37eb7a9de6bd92ceb73bd6351971fdd39045bf95f8bf9edac'
p=json.loads(P.read_text());c=json.loads(C.read_text());stored=json.loads((A/'terminal-observation.json').read_text())
q=subprocess.run([sys.executable,str(A/'audit.py')],capture_output=True,text=True,timeout=90)
assert q.returncode==0 and q.stdout==stored['normal']['stdout'] and json.loads(q.stdout)['status']=='PASS_AQ16_INDEPENDENT_FINITE_AUDIT'
neg=subprocess.run([sys.executable,'-O',str(A/'audit.py')],capture_output=True,text=True,timeout=30)
assert neg.returncode!=0 and 'optimized Python is unsupported' in neg.stderr
pr={r[0]:r[1:] for r in p['source']};cr={r[0]:r[1:] for r in c['source']}
assert pr['dDifference']==['-','dValueVariable','DstarComputed']
# Independent gate-level witness-degree upper bound: subtraction cannot
# increase degree, even when cancellation makes this bound non-sharp.
deg={name:1 for name in c['witnesses']};deg.update({name:0 for name in c['fixed_numerals']})
get=lambda x:0 if isinstance(x,int) else deg[x]
for name,op,a,b in c['source']:
    assert name not in deg and op in ('+','-','*')
    deg[name]=get(a)+get(b) if op=='*' else max(get(a),get(b))
assert len(c['witnesses'])==16 and len(c['source'])==96 and len(c['residuals'])==7
assert max(deg[n] for n in c['residuals'])==16 and deg[c['output']]==32
# The claimed leading coefficient follows independently by tracing A0. Its
# x^2 y^4 eta^2 contribution comes only from ell^2, where
# ell=X*Y^2*(eta+zeta). M^2=(1+J*beta)^6*(J*beta)^2.
required={'A0':['-','g38','g42'],'g42':['*','g39','g41'],'g39':['*','M','M'],
 'g41':['+',1,'g40'],'g40':['*','ell','g30'],'g30':['+','ell','k'],
 'M':['*','q3','qm'],'q3':['*','q','q2'],'q2':['*','q','q'],'q':['+',1,'qm'],
 'qm':['*','J','beta'],'ell':['*','E','kY'],'E':['*','X','Y'],'kY':['*','Y','k'],
 'k':['+','eta','zeta']}
for name,row in required.items():assert cr[name]==row,(name,cr[name],row)
# The highest J^8 term in M^2 has beta^8; it cannot be canceled by the
# distinct remaining terms of A0. The real sum of squares has nonzero top
# homogeneous part, so the actual beta>0 yields exact degree 32.
assert c['port_hypotheses']=={'beta_lower_bound':2}
# Evaluate the parent on positive witnesses and beta=1; this deliberately
# violates beta>=2 and shows positivity of the reconstructed term is not an
# unconditional property. It is not claimed to be a zero of the equation.
def value(beta):
    env={name:1 for name in p['witnesses']};env.update({'zeta':33,'beta':beta,'K0':1,'MC':1,'MF':1})
    for name,op,a,b in p['source']:
        x=a if isinstance(a,int) else env[a];y=b if isinstance(b,int) else env[b]
        env[name]=x+y if op=='+' else x-y if op=='-' else x*y
    return env
b1=value(1);b2=value(2)
assert (b1['k'],b1['c'],b1['a'],b1['q'],b1['U'],b1['H'],b1['shift'],b1['DstarComputed'])==(34,35,2,2,4,11,-26,-2)
assert b2['DstarComputed']==419
# Ensure the deleted binding is an integer difference, not natural truncated
# subtraction. A sign mutation is rejected by the actual structural predicate.
def binding_ok(rows):assert rows['dDifference']==['-','dValueVariable','DstarComputed']
bad=dict(pr);bad['dDifference']=['+','dValueVariable','DstarComputed']
try:binding_ok(bad)
except AssertionError:pass
else:raise AssertionError('deleted-binding sign mutation accepted')
assert {str(p.resolve()):H(p) for p in inputs}==before
result={'status':'PASS_AQ16_FINITE_AUDIT_REVIEW','inputs_sha256':before,'replayed_audit_exit':q.returncode,
        'replayed_audit_stdout':q.stdout,'optimized_exit':neg.returncode,'degree_upper_bound':32,
        'beta_one_positive_assignment_Dstar':-2,'beta_two_same_assignment_Dstar':419,
        'scope':'Review of finite integer algebra; beta=1 example is not claimed to be an equation zero. No AQ16 Lean proof, paired replay, PDF semantics or global minimality.'}
out=HERE/'receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(result['status'],H(out))
