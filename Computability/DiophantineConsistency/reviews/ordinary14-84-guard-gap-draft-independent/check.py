#!/usr/bin/env python3
"""Independent guard positivity source/finite review; no Lean."""
import hashlib,itertools,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-guard-gap-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'GuardGap.lean','e87aac162031101468b263a119fc5a88073b4cbdbf2bd3fb12608b626709e9e5').decode()
pin(A/'check_source.py','1c85481bc68efac81fc05905ddb97aff3a8a83402c5e386c5827bc2dd5403c59')
receipt=pin(A/'observation.json','7df80e6e691664c98121fd28f46c347c15f3da3eeafae02e314fbf4464a28ffc')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-guard-gap-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='99ba5778b96f9cb63a7011cf1bd8eee4c2d82497b6cc4e389acd331d8ec4baea'
for path,h in {
 'ordinary14-84-85-zero-fields-draft/ZeroFields.lean':'75bb11893469673856b6fe02eba6f17317dfa8b4b65d35272577c42cf47b9c1e',
 'ordinary14-aux-graph-norm-client-draft/GraphNormClient.lean':'c3350a90b8fa909c208ad197acc7a3bbb15bd3e6d8e45ebf097645ae602ec02e',
 'ordinary14-qcube84-lean-draft/P84QcubeGraph.lean':'552fa737fa0c36a58220053be90c4cdb35785d1fae53bc1c30bc15f8404104e9',
}.items():pin(D/'research'/path,h)
pin(D/'Lean/DiophantineConsistency/ModelDifferenceRing.lean','5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998')
for f in ('(hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)',
 '(hF : 0<v 1) (hw : 0<v 6)',
 '(hz : InternalZero (P84QcubeGraph.graph p).output v)',
 '(ZeroFields8485Draft.fields84 p v hz).2.2.2.2',
 '(ι q-ι (v 1)-ι (v 2))*(ι X+ι K)-ι (v 1)-ι (v 0*beta)*ι (v 13)=0',
 'mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (le_of_lt hx)',
 'exact ι_lt_ι.mp hlt'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-84-85-zero-fields-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
zeros=0
for J,beta,F,alpha,w,K,h in itertools.product(range(4),range(5),range(1,5),range(5),range(1,5),range(4),range(4)):
 q=1+J*beta;X=q*w;gap=q-F-alpha
 if gap*(X+K)==F+J*beta*h:
  assert X>0 and X+K>0 and gap>0 and F+alpha<q
  zeros+=1
assert zeros
# If F is not positive the strict gap can fail at an actual guard zero.
q=1;F=0;alpha=1;X=1;K=0;Jbeta=0;h=0
assert (q-F-alpha)*(X+K)-F-Jbeta*h==0 and not F+alpha<q
# An unrestricted negative K invalidates the factor positivity argument.
q=2;F=1;alpha=2;X=2;K=-3;Jbeta=1;h=0
assert (q-F-alpha)*(X+K)-F-Jbeta*h==0 and not F+alpha<q
print(json.dumps({'scope':'source and finite guard controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'bounded_guard_zeros':zeros,
 'zero_F_boundary':True,'negative_K_boundary':True},sort_keys=True,indent=2))
