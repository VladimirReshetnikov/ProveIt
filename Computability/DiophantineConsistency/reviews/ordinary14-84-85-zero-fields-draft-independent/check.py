#!/usr/bin/env python3
"""Independent zero-field source/finite review; no Lean invocation."""
import hashlib,itertools,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2]; A=D/'research/ordinary14-84-85-zero-fields-draft'
def sha(d): return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes(); assert sha(d)==h,str(p); return d
source=pin(A/'ZeroFields.lean','75bb11893469673856b6fe02eba6f17317dfa8b4b65d35272577c42cf47b9c1e').decode()
pin(A/'check_source.py','51d72734169694a3a0ef9d3e61f221570d7c11c7d932beabba452f2e8188d7cf')
receipt=pin(A/'observation.json','de704fefeeb3771d1566922d9df1cf5ba3f151e7c4ce6ad0e427bda0fd632afb')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-85-zero-fields-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='e42659387efe177fc110e930d952ea3eeaa1c074a2682cb61425f056b9017a2d'
for path,h in {
 'research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean':'92ace01321c77730c81eba032d1fdd86778e53399a073258cdbd49f7a621718f',
 'research/ordinary14-qcube84-lean-draft/P84QcubeGraph.lean':'552fa737fa0c36a58220053be90c4cdb35785d1fae53bc1c30bc15f8404104e9',
 'research/ordinary14-qcube85-lean-draft/P85QcubeGraph.lean':'46c5ffa3344d70b22ca9bc3c56a7b0ba37ac6603a3f7b38f202f5d84fc44ef9b',
 'Lean/DiophantineConsistency/ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998',
}.items(): pin(D/path,h)
for n in ('84','85'):
 graph='P'+n+'QcubeGraph'; block=source.split('theorem fields'+n,1)[1].split('\n\n',1)[0]
 assert f'(hz : InternalZero ({graph}.graph p).output v)' in block
 for field in ('A0','A1','aux','gap','guardResidual'):
  suffix=' v-1=0' if field=='aux' else ' v=0'
  assert f'eval ({graph}.graph p).{field}'+suffix in block
 assert f'rw [internalZero_iff,{graph}.output_shape] at hz' in block
 assert f'(eval ({graph}.graph p).aux v-1)' in block
 assert '(fiveSquares_eq_zero_iff _ _ _ _ _).mp hfive' in block
run=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
assert not run.stderr and run.stdout==receipt
cases=0
for a,b,aux,g,h in itertools.product(range(-2,3),repeat=5):
 zero=(a*a+b*b+(aux-1)**2+g*g+h*h)==0
 assert zero == (a==0 and b==0 and aux==1 and g==0 and h==0)
 cases+=1
print(json.dumps({'scope':'source and finite controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'shifted_aux_tuples':cases},sort_keys=True,indent=2))
