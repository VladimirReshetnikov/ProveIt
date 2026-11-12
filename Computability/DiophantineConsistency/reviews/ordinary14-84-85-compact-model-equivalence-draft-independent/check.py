#!/usr/bin/env python3
"""Independent symbolic-port composition review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-85-compact-model-equivalence-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'CompactEquivalence.lean','b7a3e58448aaf8683dd7d2438dc2d4673a24f4e3f6ec32749fcc2d2cbd3974ae').decode()
pin(A/'check_source.py','5216f29259023db23d6a09d45880a83abdce60a8d8c85572a102e44c629ec70e')
receipt=pin(A/'observation.json','7e22db813b9fa8e507d81f0f6156810f91b57be4788f8801d50def64a6d147a5')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-85-compact-model-equivalence-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='61d55842df051cc4b58a97757b886b91363fe1cd333e727ccf6f305cf6c9a0e0'
for path,h in {
 'research/ordinary14-84-85-model-equivalence-draft/ModelEquivalence.lean':'4a0bb28f91614ee0a30046e8072fa246f2f55117a059c7a56becae95cedeedcc',
 'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean':'0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414',
 'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean':'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea',
 'Lean/DiophantineConsistency/Compact44/C44Short15Facts.lean':'f4076a72a8a236572185e774a1d042e4ea60c51fefbccdcedf4aae10d076dec6',
 'Lean/DiophantineConsistency/Compact44/P72Root.lean':'066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091',
}.items():pin(D/path,h)
ports=(D/'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean').read_text()
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports
for f in ('ports CompactFixedBeta.betaNat K lowNat highNat',
 'let t : V := (67:V)*8807','C44Short15Facts.port_bounds (V:=V) CompactFixedBeta.betaNat K lowNat highNat',
 'have hradix : (p 0 : V)=Exp.exp t-1',
 'rw [←hid,add_tsub_cancel_right]',
 'P72Root.cast_port p 0','P72Root.cast_port p 1','P72Root.cast_port p 2','P72Root.cast_port p 3',
 '(p 0 : V) (p 1 : V) (p 2 : V) (p 3 : V) t hb.1 hb.2.2.2 ht hradix',
 'hp0 hp1 hp2 hp3 hb.2.1 hb.2.2.1'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=240)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-84-85-model-equivalence-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
cases=0
for exponent in range(4,11):
 beta=2**exponent-1
 for K in (0,1,9):
  for low in (0,beta-1):
   for high in (0,beta-1):
    ports=[beta,K,low,beta+high]
    assert ports[0]>0 and ports[2]<ports[0] and ports[3]<2*ports[0]
    assert ports[0]+1==2**exponent and ports[3]==beta+high
    cases+=1
assert 67*8807==590069
print(json.dumps({'scope':'source interface and finite port controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'toy_port_cases':cases,
 'symbolic_beta_exponent':590069},sort_keys=True,indent=2))
