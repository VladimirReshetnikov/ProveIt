#!/usr/bin/env python3
"""Independent guard map source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-88-to-87-positive-map-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(A/'README.md','ae096cc3cfca6bcc98454b2bf640deadb16b854eb3c7f9e1c1b46bd1bc4f0ec7')
s=pin(A/'PositiveMap88To87.lean','69dcc61739d475807d64a78f09bc3f186caa3aa7456be6c1d969b3ea49e52542').decode()
pin(A/'check_source.py','2d7e171b79c5951b763e5f52845772c973b9f4424843ff4667a721f20a664318')
receipt=pin(A/'observation.json','35e2713fe7ed308b33b5fa2b77a00ba168b407c409fc79d8a70c01eb7c75d298')
for f in ['Function.update v 13 (v 13+v 1)', 'add_pos (hv 13) (hv 1)', 'Ring88To87Draft.output_eval p (fun j => ι (v j))', 'rw [←cast_forward v] at h', 'rw [h]']:assert f in s,f
n=0
for t in range(1,40):
 for F in range(1,40):
  omega=t+F;assert omega>0 and omega>F;n+=1

def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
p=D/'reviews'/'ordinary14-88-87-ring-client-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'guard map source review; no Lean or unconditional reverse','finite_controls':n},sort_keys=True,indent=2))
