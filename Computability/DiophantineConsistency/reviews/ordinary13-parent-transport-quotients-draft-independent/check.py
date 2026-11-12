#!/usr/bin/env python3
"""Independent 13-parent transport quotient source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary13-parent-transport-quotients-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'ParentTransportQuotients.lean','fe76f0612146c662dced8adcba7b561dc3262019e58d6a86edd48a5b9e1b1d81').decode()
pin(A/'check_source.py','94fd33e64386944929055968606280c19cba68a8daff0258176eb63f66e52a87')
receipt=pin(A/'observation.json','cd67537cfd77a4b9756f3011a20e89df5ea0116668e62aebc640ea46837e155e')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary13-parent-transport-quotients-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='2bc5c04f05363e6e0b0f26eb641e76c1db2f23d93e475209a3177bd92e0dc552'
p=D/'reviews/ordinary13-parent-scaled-norms-draft-independent'
pin(p/'check.py','fed9b27d3fb4c4e60ad63f4a0c898a5487484de5d32531129276514e1edfef7e')
pin(p/'result.json','ef10028ca9a897ad2e68f84ab7608f4b107fa266bf22ab492b2abb6dbad86ec4')
dep=pin(D/'Lean/DiophantineConsistency/ArithmeticAdaptiveTransportQuotient2011.lean','12391247b1daad21ede3ff0ec3bd0d19e443a2042e8ad3509f91a4ff08a62ab8').decode()
assert '∃ w : V, 0<w ∧ q*A=(v 1+v 2)*A+v 1*q+b*w' in dep
for f in ('(hb : 0<(p 0:V)) (hv : ∀ j, 0<v j)',
 '(hz : InternalZero (P88FourSquare.graph (fun j => (p j : ℤ))).output v)',
 'ParentScaledNormsDraft.scaled_norms p v hz',
 'quotients_of_scaled_norms p v hp.2.1 hp.2.2.1 hn',
 'quotients_force_transport p v hb hv hq',
 'quotient_transport p v hp.2.1 hpos tau hfirst',
 'positive_Y_quotient_of_facts p v hp.2.1 (hv 7) hq'):
 assert f in s,f
n=0
for b in range(1,10):
 q=b+1
 for F in range(1,q):
  for alpha in range(1,q-F):
   for X in range(1,10):
    for K in range(4):
     A0=X+K*q;Bp=q*A0;Bn=(F+alpha)*A0+F*q;bt=Bp-Bn
     if bt>0 and bt%b==0:
      t=bt//b;assert t>0 and Bp==Bn+b*t;n+=1
assert n>0
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'13-parent transport quotient source review; no Lean','finite_transport_cases':n,'prior_scaled_norm_review':'pinned, not rerun'},sort_keys=True,indent=2))
