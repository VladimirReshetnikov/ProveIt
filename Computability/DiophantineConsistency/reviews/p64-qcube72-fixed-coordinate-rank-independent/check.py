#!/usr/bin/env python3
"""Independent finite controls and pinned scope review; no Lean."""
import hashlib,json,math,random,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def need(b,s):
    if not b:raise RuntimeError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=Path(__file__).resolve().parents[2];d=base/'research'/'p64-qcube72-fixed-coordinate-rank-obstruction';g=base/'research'/'p64-qcube72-free-main-candidate'/'graph.json'
pins={d/'README.md':'50a66967409801616c7226ea6e9e2b19f934e1083d134f96516b994964d6cdc9',
 d/'check.py':'5c06c12346ddaa6a8f3d57e698c6df84ba0758431dce502a3d49894d603f9536',
 d/'result.json':'f48cc013d8a9383a4a9391e80b213c3e75f0d7d4399fd7a0cf842c7a049809dc',
 g:'875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806',
 base/'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean':'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea',
 base/'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean':'0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414'}
for p,h in pins.items():need(sha(p)==h,'pin drift '+str(p))
r=subprocess.run([sys.executable,'-I','-S','-B',str(d/'check.py')],capture_output=True,check=True,timeout=20)
need(r.stdout==(d/'result.json').read_bytes() and not r.stderr,'author controls reproduction')
rows=json.loads(g.read_bytes())['source'];tab={r[0]:r for r in rows}
for n,row in {'Y':['Y','*','q3','s'],'U':['U','*','Y','Y'],'H':['H','+','four_a',3],
              'Dstar':['Dstar','+','U_b0','H_main_gap'],'H_main_gap':['H_main_gap','*','H','h'],
              'R':['R','+','R_product','mask']}.items():need(tab[n]==row,'graph gate '+n)
# Independent finite instances of gcd cancellation and rank reduction.
cases=0
for q in range(2,100):
 for s in range(1,5):
  Y=q**3*s
  for X in range(1,6):
   H=4*Y*(X+1)+3; delta=math.gcd(q**6,H)
   need(delta==(3 if q%3==0 else 1),'gcd formula')
   need((q**6//delta)%q==0,'cancelled factor not multiple q')
   cases+=1
rng=random.Random(729041)
for _ in range(3000):
 q=rng.randrange(3,500); F=rng.randrange(1,q-1); alpha=rng.randrange(1,q-F);J=rng.randrange(1,15);MC=rng.randrange(0,50);MF=rng.randrange(0,50)
 C=q-F-alpha;R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
 need((R-C-MC*J)%q==0,'rank residue')
# Transport-only negative control: same C, different w, F and alpha.
q=5;K=1;C=1
old=(1,3,4,1);new=(2,2,5,1)
for F,alpha,w,z in (old,new):
 need(q-F-alpha==C and (K+w)*C==F+z*(q-1),'transport example')
need((old[0]-new[0])%(q-1)!=0,'missing-w negative control')
# Particular reviewed symbolic full-zero residues.
q=3;J=1;h=486%q;k=428%q;MC=(184-40+115)%q
need((h+k-1-MC*J)%q==0,'example not excluded')
result={'status':'PASS_FIXED_COORDINATE_RANK_REVIEW','script_sha256':sha(__file__),
        'author_readme_sha256':pins[d/'README.md'],'graph_sha256':pins[g],
        'gcd_controls':cases,'rank_controls':3000,'same_C_changed_w_transport_negative_control':True,
        'symbolic_zero_required_C_residue':0,
        'scope':'Standard-integer fixed-J/k/h necessary condition; no Lean theorem, unrestricted old-graph nonexistence or compact44 existence claim.'}
print(json.dumps(result,indent=2,sort_keys=True))
