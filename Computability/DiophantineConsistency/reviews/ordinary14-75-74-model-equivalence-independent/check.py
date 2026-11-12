#!/usr/bin/env python3
"""Independent model-wrapper interface and finite-coordinate audit; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-75-74-model-equivalence-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={'README.md':'5bf6cc3102f4eace35e3d90bd6f5290256adae671b58e9a1ac4f814e0e320fd9','ModelEquivalence75To74.lean':'d0b87479f1370ee5c1d9510a94258fabd333f8b64d01e479aa66230a1c3c42ac','check_source.py':'c57bab67409c49ec02d93ba786a5a7235b4325b12ec113c1072518c347b09bc7','observation.json':'8bd44cd75e52ee3d94c1384ce9da30c200ad59259fd3a11237e39e4e58dc1e0c'}
tail=b"\nIndependent source review: [75/74 model wrapper](../../reviews/ordinary14-75-74-model-equivalence-independent/README.md).\n"
final=(A/'README.md').read_bytes()
assert hashlib.sha256(final).hexdigest()=='ec6808119b2a7a279ec67d8e6e5728a743f79c830a9224321cf0a25368af31b7'
assert final.endswith(tail) and hashlib.sha256(final[:-len(tail)]).hexdigest()==pins['README.md']
for n,h in pins.items():
 if n!='README.md':assert sha(A/n)==h,n
src=(A/'ModelEquivalence75To74.lean').read_text(); guard=D/'research/ordinary14-74-ownzero-guard-strict-draft/OwnZeroGuardStrict74.lean';maps=D/'research/ordinary14-75-74-positive-map-draft/Positive75To74.lean';p72=D/'Lean/DiophantineConsistency/Compact44/P72Root.lean'
for f,h in [(guard,'d8d99e58177cdc6fde4fad5f79b577ce97023162656931691ce314141f98e1b8'),(maps,'c8e10e66643f025988751af1a55b7d70dc23ea25eec70b6efe4dc256003b7d70'),(p72,'066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091')]:assert sha(f)==h
assert not re.search(r'\b(?:sorry|admit|axiom)\b',src)
for t in ['(hd : Discrete (DiffRing V)) (hb : 0<beta)','(hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)', 'Positive75To74Draft.forward_map p v hv hz','OwnZeroGuardStrict74Draft.strict_of_zero p beta K v hd hbeta hK hb hv hz','Positive75To74Draft.reverse_map p v hv hstrict hz','(p 0 : V) (p 1 : V) hd hb','P72Root.cast_port p 0','P72Root.cast_port p 1']:
 assert t in src,t
t=guard.read_text()
for item in ['theorem strict_of_zero','(hd : Discrete (DiffRing V))','(hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)','(hb : 0<beta) (hv : ∀ j, 0<v j)','(hz : InternalZero (P74PositiveGuard.graph p).output v) : 1<v 13','(ι_nonneg K)']:
 assert item in t,item
r=p72.read_text();assert re.search(r'theorem cast_port \(p : Fin 4 → ℕ\) \(j : Fin 4\)\s*:\s*\(\(\(fun j => \(p j : ℤ\)\) j : ℤ\) : DiffRing V\) = ι \(p j : V\)',r)
# Verify strict direction is sourced from the 74 zero and the forward from 75.
forward,reverse=src.split('constructor',1)[1].split('/-- Natural-port',1)[0].split('  · ',2)[1:]
assert 'forward_map p v hv hz' in forward and 'strict_of_zero p beta K v hd hbeta hK hb hv hz' in reverse and 'reverse_map p v hv hstrict hz' in reverse
# A sampled model of natural coordinates checks the exact witness slots/inverses only.
controls=0
for x in range(1,41):
 v=list(range(1,15));v[13]=x;w=v.copy();w[13]=x+1
 assert all(j>0 for j in w) and w[:13]==v[:13]
 assert w[13]>1 and w[13]-1==v[13];controls+=1
review=D/'reviews/ordinary14-75-74-positive-map-independent'
assert sha(review/'check.py')=='fb19014b6250056bd240c68820ce288d80d343d1a3ceafe067d54b259d1b970f'
assert sha(review/'observation.json')=='b7976ca69463a820f0b2c6c77f52e0610ac1fdaa69b24883d65e6f0d797dc987'
assert subprocess.run([sys.executable,'-I','-S','-B',str(review/'check.py')],cwd=D,check=True,capture_output=True).stdout==(review/'observation.json').read_bytes()
assert subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,check=True,capture_output=True).stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'source/interface review and finite coordinate controls; no Lean or endpoint theorem','author_pins':pins,'strict_source_sha256':sha(guard),'map_source_sha256':sha(maps),'cast_port_source_sha256':sha(p72),'coordinate_controls':controls,'positive_map_review_replayed':True,'author_receipt_reproduced':True},sort_keys=True,indent=2))
