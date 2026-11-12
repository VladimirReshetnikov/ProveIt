#!/usr/bin/env python3
"""Independent pointwise source-wrapper and dependency replay; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-78-75-model-equivalence-draft';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={'README.md':'82ab7ba1565b28b752759ecbf492bd6fef9d85bac6b5c1d8852c657cfbb9f195','ModelEquivalence78To75.lean':'482a6102d4e339d3997a5208fc7ee1becacc5beecaf05f4f06e4a11b5b683f6c','check_source.py':'29e38662c3aeef417e68f7935e7496aca430d41e787bbcf7fbef76e20ee81bfc','observation.json':'b45fcc8e4df185fbb54a18dcd39b7ff7ee9066e23144d60d4c4a73eb5e44b8d9'}
tail=b"\nIndependent source review: [75/78 pointwise wrapper](../../reviews/ordinary14-78-75-model-equivalence-independent/README.md).\n"
final=(A/'README.md').read_bytes()
assert hashlib.sha256(final).hexdigest()=='297313c754810712f630c1155a55a7e460340a0c3ca3347541a1792a07f7df5a'
assert final.endswith(tail) and hashlib.sha256(final[:-len(tail)]).hexdigest()==pins['README.md']
for n,h in pins.items():
 if n!='README.md':assert sha(A/n)==h,n
s=(A/'ModelEquivalence78To75.lean').read_text();left=D/'research/ordinary14-75-to-78-model-map-draft/Model75To78.lean';right=D/'research/ordinary14-78-to-75-model-map-draft/Model78To75.lean';cast=D/'Lean/DiophantineConsistency/Compact44/P72Root.lean'
for p,h in [(left,'c4315f65bed66e551c791ac11f706d3156d23b21b8256aa4b8c52384ed13ace8'),(right,'9df593d1484be12f05e8cb4115ea5b8f0f233817b205a0bca39066014a3d60ec'),(cast,'066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091')]:assert sha(p)==h
assert not re.search(r'\b(?:sorry|admit|axiom)\b',s)
for t in ['(hbeta : (p 0 : DiffRing V)=ι beta) (hb : 0<beta) (hv : ∀ j, 0<v j)','Model75To78Draft.zero_78_of_75_zero p beta v hbeta hb hv','Model78To75Draft.zero_of_78_zero p v','P72Root.cast_port p 0','zero_iff (fun j => (p j : ℤ)) (p 0 : V) v hbeta hb hv']:
 assert t in s,t
for source,marker,start,end in [(left,'theorem zero_78_of_75_zero','P75NegativePell','P78AuxRoot'),(right,'theorem zero_of_78_zero','P78AuxRoot','P75NegativePell')]:
 body=source.read_text().split(marker,1)[1].split(':= by',1)[0]
 assert body.index(start)<body.index(end) and body.count('.output v')==2
assert re.search(r'theorem cast_port \(p : Fin 4 → ℕ\) \(j : Fin 4\)\s*:\s*\(\(\(fun j => \(p j : ℤ\)\) j : ℤ\) : DiffRing V\) = ι \(p j : V\)',cast.read_text())
reviews=[('ordinary14-75-to-78-model-map-independent','0f7a173feeb3c2b673a613a7955d86adc9dc2f7f487996755506c3103e37dcaf','19dba6b87f97c108b41b5def418f3dc183fcf88e4fe26144e45d330919b6971e'),('ordinary14-78-to-75-model-map-independent','f263c11fdf40711f413727b03e586a033d00d9735c49b27e1d830d023e43aeeb','c1fcaf340d50647e622e4a5585026226f2754a09fbfad9006a0768e98439782d')]
for n,h1,h2 in reviews:
 q=D/'reviews'/n
 assert sha(q/'check.py')==h1 and sha(q/'observation.json')==h2
 assert subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],cwd=D,check=True,capture_output=True).stdout==(q/'observation.json').read_bytes()
assert subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,check=True,capture_output=True).stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'source-interface and prior source-review replay; no Lean, provider or endpoint','author_pins':pins,'map_source_sha256':[sha(left),sha(right)],'cast_port_sha256':sha(cast),'independent_map_reviews_replayed':[x[0] for x in reviews],'author_receipt_reproduced':True},sort_keys=True,indent=2))
