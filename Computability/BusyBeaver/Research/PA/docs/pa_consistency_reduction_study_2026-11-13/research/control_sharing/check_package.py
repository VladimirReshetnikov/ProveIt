#!/usr/bin/env python3
"""Quick integrity and exact-input reconstruction; no long search is rerun."""
from pathlib import Path
import hashlib,json,sys
if not __debug__:
    raise SystemExit('Assertions are required; do not use -O or PYTHONOPTIMIZE.')
HERE=Path(__file__).resolve().parent
manifest=HERE/'SHA256SUMS'
checked=0
for line in manifest.read_text().splitlines():
    want,name=line.split('  ',1)
    assert hashlib.sha256((HERE/name).read_bytes()).hexdigest()==want,name
    checked+=1
labels=json.loads((HERE/'inputs/n6_original/pa194n6.labels.json').read_text())
dense=(HERE/'inputs/n6_original/pa194n6.tm').read_text()
native=[]
for line in dense.splitlines():
    q,b,w,d,n=line.split()
    native.append((labels[int(q)],int(b),int(w),d,labels[int(n)]))
reconstructed=''.join(f'{q} {b} {w} {d} {n}\n' for q,b,w,d,n in sorted(native)).encode()
assert reconstructed==(HERE/'inputs/n6.native.tm').read_bytes()
assert hashlib.sha256(reconstructed).hexdigest()=='63b6f604ee34ee119eb92ce3125021257204142854dec416c6b955f0560b975a'
old=reconstructed.decode().splitlines()
new=(HERE/'inputs/n6_append0.native.tm').read_text().splitlines()
assert len(old)==len(new)==388
assert [(a,b) for a,b in zip(old,new) if a!=b]==[('198 0 1 L 40','198 0 0 L 40')]
contexts=(HERE/'inputs/abstract_k5.txt').read_bytes()
assert len(contexts.splitlines())==29262
assert hashlib.sha256(contexts).hexdigest()=='73bd8c565c603c771a0862e529e1ad91bd98a606e8da7081708da55c01eb27fa'
sys.path.insert(0,str(HERE/'sources/base'))
import compiler as c,symbolic_runtime as s
c.ROOT=s.ROOT=HERE/'inputs/pa196'
inc=('leaf','inc',1)
c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
g=c.read_grammar(HERE/'inputs/primary/source/pa194.grammar.json')
rows,index,shape=c.build(g)
raw=''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n' for (q,b),(w,d,n) in sorted(rows.items())).encode()
assert len(rows)==402 and len(shape)==67
assert hashlib.sha256(raw).hexdigest()=='b25933d14de19f72709bdecf7a67a4e21c150f525cf61ec76c074ac577d6cc87'
print(json.dumps({'status':'PASS','manifest_files':checked,'n6_native_reconstruction':True,
                  'n6_contexts':29262,'primary_raw_states':len(rows)//2,
                  'primary_readers':len(shape),'scope':'Integrity and exact inputs only; no search-completeness or consistency theorem.'},indent=2))
