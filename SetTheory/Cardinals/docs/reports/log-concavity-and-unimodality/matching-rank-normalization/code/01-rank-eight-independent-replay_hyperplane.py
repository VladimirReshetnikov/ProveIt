#!/usr/bin/env python3
"""Independent injection-based replay of the nine-fifths transition table."""
from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations
from pathlib import Path
from hashlib import sha256
import json,time,sys
def coordinate_images(rows):
    return frozenset(tuple(sorted(a)) for a in permutations(range(4),len(rows))
                     if all(mask&(1<<col) for mask,col in zip(rows,a)))
def digest(path):
    return sha256(path.read_bytes()).hexdigest()
def require(ok,message):
    if not ok:raise RuntimeError(message)

HERE=Path(__file__).resolve().parent
BASE=HERE.parent/"primary"
names=('check_hyperplane_transition.py',
       'check_hyperplane_transition.json')
before={f:digest(BASE/f) for f in names}
start=time.monotonic()
images={r:{rows:coordinate_images(rows) for rows in combinations_with_replacement(range(1,16),r)}
        for r in (2,3,4)}
parts=tuple((P,tuple(i for i in range(5) if i not in P)) for P in combinations(range(5),3))
data=[]
for rows in combinations_with_replacement(range(1,16),5):
    bases=[bool(images[4][rows[:i]+rows[i+1:]]) for i in range(5)]
    witnesses=[]
    for P,K in parts:
        triples=images[3][tuple(rows[i] for i in P)]
        pairs=images[2][tuple(rows[i] for i in K)]
        normal_coordinates=set()
        for triple in triples:
            missing=next(i for i in range(4) if i not in triple)
            for pair in pairs:
                if missing in pair:
                    normal_coordinates.update(i for i in pair if i!=missing)
        witnesses.append(normal_coordinates)
    data.append((rows,bases,witnesses))
records=[]
for H in (1,3,7,15):
    support=set(i for i in range(4) if H&(1<<i))
    hist=Counter(); joint=Counter(); bad=[]; stream=sha256(); full=sha256()
    for rows,bases,witnesses in data:
        Q=sum(flag and bool(row&H) for flag,row in zip(bases,rows))
        S=sum(bool(support & possible) for possible in witnesses)
        require(5*S>=9*Q,('nine-fifths',H,rows,S,Q))
        c=S-2*Q
        if c<0:
            require((S,Q)==(9,5),('bad type',H,rows,S,Q))
            require(all(bases),('bad profile not U(4,5)',H,rows))
            bad.append(list(rows))
        hist[c]+=1; joint[S,Q]+=1
        stream.update(f'{rows}:{c}\n'.encode())
        full.update(f'{rows}:{S}:{Q}\n'.encode())
    rec={'normal_support':H,'profiles':len(data),'minimum':min(hist),'negative_count':len(bad),
         'counts':dict(sorted(hist.items())),'sha256':stream.hexdigest(),'S_Q_sha256':full.hexdigest(),
         'S_Q_histogram':[[S,Q,num] for (S,Q),num in sorted(joint.items())],
         'all_bad_profiles_U45':True,'bad_profiles':bad}
    records.append(rec)
    print(json.dumps({k:rec[k] for k in ('normal_support','profiles','minimum','negative_count','sha256')}),flush=True)
reference=json.loads((BASE/'check_hyperplane_transition.json').read_text())
require(len(reference)==4,'reference length')
for a,b in zip(records,reference):
    for key in ('normal_support','minimum','negative_count','sha256'):
        require(a[key]==b[key],('reference mismatch',key,a['normal_support']))
    require(a['counts']=={int(k):v for k,v in b['counts'].items()},'histogram mismatch')
require(before=={f:digest(BASE/f) for f in names},'input mutation')
out={'status':'pass','profiles':len(data)*4,'all_hashes_match':True,'frozen_input_sha256':before,
     'verifier_sha256':digest(Path(__file__).resolve()),'seconds':time.monotonic()-start,'records':records}
if '--save-certificate' in sys.argv:
    (HERE.parent.parent/'data'/'independent_hyperplane_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ('status','profiles','all_hashes_match','seconds')}))
