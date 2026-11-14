import itertools
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'upstream/U208_ConPA_2026-10-29/U208_ConPA_2026-10-29'
out=ROOT/'analysis/register_permutations'
out.mkdir(exist_ok=True)
mapping={int(q):v for q,v in json.loads((BASE/'baseline/legacy_mapping.json').read_text()).items()}
legacy_core={0,1,2,3,4,5,6,7,9,10,13,14,19,20,28,29,30,31,38,40,41,42,43,44,
             48,56,57,58,59,60,63,64,69,73,74,75,83,84,85,95,97,109,112,131}
core={q for q,v in mapping.items() if v in legacy_core}
skip=(51,36,25,48,32,33,22,55,60)
phy=(6,2,0,4,3,7,8,5,1)
t={}
for line in (BASE/'machine/u208.native.tm').read_text().splitlines():
    if not line or line.startswith('#'):continue
    q,b,w,d,z=line.split();t[int(q),int(b)]=(int(w),d,int(z))
states=sorted({q for q,b in t})
zero=[1,3,4,6,7]
records=[]
for i,new in enumerate(itertools.permutations(zero)):
    perm=list(range(9))
    for a,b in zip(zero,new):perm[phy[a]]=phy[b]
    targets={q:skip[perm[j]] for j,q in enumerate(skip)}
    candidate={key:(w,d,targets.get(z,z) if key[0] not in core else z)
               for key,(w,d,z) in t.items()}
    groups={}
    for q in states:groups.setdefault((candidate[q,0],candidate[q,1]),[]).append(q)
    duplicates=[v for v in groups.values() if len(v)>1]
    pairs=sum(1 for q in states for r in states if q<r for b in(0,1)
              if candidate[q,b]==candidate[r,b])
    name=f'permutation{i:03d}'
    (out/(name+'.tm')).write_text('#! start 0\n'+''.join(f'{q} {b} {w} {d} {z}\n'for(q,b),(w,d,z)in sorted(candidate.items())))
    rec={'name':name,'physical_permutation':perm,'new_phy':[perm[v] for v in phy],
         'changed_rows':sum(candidate[k]!=t[k] for k in t),'literal_duplicates':duplicates,
         'shared_row_pairs':pairs}
    records.append(rec)
(out/'inventory.json').write_text(json.dumps(records,indent=2)+'\n')
print('CORE',sorted(core))
print('Literal duplicates', [r for r in records if r['literal_duplicates']])
print('Pair range', min(r['shared_row_pairs'] for r in records),max(r['shared_row_pairs'] for r in records))
