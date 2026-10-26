from pathlib import Path
from itertools import product
import json, hashlib, random, re
D=Path(__file__).resolve().parent
B=D.parent
metrics=json.loads((D/'candidate_metrics.json').read_text())
manifest={x['path']:x for x in json.loads((B/'provenance/selected_manifest.json').read_text())}
checks=[]
for x in metrics['candidates']:
    path=f"Computability/DiophantineConsistency/Lean/DiophantineConsistency/{x['module']}.lean"
    data=(B/'sources'/path).read_bytes()
    sha=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    checks.append({'module':x['module'],'sha_matches_pinned_tree':sha==manifest[path]['sha']})
s=(D/'CurrentSimplificationCandidates.lean').read_text()
# This only checks dangerous declarations/tactic holes, not elaboration.
checks.append({'no_sorry_admit_axiom_declarations':not re.search(r'\b(sorry|admit)\b|^\s*axiom\b',s,re.M)})
count_one=0
for n in range(7):
    for f in product(range(3),repeat=n):
        if sum(f)<=1:
            assert all(x==0 for x in f) or any(f[i]==1 and all(j==i or f[j]==0 for j in range(n)) for i in range(n))
            count_one+=1
# Test the exact prefix identity underlying both offset candidates. It retains
# the prefix hypotheses only; ignored later entries may exceed one.
r=random.Random(2011)
count_prefix=0
def word(f,n): return sum(2**j*f[j] for j in range(n))
for k,n in [(1,8),(2,7)]:
    for bits in product(range(2),repeat=n):
        for _ in range(10):
            f=[r.randrange(6) for _ in range(k)]+list(bits)+[r.randrange(6) for _ in range(k)]
            assert word(f,k+n)==(2**k*word(f[k:],k+n))%(2**(k+n))+word(f,k)
            count_prefix+=1
count_cycle=0
for n in range(1,9):
    for values in product([False,True],repeat=n):
        if values[0] and all(not values[i] or values[(i+1)%n] for i in range(n)):
            assert all(values)
            count_cycle+=1
result={'status':'STATIC_AND_FINITE_SMOKE_ONLY','lean_compilation':'NOT RUN; no Lean runtime; no installation attempted',
        'source_checks':checks,'one_hot_arrays_checked':count_one,'prefix_cases_checked':count_prefix,
        'positive_cycle_sizes_checked':'1..8','cycle_premise_satisfying_predicates':count_cycle,
        'warning':'Finite arithmetic checks do not validate Lean elaboration, simp behavior, universes, or imported API.'}
(D/'static_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
