"""Fresh exact finite Boolean algebra. No external/source scientific code imported.
Enumerate NC five-input tables by the Hattori--Takesue/Boccara--Fuks identity,
then exhibit noninjectivity by equal one-step output words on periodic inputs.
No trajectory evolution is performed. All arithmetic uses Python integers.
"""
import json
from pathlib import Path
from collections import Counter
N=5
words=[tuple((x>>(N-1-i))&1 for i in range(N)) for x in range(1<<N)]
def idx(w):
    z=0
    for b in w:z=(z<<1)|b
    return z
terms=[[(idx((0,)*k+w[1:N-k+1]),idx((0,)*k+w[:N-k])) for k in range(1,N)] for w in words]
rules=[]
for mask in range(1<<15):
    seed=[0]+[(mask>>i)&1 for i in range(15)]
    f=tuple(w[0]+sum(seed[a]-seed[b] for a,b in terms[t]) for t,w in enumerate(words))
    if all(v in (0,1) for v in f):
        assert list(f[:16])==seed
        rules.append(f)
assert len(rules)==428
shifts={tuple(w[k] for w in words):k-2 for k in range(5)}
left=set(range(len(rules)))
cert={}
for period in range(1,13):
    inputs=[tuple((x>>(period-1-i))&1 for i in range(period)) for x in range(1<<period)]
    windows=[tuple(idx(tuple(x[(i+j-2)%period] for j in range(5))) for i in range(period)) for x in inputs]
    for ri in list(left):
        f=rules[ri]; seen={}
        for xi,win in enumerate(windows):
            y=idx(tuple(f[t] for t in win))
            if y in seen:
                cert[ri]={'period':period,'a':seen[y],'b':xi,'image':y}
                left.remove(ri);break
            seen[y]=xi
    if len(left)==5:break
survivors=[{'rule':idx(tuple(reversed(rules[i]))),'table':''.join(map(str,rules[i])),'shift':shifts.get(rules[i])} for i in sorted(left)]
result={'count':len(rules),'survivors':survivors,'collision_period_counts':dict(sorted(Counter(v['period'] for v in cert.values()).items())),'tested_max_period':period,'certificates':[{'table':''.join(map(str,rules[i])),**v} for i,v in sorted(cert.items())]}
assert len(left)==5 and all(rules[i] in shifts for i in left)
print(json.dumps({k:v for k,v in result.items() if k!='certificates'},indent=2))
with open(Path(__file__).with_name('radius2_certificate.json'),'w') as fh: json.dump(result,fh,indent=2)
