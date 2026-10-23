import json, math, itertools, collections, hashlib
from pathlib import Path
R=Path(__file__).resolve().parent
P=R/'upstream_parent_quartic31.json'
src=json.loads(P.read_text());n=len(src['variables']); blocks=[]
for eq in src['equations']:
    d=collections.defaultdict(int)
    for row in eq['terms']:
        a=row['powers']; supp=[i for i,k in enumerate(a[:n]) if k]
        for k in itertools.product(*(range(a[i]+1) for i in supp)):
            c=row['coefficient']; b=[0]*n+a[n:]
            for i,v in zip(supp,k): b[i]=v;c*=math.comb(a[i],v)
            d[tuple(b)]+=c
    grouped=collections.defaultdict(dict)
    for a,c in sorted(d.items()):
        if c:
            mon=[i+1 for i,k in enumerate(a[:n]) for _ in range(k)];mon=[0]*(2-len(mon))+mon
            factor=math.factorial(2-sum(a[:n]))*math.prod(math.factorial(v) for v in a[:n])
            grouped[tuple(mon)][a[n:]]=c*factor
    blocks.append({'equation':eq['number'],'pairs':[list(p) for p in grouped], 'terms':[{'pair':list(p),'coefficient':[{'powers':list(a),'coefficient':c} for a,c in cs.items()]} for p,cs in grouped.items()]})
marked=sorted({tuple(p) for b in blocks for p in b['pairs']})
data={'variables':['1']+src['variables'],'blocks':blocks,'marked_pairs':marked,'parent_sha256':hashlib.sha256(P.read_bytes()).hexdigest()}
(R/'source_support.json').write_text(json.dumps(data,indent=2)+'\n')
(R/'marked.txt').write_text(str(n+1)+' '+str(len(marked))+'\n'+'\n'.join(' '.join(map(str,p)) for p in marked)+'\n')
print('marked',len(marked),'quadratic',len([p for p in marked if p[0]]),'sizes',[len(b['pairs']) for b in blocks]);print(marked)
