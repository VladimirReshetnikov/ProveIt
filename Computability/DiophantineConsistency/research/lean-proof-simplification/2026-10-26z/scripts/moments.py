"""Independent finite-data check; not a replacement for Lean kernel proofs."""
from pathlib import Path
import re, json, hashlib, argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('repository', type=Path, help='Path to a checkout of ProveIt at commit 553a5f7a463cbaab8800ff8148fef0bc5a9e1b22')
parser.add_argument('--output', type=Path, help='Optional JSON output path')
args=parser.parse_args()
root=args.repository/'Computability/DiophantineConsistency/Lean/DiophantineConsistency' 
s=(root/'WangTiles942Data.lean').read_text()
body=s.split('def actionCache : Array Action := #[',1)[1].split(']',1)[0]
actions=[(a=='true',d=='true',int(q)) for a,d,q in re.findall(r'\((true|false), (true|false), (\d+)\)',body)]
assert len(actions)==430
targets={d:sorted({q for a,e,q in actions if e==d}) for d in [False,True]}
rail=lambda d,q:205-199*int(d)+sum(i<q for i in targets[d])
trans=[((1-int(d))*rail(False,q),j+2,int(d)*rail(True,q),int(a)) for j,(a,d,q) in enumerate(actions)]
signals={d:[(int(d)*rail(d,q),b,(1-int(d))*rail(d,q),2*q+b+2) for q in targets[d] for b in range(2)] for d in [False,True]}
copies=[(0,432*a+b,0,432*a+b) for a in [1,0] for b in range(2)]
tail=[(0,432*a+b,0,438) for a in range(2) for b in range(2)]+[(2,434,2,0),(3,436,4,4),(4,436,4,0)]+[(1,438,1,t) for t in [434,435,436]]+[(a*a,437,b,437) for a in range(3) for b in range(3)]
families={'start':[(2,435,3,1)],'transition':trans,'copies':copies,'right_signals':signals[True],'left_signals':signals[False],'tail':tail}
weight=lambda t:1+1024*(1+t[0]+256*t[1]+131072*t[2]+33554432*t[3])
mom=lambda l:(len(l),)+tuple(sum(t[i] for t in l) for i in range(4))
linear=lambda v:1025*v[0]+1024*v[1]+262144*v[2]+134217728*v[3]+34359738368*v[4]
result={}
for name,l in families.items():
 m=mom(l); mass=sum(map(weight,l));assert mass==linear(m)
 result[name]={'moments':m,'mass':mass}
allrows=sum(families.values(),[]); assert len(allrows)==942
result['all']={'moments':mom(allrows),'mass':sum(map(weight,allrows))}
result['south_le_45']={'moments':mom([t for t in allrows if t[3]<=45]),'mass':sum(weight(t) for t in allrows if t[3]<=45)}

for d in [False,True]:
 l=[t for t in signals[d] if t[3]<=45];qs=[q for q in targets[d] if q<=21]
 result['low_signals_'+str(d)]={'moments':mom(l),'mass':sum(map(weight,l)),'target_count':len(qs),'target_sum':sum(qs),'rail_sum':sum(rail(d,q) for q in qs)}
result['targets']={str(d):{'count':len(targets[d]),'sum':sum(targets[d]),'rail_sum':sum(rail(d,q) for q in targets[d])} for d in [False,True]}
result['source_sha256']=hashlib.sha256(s.encode()).hexdigest()
print(json.dumps(result,indent=2))
if args.output:
    args.output.write_text(json.dumps(result,indent=2)+'\n')
