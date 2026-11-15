import json,itertools,random,argparse
from pathlib import Path
HERE=Path(__file__).parent
parser=argparse.ArgumentParser();parser.add_argument('--positive',action='store_true');parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
base=json.loads((HERE/'inputs/JH5X.tree.json').read_text())
mac={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,'node72':69,'node75':213,'node142':194,'node150':221,'node60':99,'node61':190}
def tup(t):
 if isinstance(t,str):return mac[t]
 if t==['leaf','inc',1]:return 61
 if t==['leaf','breakTo',1]:return -1
 return tuple(map(tup,t))
base=tup(base)
def flat(t):return [t]if isinstance(t,int)else flat(t[0])+flat(t[1])
def replace(t,w):
 it=iter(w)
 def go(t):return next(it)if isinstance(t,int)else tuple(map(go,t))
 z=go(t);assert next(it,None)is None
 return z
# N(H) -> U(D, U(D,H) -> A), with freely chosen A.
b=([12,12,19,61,90,98,90,61,61,166,90,98,90,61,61,90] if args.positive else [12,19,61,90,12,98,90,61,61,166,90,98,90,61,61,90])
assert len(b)==16
w=flat(base);assert len(w)==188
out=[]
# The same mathematical schema under all independent D,A,H renamings;
# existing six-head order and unchanged prefix/gate retained in every input.
for pp in itertools.permutations((98,166,12)):
 mp=dict(zip((98,166,12),pp));ww=w[:18]+[mp.get(v,v)for v in b]+w[34:]
 out.append(replace(base,ww))
# Add balanced and randomized associations to avoid inherited topology bias.
rng=random.Random(202611152001)
for _ in range(30):
 ww=w[:18]+b+w[34:]
 def assoc(v):
  if len(v)==1:return v[0]
  k=rng.randrange(1,len(v));return assoc(v[:k]),assoc(v[k:])
 out.append(assoc(ww))
fixed=(HERE/'inputs/fixed_runtime_rows.txt').read_text().splitlines()
lines=fixed+[str(len(out))]
for num,t in enumerate(out):
 ns=[];cache={}
 def emit(t):
  if t in cache:return cache[t]
  row=(0,t,-1,-1)if isinstance(t,int)else (1,emit(t[0]),emit(t[1]),0)
  q=len(ns);ns.append(row);cache[t]=q;return q
 root=emit(t);lines.append(f'{num} {len(ns)} {root}')
 lines.extend(' '.join(map(str,r))for r in ns)
args.output.write_text('\n'.join(lines)+'\n')
print('wrote',len(out),'trees')
