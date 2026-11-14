from pathlib import Path
import json,itertools,argparse
HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description='Generate the 96 joint AX11 semantic grammar seeds.')
parser.add_argument('--repo',type=Path,default=HERE.parents[1]/'ProveIt')
parser.add_argument('--primary',type=Path,default=HERE.parent/'incoming/pa194_ax11_research_2026-11-14/primary')
parser.add_argument('--h-raw',type=Path,help='Optional AX11H raw native table for its fixed controller.')
parser.add_argument('--prefix',default='seeds')
args=parser.parse_args()
REPO=args.repo.resolve()
PRIMARY=args.primary.resolve()
Q=REPO/'Computability/BusyBeaver/Research/PA/docs/pa194q_conpa_2026-11-13'
INC=('leaf','inc',1);BREAK=('leaf','breakTo',1)
MACROS={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,'node72':69,'node75':213,'node142':194,'node150':221,INC:61}
def isnode(x):return isinstance(x,tuple)and len(x)==2
def read(path):
 d=json.loads(path.read_text())
 def rec(x):
  if isinstance(x,list):return tuple(x)
  if x=='node60':return (INC,INC)
  if x=='node61':return ((INC,INC),(INC,INC))
  if x in d['rules']:return tuple(rec(y)for y in d['rules'][x])
  return x
 return rec(d['root'])
def word(x):return word(x[0])+word(x[1])if isnode(x)else[x]
def reword(t,w):
 it=iter(w)
 def go(t):return tuple(go(x)for x in t)if isnode(t)else next(it)
 ans=go(t);assert next(it,None)is None
 return ans
def tarray(t):
 ns=[];seen={}
 def go(t):
  if t in seen:return seen[t]
  row=(1,go(t[0]),go(t[1]),0)if isnode(t)else(0,MACROS[t],-1,-1)
  k=len(ns);seen[t]=k;ns.append(row);return k
 root=go(t);return ns,root
def I(a,b):return ('I',a,b)
def M(a,b):return ('M',a,b)
def E(a,b,flip):return ('E',b,a)if flip else('E',a,b)
def U(a,b):return ('U',a,b)
def N(a):return ('N',a)
def Ex(a,b):return N(U(a,N(b)))
def emit(t):
 if isinstance(t,str):return [{'D':'node55','H':'node58','A':'node70'}[t]]
 op,*args=t
 if op=='N':return emit(args[0])+['node49',INC,'node65']
 a,b=args
 if op=='U':return emit(b)+emit(a)+['node65',INC,INC]
 return emit(a)+emit(b)+['node65']+[INC]*{'I':0,'M':1,'E':3}[op]
def parts(flip,s3,s4,s6):
 def cur(a,b,c,s):return I(b,I(a,c))if s else I(a,I(b,c))
 return [emit(cur(M('H','D'),E('H','A',flip),M('A','D'),s3)),
  emit(cur(E('H','D',flip),M('A','H'),M('A','D'),s4)),
  emit(Ex('D',E('H','D',flip))),
  emit(cur(U('D','A'),U('D',I('A','H')),U('D','H'),s6))]
shapes=[read(PRIMARY/'inputs/primary.grammar.json'),read(Q/'construction/grammar.json')]
base=word(shapes[0]);assert len(base)==190
for p,(a,z)in zip(parts(0,0,0,0),[(54,70),(70,86),(86,102),(102,121)]):assert base[a:z]==p
rows={}
for ln in(args.h_raw or (PRIMARY/'inputs/primary.raw.native.tm')).read_text().splitlines():
 q,b,w,d,n=ln.split();q,b,w,n=map(int,(q,b,w,n))
 if q<1300:rows[q,b]=(w,int(d=='R'),n)
rows[164,1]=(1,1,114)
text=[str(len(rows)//2)]
for q in sorted({q for q,b in rows}):text.append(' '.join(map(str,[q,*rows[q,0],*rows[q,1]])))
seeds=[];info=[]
for flags in itertools.product(range(2),repeat=4):
 for gamma in ['A','D','H']:
  w=base[:]
  for p,(a,z)in zip(parts(*flags),[(54,70),(70,86),(86,102),(102,121)]):assert len(p)==z-a;w[a:z]=p
  w[121:128]=emit(I(gamma,U(gamma,gamma)));w[-1]='node49'
  assert len(w)==190
  for shapeid,shape in enumerate(shapes):
   seeds.append(reword(shape,w));info.append(dict(flags=flags,gamma=gamma,shape=shapeid))
text.append(str(len(seeds)))
for tid,t in enumerate(seeds):
 ns,root=tarray(t);text.append(f'{tid} {len(ns)} {root}')
 text.extend(' '.join(map(str,row))for row in ns)
(HERE/(args.prefix+'.txt')).write_text('\n'.join(text)+'\n')
(HERE/(args.prefix+'.json')).write_text(json.dumps(info,indent=2)+'\n')
print('seed count',len(seeds))
