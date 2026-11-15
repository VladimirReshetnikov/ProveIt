from pathlib import Path
import sys,json,collections,importlib.util,time
from types import SimpleNamespace
import argparse
HERE=Path(__file__).resolve().parent;BASE=HERE.parents[1]
import engine_helpers as b
from engine_foldscreen import proposed_folds
parser=argparse.ArgumentParser(description='Replay the bounded coupled scanner association search.')
parser.add_argument('--output',type=Path,default=HERE/'replayed_search_scanner')
parser.add_argument('--depth',type=int,default=7,help='Number of breadth-first levels processed')
args=parser.parse_args();OUT=args.output;OUT.mkdir(parents=True,exist_ok=True)
c=SimpleNamespace(b=b,proposed_folds=proposed_folds,ax=b.grammar(BASE/'construction/inputs/primary.grammar.json'),ins=__import__('json').loads((BASE/'machines/PA194OR/parent.instructions.json').read_text()))
P=HERE/'rejected_operand193' 
raw=b.read_table(P/'raw.tm');raw[4001,0]=(0,True,111);raw[4001,1]=(1,True,90);raw[69,0]=(0,False,4001)
raw=b.rename(raw,{4000:185,4001:92,2004:333})
# Reassign the existing history selector: node20 will enter on zero, node72 on one.
raw[92,0]=(0,True,90);raw[92,1]=(1,True,111)
raw.update({(84,0):(0,True,68),(53,0):(0,True,69),(53,1):(1,True,214),(310,0):(0,True,53),(100,0):(0,True,213),(100,1):(1,True,174),(174,0):(0,True,28),(174,1):(1,True,164)})
nodes={k:b.tup(v)for k,v in json.loads((P/'nodes.json').read_text()).items()}
nodes.update(node21=('node20','node170'),node171=('node21','node23'),node172=('node7','node171'),node162=('node37','node163'),node164=('node75','node162'))
macros={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,'node72':69,'node75':213,'node142':194,'node150':221,('leaf','inc',1):61,'node60':99,'node61':190,('node55','node65'):333}
inc=('leaf','inc',1);macros[(inc,inc)]=99;macros[((inc,inc),(inc,inc))]=190
BREAK=('leaf','breakTo',1)
def isnode(t):return isinstance(t,tuple)and len(t)==2
def build(t,short=True):
 rr={k:v for k,v in raw.items() if k[0]<1300};index={}
 def state(t):
  if t in macros:return macros[t]
  if t in index:return index[t]
  assert isnode(t),t
  q=2000+len(index);index[t]=q
  for bit,child in enumerate(t):rr[q,bit]=(0,False,302)if child==BREAK else(bit,True,state(child))
  return q
 rt=state(t);rr[101,1]=(1,True,rt)
 if short:rr[23,0]=(0,False,75);rr.pop((34,0));rr.pop((34,1))
 return b.reachable(rr)
def targetpath(t,p=''):
 if t=='node72':return p
 if not isnode(t):return None
 return targetpath(t[0],p+'0') or targetpath(t[1],p+'1')
def replace(t,p,x):
 if not p:return x
 k=int(p[0]);l=list(t);l[k]=replace(l[k],p[1:],x);return tuple(l)
def get(t,p):
 for x in p:t=t[int(x)]
 return t
def mutations(t):
 p=targetpath(t)
 for k in range(len(p)):
  pp=p[:k];a,d=get(t,pp)
  if isnode(a):yield replace(t,pp,(a[0],(a[1],d)))
  if isnode(d):yield replace(t,pp,((a,d[0]),d[1]))
sys.path.insert(0,str(BASE/'construction/vendor'));import symbolic_runtime as rt
def contracts(sites,ins):
 def frame(i,extra=0,effect=rt.PLAIN):return rt.frame(tuple(map(int,sites[i][0])),extra,effect)
 def target(i,extra=0,effect=rt.PLAIN):return rt.canonical(frame(i,extra,effect))
 cs=[]
 for i,code in enumerate(ins):
  st=frame(i)
  if code[0]=='inc':_,r,n=code;cs.append((i,None,st,target(n,0,('x','inc',rt.PHYSICAL[r]))))
  elif code[0]=='dec':_,r,z,n=code;cs.extend([(i,(rt.PHYSICAL[r],True),st,target(z)),(i,(rt.PHYSICAL[r],False),st,target(n,1,('x','dec',rt.PHYSICAL[r])))])
  elif code[0]=='jump':cs.append((i,None,st,target(code[1])))
  else:cs.append((i,None,st,None))
 return cs
seen={c.ax};front=[c.ax];results=[];count=0;best=999;started=time.monotonic()
for depth in range(args.depth):
 nextfront=[]
 for t in front:
  if targetpath(t)[-1]=='1':
   rr=build(t);ff=c.proposed_folds(rr);price=len(rr)//2-len(ff)
   if price<best:best=price;print('best',price,'depth',depth,'raw',len(rr)//2,'folds',len(ff),flush=True)
   if price<=194:
    ss,ii=b.source(nodes,t);assert ii==c.ins
    try:child,ali=b.apply_folds(rr,ff);lc=b.check_folds(rr,child,ali,ff)
    except (AssertionError,KeyError):continue
    cv=rt.validate(child,contracts(ss,ii));count+=1
    rec={'depth':depth,'price':price,'raw':len(rr)//2,'folds':len(ff),'validation':cv,'path72':targetpath(t)}
    if cv['ok']:
     try:rec['startup']=b.startup(child,ss[25][0])
     except Exception as e:rec['startup_error']=str(e)
     dest=OUT/('hit'+str(len(results)));dest.mkdir(exist_ok=True);(dest/'native.tm').write_text(b.table_text(child));b.dump(dest/'sites.json',ss);b.dump(dest/'instructions.json',ii);b.dump(dest/'tree.json',t);b.dump(dest/'receipt.json',rec)
    results.append(rec)
    if count%10==0 or cv['ok']:print('trial',count,rec,flush=True)
  for u in mutations(t):
   if u not in seen:seen.add(u);nextfront.append(u)
 if len(nextfront)>10000:nextfront=nextfront[:10000]
 print('depth',depth,'front',len(front),'next',len(nextfront),'seconds',time.monotonic()-started,flush=True)
 front=nextfront
 if not front:break
b.dump(OUT/'summary.json',{'variants':len(seen),'validated':count,'best':best,'results':results})
