from pathlib import Path
import sys,json,itertools,time
exec((Path(__file__).resolve().parent/'eq_variants.py').read_text().split('for i,t in enumerate(hits):')[0])
from collections import Counter
out=(Path(__file__).resolve().parent/'output/equality');out.mkdir(parents=True,exist_ok=True)
G,P=b.decoder_map(T,TREE)
OLD=hits[10];PROTECT=set(json.loads((BASE/'research/experiments/receipts/engine_protected.json').read_text())['states'])|{302}
FREE=[77,87,88,301]
PHY=(6,2,0,4,3,7,8,5,1)
def frame(pc,logical,spares,gap=0):
 physical=[None]*9
 for i,j in enumerate(PHY):physical[j]=logical[i]
 ones={-1,64+gap}|{i for i,b in enumerate(pc)if b=='1'};pos=65+gap
 for value in physical+list(spares):pos+=1;ones.update(range(pos,pos+value+1));pos+=value+1
 return ones

def inc(pc):
 if not pc:return '',1
 n=len(pc);v=int(pc,2)+1
 return format(v%(1<<n),'0'+str(n)+'b'),int(v==1<<n)
def strip(pc,bit,n):
 for i in range(len(pc)-1,-1,-1):
  if pc[i]==bit:
   n-=1
   if n==0:return pc[:i]
 return ''
def expected(pc,op,arg,logical,spares,gap):
 logical=list(logical);spares=list(spares);shift=0
 if op=='CI':logical[arg]+=1;spares.append(1);pc,shift=inc(pc)
 elif op=='CD'and logical[arg]:logical[arg]-=1;gap+=1;pc,shift=inc(pc)
 elif op in('CD','CB'):pc,shift=inc(strip(pc,'0',1 if op=='CD'else arg))
 elif op=='CC':pc=strip(pc,'1',arg)
 else:raise ValueError(op)
 return 84,-shift,{x-shift for x in frame(pc,logical,spares,gap+shift)}
def dispatch(q,h,ones):
 if q!=84 or h-1 not in ones or any(x<h-1 for x in ones):return False
 right=sorted(x for x in ones if x>=h+52)
 if not right or right[0]<h+64:return False
 p=right[0]+1;last=max(ones);values=[]
 while p<last:
  if p in ones or p+1 not in ones:return False
  start=p+1;p=start
  while p in ones:p+=1
  values.append(p-start-1)
 return p==last+1 and len(values)>=10
def testaction(tt,action,pcs,op,arg):
 for pc in pcs:
  for val,spare,gap in[(0,1,0),(1,1,0),(3,2,3),(2,0,1)]:
   regs=[val]*9;spares=[spare,1];ones=frame(pc,regs,spares,gap);want=expected(pc,op,arg,regs,spares,gap)
   h=len(pc)-1;w,d,q=action
   if w:ones.add(h)
   else:ones.discard(h)
   h+=d
   for k in range(6000):
    if dispatch(q,h,ones):
     if(q,h,ones)!=want:return False
     break
    if q==254 or(q,int(h in ones))not in tt:return False
    v=int(h in ones);w,d,q=tt[q,v]
    if w:ones.add(h)
    else:ones.discard(h)
    h+=d
   else:return False
 return True

def repl(n,old,new):return new if n==old else n if s.leaf(n)else(repl(n[0],old,new),repl(n[1],old,new))
def swap(n):return(n[0],11-n[1])if s.leaf(n)and n[0]in('CI','CD')and n[1]in(5,6)else n if s.leaf(n)else(swap(n[0]),swap(n[1]))
def compile(h):
 tree=repl(TREE,OLD,h);rows=s.sites(tree);nodepaths={}
 def visit(n,p=''):
  if s.leaf(n):return
  nodepaths.setdefault(n,[]).append(p);visit(n[0],p+'0');visit(n[1],p+'1')
 visit(tree)
 active=set()
 def walk(n):
  if s.leaf(n)or n in active:return
  active.add(n);walk(n[0]);walk(n[1])
 walk(h)
 mapped={};tt=T.copy();claimed=set();free=list(FREE);fresh=303
 # root stays77 so unchanged parent paths route it
 mapped[h]=77;claimed.add(77);free.remove(77)
 for n in sorted(active,key=repr):
  if n in mapped:continue
  candidates=[q for q,ns in G.items()if n in ns and q not in claimed]
  if candidates:
   # P6 uses108 in comparison;13 remains engine
   mapped[n]=max(candidates)
   if mapped[n] in free:free.remove(mapped[n])
  else:
   q=free.pop(0)if free else fresh
   if q==fresh:fresh+=1
   mapped[n]=q;claimed.add(q)
 for n,q in mapped.items():
  if q not in claimed:continue
  for bit,ch in enumerate(n):
   if not s.leaf(ch):tt[q,bit]=(bit,1,mapped[ch])
   else:tt[q,bit]=({'CD':lambda a:(bit,1,45 if a==5 else 21),'CI':lambda a:(bit,1,63 if a==5 else 13),'CC':lambda a:(0,-1,1 if a==1 else 10),'CB':lambda a:(0,-1,302)}[ch[0]])(ch[1])
 for n,q in mapped.items():
  for bit,ch in enumerate(n):
   if not s.leaf(ch):continue
   pcs=[p+str(bit) for p in nodepaths[n] if any(p.startswith(root) for root in P[77])]
   if q not in claimed:
    if not testaction(tt,tt[q,bit],pcs,*ch):raise ValueError(('shared leaf context',q,bit,ch,pcs[:2],len(pcs)))
    continue
   oldchoice=T.get((q,bit));choices=[]
   if oldchoice:choices.append(oldchoice)
   choices += [(bit,1,z)for z in sorted({q for q,c in T})]+[(w,d,z)for w,d,z in itertools.product((0,1),(-1,1),sorted({q for q,c in T}))]
   for action in choices:
    if testaction(tt,action,pcs,*ch):tt[q,bit]=action;break
   else:raise ValueError(('no leaf implementation',q,bit,ch,pcs[:2],len(pcs)))
 reach={0};todo=[0]
 for q in todo:
  for bit in(0,1):
   z=tt[q,bit][2]
   if z!=254 and z not in reach:reach.add(z);todo.append(z)
 tt={k:v for k,v in tt.items()if k[0]in reach}
 # retain302 currently; deleting it needs separate replacement of returns
 b.decoder_map(tt,tree)
 return tree,tt
if __name__=='__main__':
 results=[]
 for i,h0 in enumerate(hits):
  for reflect in(False,True):
   h=swap(h0)if reflect else h0;name=f'v{i:02d}'+('r'if reflect else'');start=time.monotonic()
   try:
    tree,tt=compile(h);d=out/name;d.mkdir(parents=True,exist_ok=True);(d/'candidate.tm').write_bytes(b.table_bytes(tt));(d/'sites.json').write_bytes(s.compact(s.sites(tree)))
    r={'variant':name,'states':len(tt)//2,'metrics':s.metrics(tree),'seconds':time.monotonic()-start}
   except Exception as e:r={'variant':name,'error':repr(e),'seconds':time.monotonic()-start}
   results.append(r);print(json.dumps(r),flush=True);(out/'summary.json').write_text(json.dumps(results,indent=2))
