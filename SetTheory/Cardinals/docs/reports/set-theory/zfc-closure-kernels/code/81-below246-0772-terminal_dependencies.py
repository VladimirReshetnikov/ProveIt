"""Locate borrowed decoder rows outside the declared instruction-path positions."""
from pathlib import Path
import sys,json,collections
sys.path.insert(0,str(Path(__file__).parent));import compile_rotated as c
ls=[]
def walk(n,p,qs):
 for b,e in enumerate(c.ns[n]):
  if e[0]=='CN':walk(e[1],p+str(b),qs+[c.nq[n]])
  else:
   for g in ((0,1) if e[0]=='CD' else (None,)):ls.append((p+str(b),qs+[c.nq[n]],e,g))
walk(0,'',[])
raw=(Path(__file__).parent/'cases.txt').read_text().splitlines();assert len(ls)==len(raw)==8391
borrowed=collections.Counter();examples={}
for ci,(line,(p,qs,op,g)) in enumerate(zip(raw,ls)):
 a=list(map(int,line.split()));i=0;n=a[i];i+=1;tape=set(a[i:i+n]);i+=n;wantq,wanth,n=a[i:i+3];i+=3;wantt=set(a[i:i+n]);state=96;h=0
 for tick in range(10000):
  b=int(h in tape);row=(state,b)
  if state in c.qsig and not (0<=h<len(p) and state==qs[h] and b==int(p[h])):
   borrowed[row]+=1;examples.setdefault(row,(ci,p,op,g,tick,h))
  w,d,state=c.T[row]
  if w:tape.add(h)
  else:tape.discard(h)
  h+=1 if d=='R' else -1
  if state==254 or state==96 and h==wanth and tape==wantt:break
 else:raise AssertionError(ci)
classes=sorted({s for q,b in borrowed for s in c.qsig[q]})
out={'classes':classes,'rows':[{'row':[q,b],'transition':c.T[q,b],'count':n,'example':examples[q,b],'classes':sorted(c.qsig[q])} for (q,b),n in sorted(borrowed.items())]}
(Path(__file__).parent/'original_terminal_dependencies.json').write_text(json.dumps(out,indent=2)+'\n')
print('classes',len(classes),classes);print('rows',len(borrowed),list(sorted(borrowed)))
