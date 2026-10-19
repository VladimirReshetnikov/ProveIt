from pathlib import Path
import sys,collections,json
sys.path.insert(0,str(Path(__file__).parent))
import compile_rotated as c
paths={}
def walk(n,p):
 paths[n]=p
 for b,e in enumerate(c.ns[n]):
  if e[0]=='CN':walk(e[1],p+str(b))
walk(0,'')
allrows=set();result={}
for q,ss in c.qsig.items():
 if len(ss)==1:continue
 deps=set();arcs=[]
 for n in c.qocc[q]:
  p=paths[n]
  for b,e in enumerate(c.ns[n]):
   if e[0]!='CN':continue
   target=c.nq[e[1]];initial={i-len(p)-1:int(x) for i,x in enumerate('1'+p+str(b))};initial={i:b for i,b in initial.items() if b}
   tape=initial.copy();state=q;h=0;trace=[]
   for tick in range(30):
    if tick and state==target and h==1 and tape==initial:break
    row=(state,tape.get(h,0));trace.append(row);w,d,state=c.T[row]
    if w:tape[h]=1
    else:tape.pop(h,None)
    h+=1 if d=='R' else -1
   else:raise AssertionError((q,p,b,target,trace))
   if len(trace)>1:deps.update(trace[1:]);arcs.append((b,p[-8:],target,trace))
 if deps:
  result[q]={'borrowed_rows':sorted(deps),'borrowed_source_classes':sorted({s for state,b in deps for s in c.qsig.get(state,set())}),'arcs':arcs}
  allrows.update(deps)
print('ALL ROWS',sorted(allrows))
print('SOURCE CLASSES',sorted({s for state,b in allrows for s in c.qsig.get(state,set())}))
(Path(__file__).parent/'original_alias_dependencies.json').write_text(json.dumps(result,indent=2)+'\n')
for q,v in result.items():print(q,v['borrowed_rows'],v['borrowed_source_classes'])
