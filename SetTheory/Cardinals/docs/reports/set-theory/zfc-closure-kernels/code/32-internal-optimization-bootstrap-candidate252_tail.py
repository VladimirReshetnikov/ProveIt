"""Exploratory one-symbol positive-decrement tail change."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent
import importlib.util,json
sp=importlib.util.spec_from_file_location('gen',ROOT.parent/'vendor/upstream/ZF/m253/tools/generate_candidate.py');g=importlib.util.module_from_spec(sp);sp.loader.exec_module(g)
T=g.patched_rows();T[49,1]=(0,'R',64);T[97,0]=(1,'L',112);T={k:v for k,v in T.items()if k[0]!=5}
assert len(T)==504 and all(v[2]not in(5,8)for v in T.values())
(ROOT.parent/'candidate252_tail_oldlabels.tm').write_text('#! start 97\n'+''.join(f'{q} {b} {w} {d} {p}\n'for(q,b),(w,d,p)in sorted(T.items())))

def frame(tape,h):
 if h-1 not in tape or any(x<h-1 for x in tape):return None
 end=max(tape);header=next((j for j in range(h,end+1)if j in tape),None)
 if header is None:return None
 regs=[];j=header+1
 while j<=end:
  if j in tape:return None
  j+=1;start=j
  while j in tape:j+=1
  if j==start:return None
  regs.append(j-start-1)
 if len(regs)<9:return None
 return {'gap':header-h,'regs':regs[:9],'ext_count':len(regs)-9,'ext_nonzero':[[j,v]for j,v in enumerate(regs[9:])if v],'head':h,'ones':len(tape)}

ones=set();head=0;state=97;frames=[];seeninitial=False;target=None
for n in range(4000000):
 if state==96:
  f=frame(ones,head)
  if f:
   if len(frames)<10:frames.append(dict(step=n,**f))
   if f['regs']==[0,0,0,0,0,0,2,0,0] and not seeninitial:
    print('initial',n,f,flush=True);seeninitial=True
   if f['regs']==[0,2,0,0,0,0,5,0,0] and f['gap']==40:
    target={'step':n,**f,'state':state,'all_ones':sorted(ones)};print('TARGET',n,f,flush=True);break
 bit=int(head in ones);w,d,state=T[state,bit]
 if w:ones.add(head)
 else:ones.discard(head)
 head+=1 if d=='R'else-1
 if abs(head)>50000:
  print('escape',n,head,state);break
out={'frame_examples':frames,'target':target,'final':{'step':n,'head':head,'state':state,'ones':len(ones)}}
print(json.dumps(out,indent=2));(ROOT/'candidate252_tail_boot.json').write_text(json.dumps(out,indent=2)+'\n')
