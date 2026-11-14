from pathlib import Path
import json,sys
import tag_prepare as p
ROOT=p.ROOT
src=ROOT/'reference/original_search'
out=p.out
attr=(src/'leaf_attrs.txt').read_text().splitlines()
for k,u,e in [(5,2,4),(6,2,4),(8,2,4),(4,3,2)]:
 name=f'k{k}u{u}e{e}';d=out/name;d.mkdir(exist_ok=True)
 raw={(q,b):a for(q,b),a in p.raw.items()if q<1300}
 if k in (5,6):
  raw[190,0]=(0,True,330);raw[190,1]=(1,True,99 if k==5 else 330)
  raw[330,0]=(0,True,61);raw[330,1]=(1,True,99)
 elif k==8:
  raw[190,0]=(0,True,330);raw[190,1]=(1,True,330)
  raw[330,0]=(0,True,99);raw[330,1]=(1,True,99)
 gg,ww,ch=p.variant(u,e)
 vals=[];idx={}
 def enc(t):
  if t in idx:return idx[t]
  if p.c.isnode(t):
   l=enc(t[0]);r=enc(t[1]);v=(1,l,r,0)
  else:v=(0,-1 if t==p.c.BREAK else p.c.MACROS[t],-1,-1)
  i=len(vals);vals.append(v);idx[t]=i;return i
 rt=enc(gg)
 controls=sorted({q for q,b in raw})
 lines=[str(len(controls))]
 for q in controls:lines.append(str(q)+' '+' '.join(str(int(v))for b in(0,1)for v in raw[q,b]))
 lines+=['1',f'0 {len(vals)} {rt}']+[' '.join(map(str,v))for v in vals]
 (d/'templates.txt').write_text('\n'.join(lines)+'\n')
 at=attr.copy()
 if k>4:
  at[0]=str(int(at[0])+1);at.append('330 2 1 1 1 1'if k in(5,6)else'330 2 2 2 2 1')
 (d/'attrs.txt').write_text('\n'.join(at)+'\n')
 screen=(src/'screen_global.cpp').read_text()
 if k in(5,6):screen=screen.replace('if(l==99&&r==99){value[i]=190;continue;}','if(l==61&&r==99){value[i]=330;continue;}')
 elif k==8:screen=screen.replace('if(l==99&&r==99){value[i]=190;continue;}','if(l==99&&r==99){value[i]=330;continue;}')
 (d/'screen_global.cpp').write_text(screen)
 code=(src/'search_radix.cpp').read_text()
 code=code.replace('if(cycle++%1000==999)', 'if(false)')
 code=code.replace('if(pick(1000)<3)', 'if(false)')
 code=code.replace('case 190:return "\\\"node61\\\"";', 'case 190:return "\\\"node61\\\"";case 330:return "\\\"nodeIncExtra\\\"";')
 # Preserve all same-cost plateaus rather than a minimum-only file.
 (d/'search.cpp').write_text(code)
 print(name,'fixed',len(controls),'word',len(ww))
