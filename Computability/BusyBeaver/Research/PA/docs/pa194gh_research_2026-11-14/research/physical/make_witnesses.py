from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).parent/'vendor'))
import compiler as c
sites,ins,contracts=c.source(c.read_grammar('vendor/grammar.json'))
def frame(path,regs,extra=0):
 out={-1,48+extra}
 out.update(i for i,b in enumerate(path) if b)
 pos=48+extra
 for v in regs:
  pos+=2
  out.update(range(pos,pos+v+1));pos+=v
 return out
selected=[(0,0),(0,1),(5,0),(5,1),(3,0),(8,0)]
with open('witnesses.txt','w') as f:
 for pc,branch in selected:
  path,op,arg=sites[pc];cmd=ins[pc]
  regs=[0]*10
  if cmd[0]=='dec':
   r,z,p=cmd[1:];regs[c.PHYSICAL[r]]=branch
   nextpc=p if branch else z
   out=regs.copy();out[c.PHYSICAL[r]]=0;extra=branch
  elif cmd[0]=='inc':
   r,nextpc=cmd[1:];out=regs.copy();out[c.PHYSICAL[r]]+=1;extra=0
  elif cmd[0]=='jump':nextpc=cmd[1];out=regs.copy();extra=0
  else:continue
  left=sorted(frame(path,regs));right=sorted(frame(sites[nextpc][0],out,extra))
  print(pc,branch,84,len(left),*left,84,len(right),*right,file=f)
  print(pc,branch,cmd,'target',nextpc)
