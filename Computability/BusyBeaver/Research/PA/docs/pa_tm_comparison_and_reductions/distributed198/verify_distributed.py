"""Reproduce the candidate, symbolic contracts, and exact finite startup.

This is an executable checker, not a Lean theorem or a proof of a PA
biconditional.  See NOTES.txt for the trusted symbolic block interface.
"""
from pathlib import Path
import json,hashlib,re
import compiler as c
P=Path(__file__).resolve().parent

def table(path):
 return {(int(q),int(b)):(int(w),d=='R',int(n))for q,b,w,d,n in (line.split()for line in path.read_text().splitlines())}
def freeze(x):
 return tuple(map(freeze,x))if isinstance(x,list)else x

def main():
 if not __debug__:raise RuntimeError('Run without Python -O: assertion checks are required')
 t=c.read_grammar(P/'grammar.json');rows,index,shape=c.build(t)
 folds=json.loads((P/'folds.json').read_text());alias={a:b for a,b,acts in folds};actions={b:acts for a,b,acts in folds};folded={}
 assert len({q for a,b,acts in folds for q in[a,b]})==2*len(folds)
 for(q,bit),act in rows.items():
  if q in alias:continue
  w,d,n=actions[q][bit]if q in actions else act
  folded[q,bit]=w,d,alias.get(n,n)
 assert folded==table(P/'candidate.native.tm')
 labels=json.loads((P/'labels.json').read_text());assert labels[0]==74 and labels[-1]==254
 dense=table(P/'candidate.tm');assert len(dense)==len(folded)
 assert {(labels[q],b):(w,d,labels[n])for(q,b),(w,d,n)in dense.items()}==folded
 old,oldlabels=c.machine();assert all(folded[q,b]==old[q,b]for q in c.BOXSTATES for b in(0,1))
 raw=c.raw_nodes()
 def word(t):
  if c.isnode(t):return word(t[0])+word(t[1])
  if t in ('node60','node61'):return word(raw[t])
  return [t]
 selected=freeze(json.loads((P/'selected-word.json').read_text()))
 assert tuple(word(t))==selected and len(selected)==199
 # Parse the delivered Lean source data independently of the grammar reader.
 parsed={}
 for line in (P/'Program.lean').read_text().splitlines():
  m=re.match(r'def (\w+) : Tree := \.node (.*)',line)
  if not m:continue
  toks=re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b',m[2]);children=[]
  for op,arg,name in toks:children.append(parsed[name]if name else('leaf',op,int(arg)if arg else None))
  assert len(children)==2;(parsed.__setitem__)(m[1],tuple(children))
 def expand(t):
  if isinstance(t,str):return expand(raw[t])
  if c.isnode(t):return expand(t[0]),expand(t[1])
  return t
 assert parsed['x67']==expand(t)
 sites,ins,cs=c.source(t);assert len(sites)==3773 and len(cs)==4908
 emitted=json.loads((P/'sites.json').read_text())
 assert emitted==[{'ordinal':i,'path':''.join(map(str,p)),'op':op,'arg':arg,'instruction':list(ins[i])}for i,(p,op,arg)in enumerate(sites)]
 oldsites,oldins=c.program();prefix=(1,0,1,0,1,0,0,1)
 unchanged=[s for s in sites if s[0][:len(prefix)]!=prefix]
 assert unchanged==[s for s in oldsites if s[0][:len(prefix)]!=prefix]
 assert len(unchanged)==169
 rawcheck=c.validate(rows,cs);print('raw contracts',rawcheck,flush=True);assert rawcheck['ok']
 check=c.validate(folded,cs);print('folded contracts',check,flush=True);assert check['ok']
 # Literal blank run.  Equality checks the complete finite tape, not a prefix.
 expected=[0,0,0,0,0,0,2,0,0]+[1]*26;ones=set();q=0;head=0
 for steps in range(2000000):
  if q==labels.index(84) and head==-2:
   target={head-1,head};pos=head+48;target.add(pos);pos+=1
   for v in expected:pos+=1;target.update(range(pos,pos+v+1));pos+=v+1
   if ones==target:break
  assert q<len(labels)-1,'candidate halted during startup'
  w,d,q=dense[q,int(head in ones)];(ones.add if w else ones.discard)(head);head+=1 if d else -1
 else:raise AssertionError('seed frame not reached in two million steps')
 assert steps==58154
 reached={0};todo=[0]
 while todo:
  q=todo.pop()
  for b in(0,1):
   n=dense[q,b][2]
   if n<len(labels)-1 and n not in reached:reached.add(n);todo.append(n)
 assert reached==set(range(len(labels)-1))
 receipt={'working_states':len(labels)-1,'alphabet':[0,1],'initial_state':0,'halting_state':len(labels)-1,'source_macro_tokens':len(selected),'source_sites':len(sites),'outside_ax_sites':len(unchanged),'max_source_path':max(len(p)for p,*_ in sites),'raw':rawcheck,'folded':check,'startup':{'steps':steps,'dense_state':q if False else labels.index(84),'native_state':84,'head':head,'site':25,'path':'100000','gap':48,'physical_registers':expected,'ones':sorted(ones)},'hashes':{name:hashlib.sha256((P/name).read_bytes()).hexdigest()for name in['candidate.tm','candidate.native.tm','Program.lean','grammar.json','selected-word.json','sites.json']}}
 (P/'checks.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
