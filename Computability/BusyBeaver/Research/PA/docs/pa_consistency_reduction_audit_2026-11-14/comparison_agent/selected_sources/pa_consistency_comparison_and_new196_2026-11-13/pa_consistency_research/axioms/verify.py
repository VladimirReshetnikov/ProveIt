"""Rebuild exact tables; audit source binding, emission, runtime and startup.

Python standard library only. The symbolic executor calls the unchanged
register-block interfaces described in reference/M6/Runtime.lean. This
executable certificate is not a new Lean-kernel theorem.
"""
import json,hashlib
from pathlib import Path
import compiler as c
from verify_emitter import audit,require,literal_blocks,word
P=Path(__file__).resolve().parent

def table(path):
 out={}
 for line in path.read_text().splitlines():
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n));require((q,b)not in out,'duplicate row');require(b in(0,1)and w in(0,1)and d in('L','R'),'binary row');out[q,b]=(w,d=='R',n)
 return out

def source_binding(t,sites,ins):
 oldsites,oldins=c.program();oldblocks=literal_blocks();expected={}
 for op,a,b in oldblocks:
  expected.setdefault(op,(a,b))
 oldpaths={p:i for i,(p,op,arg)in enumerate(oldsites)};newpaths={p:i for i,(p,op,arg)in enumerate(sites)}
 prefix=(1,0,1,0,1,0,0,1)
 oldout=[s for s in oldsites if s[0][:8]!=prefix];newout=[s for s in sites if s[0][:8]!=prefix]
 require(oldout==newout,'exact unchanged exterior paths and operations');require(len(oldout)==169,'exterior count')
 def norm(code,start,end,ss):
  k=code[0]
  if k=='halt':return code
  narg=1 if k=='jump' else 2
  def dest(j):
   if start<=j<end:return('internal',j-start)
   if j==end:return('next',)
   return('external',ss[j][0])
  return tuple(code[:narg])+tuple(dest(j)for j in code[narg:])
 # Every macro is the same complete primitive/control block as upstream.
 cursor=50
 for op in word(t):
  a,b=expected[op];length=b-a
  for off in range(length):
   require(sites[cursor+off][1:]==oldsites[a+off][1:],'macro primitive identity')
   require(norm(ins[cursor+off],cursor,cursor+length,sites)==norm(oldins[a+off],a,b,oldsites),'macro relative control-flow identity')
  cursor+=length
 require(cursor-50==len(sites)-169,'all AX primitive sites bound')
 # Exterior targets can enter AX; compare their path names after re-association
 # only when both target sites lie outside AX. Entries into AX are its first site.
 for p,op,arg in newout:
  ni,oi=newpaths[p],oldpaths[p];nc,oc=ins[ni],oldins[oi];require(nc[:2] == oc[:2] if op in('inc','dec') else nc[:1]==oc[:1],'exterior opcode')
  narg=1 if nc[0]=='jump' else 2
  if nc[0]=='halt':continue
  for nn,oo in zip(nc[narg:],oc[narg:]):
   if oldsites[oo][0][:8]==prefix:require(oo==50 and nn==50,'AX entry binding')
   else:require(sites[nn][0]==oldsites[oo][0],'exterior successor binding')
 return {'macro_blocks':len(word(t)),'exterior_sites':169,'relative_control_flow_exact':True}

def check(name):
 p=P/name;t=c.read_grammar(p/'grammar.json');raw,index,shape=c.build(t);folds=json.loads((p/'folds.json').read_text());alias={a:b for a,b,acts in folds};actions={b:acts for a,b,acts in folds}
 require(len({q for a,b,acts in folds for q in(a,b)})==2*len(folds),'disjoint state folds')
 folded={}
 for(q,b),act in raw.items():
  if q in alias:continue
  w,d,n=actions[q][b]if q in actions else act;folded[q,b]=(w,d,alias.get(n,n))
 require(folded==table(p/'machine.native.tm'),'exact regenerated native table')
 labels=json.loads((p/'labels.json').read_text());dense=table(p/'machine.tm');require(labels[0]==74 and labels[-1]==254,'start/halt map');require(len(set(labels))==len(labels),'injective state renaming')
 require({(labels[q],b):(w,d,labels[n])for(q,b),(w,d,n)in dense.items()}==folded,'exact dense relabeling')
 count=len(labels)-1;require(count==196,'working-state count');require(set(dense)=={(q,b)for q in range(count)for b in(0,1)},'total binary table')
 old,_=c.machine();require(all(folded[q,b]==old[q,b]for q in c.BOXSTATES for b in(0,1)),'unchanged register engine')
 sites,ins,cs=c.source(t);binding=source_binding(t,sites,ins);emission=audit(name)
 rawcheck=c.validate(raw,cs);require(rawcheck['ok'],'raw universal symbolic contracts')
 check=c.validate(folded,cs);require(check['ok'],'folded universal symbolic contracts')
 emitted=[{'ordinal':i,'path':''.join(map(str,p)),'op':op,'arg':arg,'instruction':list(ins[i])}for i,(p,op,arg)in enumerate(sites)]
 require(emitted==json.loads((p/'sites.json').read_text()),'all supplied source sites')
 q=0;head=0;ones=set()
 for _ in range(58154):
  w,d,q=dense[q,int(head in ones)];(ones.add if w else ones.discard)(head);head+=1 if d else-1
 expected=[0,0,0,0,0,0,2,0,0]+[1]*26;target={head-1,head};pos=head+48;target.add(pos);pos+=1
 for v in expected:pos+=1;target.update(range(pos,pos+v+1));pos+=v+1
 require((labels[q],head)==(84,-2)and ones==target,'exact complete startup tape')
 reached={0};todo=[0]
 while todo:
  qq=todo.pop()
  for b in(0,1):
   n=dense[qq,b][2]
   if n<count and n not in reached:reached.add(n);todo.append(n)
 require(reached==set(range(count)),'all states graph-reachable')
 return {'working_states':count,'rows':len(dense),'grammar_nodes':len(shape),'simultaneous_folds':len(folds),'source_sites':len(sites),'emission':emission,'source_binding':binding,'raw_contracts':rawcheck,'folded_contracts':check,'startup_steps':58154,'complete_startup_tape_exact':True,'graph_reachable_states':len(reached),'machine_sha256':hashlib.sha256((p/'machine.tm').read_bytes()).hexdigest(),'kernel_checked':False}
if __name__=='__main__':
 if not __debug__:raise SystemExit('Run without Python -O: upstream parser assertions are required.')
 receipts={}
 for name in('diagonal196','separate196'):
  receipts[name]=check(name);print(name,json.dumps(receipts[name],sort_keys=True),flush=True)
 (P/'reproduced_checks.json').write_text(json.dumps(receipts,indent=2)+'\n')
