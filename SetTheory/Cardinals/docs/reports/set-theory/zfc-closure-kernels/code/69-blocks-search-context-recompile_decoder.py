"""Experimental contextual decoder emitter with explicit optional controls.
Freshly replays every guarded leaf using the fixed universal affine macro
contracts. No source-equivalence or blank-bootstrap claim is inferred here.
"""
from search_common import *
from functools import lru_cache
import hashlib,argparse
OLD=json.loads((Path(__file__).resolve().parent/'decoder_entries.json').read_text())
NODES={int(k):tuple(map(tuple,v)) for k,v in OLD['nodes'].items()};ROOT=OLD['root']
OLD_FP={v:int(n) for n,v in OLD['fingerprints'].items()}
MACRO={2,4,6,20,48,63,73,75,83,95,109,112,131,255,60,44,31,56,38,40,28,64,69}
PAIRS={(str(q),b) for q in MACRO for b in (0,1)}-{('6',0),('20',0),('48',0),('69',1)}
CONTROL={}
for n,pair in NODES.items():
 for bit,e in enumerate(pair):
  if e[0] not in 'BC':continue
  counts=CONTROL.setdefault((e,bit),Counter())
  for state,weight in OLD['state_entries'][str(n)].items():counts[T[state,bit]]+=weight

def emit(nodes,root,generic=False):
 @lru_cache(None)
 def fingerprint(edge):
  text='N('+','.join(fingerprint(e) for e in nodes[edge[1]])+')' if edge[0]=='N' else ':'.join(map(str,edge))
  return hashlib.sha256(text.encode()).hexdigest()
 U=T.copy();entry={};fresh=256;metadata={}
 def allocate():
  nonlocal fresh
  q=str(fresh);fresh+=1;return q
 for n in nodes:
  f=fingerprint(('N',n))
  if n==root:entry[n]='96'
  elif f in OLD_FP:entry[n]=max(OLD['state_entries'][str(OLD_FP[f])],key=OLD['state_entries'][str(OLD_FP[f])].get)
  else:entry[n]=allocate()
 C={0:'4'};BR={0:'7'}
 def control(op,k):
  cache=C if op=='C' else BR
  if k not in cache:
   prev=control(op,k-1);q=allocate();cache[k]=q
   U[q,0]=(0,'L',q if op=='C' else prev)
   U[q,1]=(0,'L',prev if op=='C' else q)
  return cache[k]
 def transition(e,bit):
  if e[0]=='N':return bit,'R',entry[e[1]]
  if e[0] in 'BC':
   if generic:
    op,k=e
    if op=='B' and bit==0 and k==0:return (1,'R','10')
    return (0,'L',control(op,k-int(bit==(0 if op=='B' else 1))))
   if e[0]=='B' and e[1]==1:return 0,'L','7' if bit==0 else '33'
   return CONTROL[e,bit].most_common(1)[0][0]
  return bit,'R',max(OLD['leaf_entries'][':'.join(map(str,e))],key=OLD['leaf_entries'][':'.join(map(str,e))].get)
 for n in nodes:
  if entry[n]=='96' or fingerprint(('N',n)) not in OLD_FP:
   for bit,e in enumerate(nodes[n]):
    U[entry[n],bit]=transition(e,bit);metadata[entry[n],bit]=e
 return U,metadata,entry

def get_sites(nodes,root):
 out=[];todo=[(('N',root),'')]
 while todo:
  e,p=todo.pop();op=e[0]
  if op=='N':todo.extend((nodes[e[1]][b],p+str(b)) for b in (1,0))
  else:out.append((p,'C'+op,None if op=='H' else audit.PHYSICAL[e[1]] if op in 'ID' else e[1]))
 return out

def make_cases(sites):
 out=[]
 for p,op,r in sites:
  for zero in ((True,False) if op=='CD' else (None,)):
   branch=(r,zero) if op=='CD' else None
   extra,effect,overflow=0,None,False
   if op=='CI': successor,overflow=audit.full_inc(p);effect=('inc',r)
   elif op=='CD' and not zero: successor,overflow=audit.full_inc(p);effect,extra=('dec',r),1
   elif op=='CD': successor,overflow=audit.full_inc(audit.full_strip(p,'0',1))
   elif op=='CB': successor,overflow=audit.full_inc(audit.full_strip(p,'0',r))
   elif op=='CC': successor=audit.full_strip(p,'1',r)
   else: successor=''
   gap=40+extra+int(overflow)-len(successor)
   target=A.canon([('b',1)],[('b',int(b)) for b in successor]+[('r',0,1,gap),('b',1),('box',('plain',effect))])
   out.append((p,branch,target,op=='CH'))
 return out
class Track(dict):
 def __getitem__(self,e):self.used.add(e);return super().__getitem__(e)

def evaluate(nodes,root,generic=False,short=False):
 U,meta,entry=emit(nodes,root,generic=generic)
 if short:U['58',0]=(0,'L','84')
 table=Track(U);table.used=set();C=make_cases(get_sites(nodes,root));failures=[]
 for i,(p,branch,target,halt) in enumerate(C):
  before=table.used.copy()
  try:A.run(table,p,branch,target,halt=halt,fuel=1000)
  except Exception as ex:
   failures.append(dict(case=i,pc=p,branch=branch,message=str(ex),touched_new=[(e,meta[e]) for e in table.used-before if e in meta]))
 if not failures:
  retained={q for q,b in table.used|PAIRS}
  size=len(retained)
 else:size=None
 return dict(cases=len(C),failures=failures,states=size,emitted_states=len(U)//2,decoder_nodes=len(nodes),generic_controls=generic,short_dispatch=short),U

def read_input(path):
 x=json.loads(Path(path).read_text())
 if 'short_zero_layouts' in x:x=x['short_zero_layouts'][0]
 return {int(n):tuple(map(tuple,p)) for n,p in x['nodes'].items()},x['root']
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('input',nargs='?');ap.add_argument('--generic',action='store_true');ap.add_argument('--short',action='store_true');ap.add_argument('--output',default='recompile-results.json');a=ap.parse_args()
 nodes,root=read_input(a.input) if a.input else (NODES,ROOT)
 result,U=evaluate(nodes,root,a.generic,a.short)
 Path(a.output).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v if k!='failures' else v[:3] for k,v in result.items()},indent=2));print('FAILURE COUNT',len(result['failures']))
