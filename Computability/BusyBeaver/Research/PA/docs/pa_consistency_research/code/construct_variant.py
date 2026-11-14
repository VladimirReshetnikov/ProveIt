from pathlib import Path
import json,sys,re,collections
import grammar as g
ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'code/runtime'
sys.path.insert(0,str(BASE));import source_language as s,build221 as b
out=ROOT/'data'
products=ROOT/'rebuild';products.mkdir(exist_ok=True)
def tup(t):return tuple(map(tup,t)) if isinstance(t,list) else t
ax=tup(json.loads((out/'variant196_AX.json').read_text()));folds=tup(json.loads((out/'variant196_folds.json').read_text()));whole=g.subst(g.nodes['trie'],g.nodes['x67'],ax)
def conv(t):
 if isinstance(t,tuple):return tuple(map(conv,t))
 m=re.fullmatch(r'(inc|dec|continueTo|breakTo|halt)(\d*)',t);return {'inc':'CI','dec':'CD','continueTo':'CC','breakTo':'CB','halt':'CH'}[m[1]],int(m[2]) if m[2] else None
oldtable=b.read_table((ROOT/'data/pa196.native.tm').read_bytes());groups,_=b.decoder_map(oldtable,conv(g.nodes['trie']))
oldstates=collections.defaultdict(set)
for q,ns in groups.items():
 for n in ns:oldstates[n].add(q)
state={};changing=set();outer_original={}
def outer(old,new):
 if old==g.nodes['x67']:return
 if isinstance(old,tuple):
  state[new]=min(oldstates[conv(old)])
  if old!=new:changing.add(new);outer_original[new]=old
  outer(old[0],new[0]);outer(old[1],new[1])
outer(g.nodes['trie'],whole)
for t in set().union(*(g.internal(t) for t in g.atoms)):
 state[t]=min(oldstates[conv(t)])
# Macrointernal sharedreader has one specialalternate context. Defaultmin mirrored oldtable's decodermapping.
rep={m:n for n,m,bit,h in folds}
def representative(n):return rep.get(n,n)
newnodes=g.internal(whole)-set(state)
free=sorted(q for q in {q for q,_ in oldtable} if q>=1300 and q not in state.values())
newrep={representative(n) for n in newnodes};assert len(newrep)<=len(free),(len(newrep),len(free))
# deterministic order by firstsourceprefix
order=[]
def preorder(t):
 if isinstance(t,tuple):
  if t in newnodes and representative(t) not in order:order.append(representative(t))
  preorder(t[0]);preorder(t[1])
preorder(whole)
for n,q in zip(order,free):state[n]=q
for n in newnodes:state[n]=state[representative(n)]
leafacts=collections.defaultdict(collections.Counter)
for q,ns in groups.items():
 for n in ns:
  for bit,ch in enumerate(n):
   if s.leaf(ch):leafacts[ch,bit][oldtable[q,bit]]+=1
defaults={}
for key,acts in leafacts.items():
 pure=[a for a in acts if a[:2]==(key[1],1)];defaults[key]=max(pure or acts,key=lambda a:acts[a])
table={k:v for k,v in oldtable.items() if k[0]<1300}
# preservealloldrows exceptchangingouter; newreaders canonical
for n in newnodes:
 q=state[n]
 for bit,ch in enumerate(n):
  table[q,bit]=(bit,1,state[ch]) if isinstance(ch,tuple) else defaults[conv(ch),bit]
# Preserve indirect arithmetic rows on unchanged outer branches.
for n in changing:
 q=state[n];old=outer_original[n]
 for bit,ch in enumerate(n):
  if old[bit]==ch:continue
  if isinstance(ch,tuple):
   w,d,z=oldtable[q,bit]
   if (w,d)==(bit,1):table[q,bit]=(w,d,state[ch])
   elif state[ch] != min(oldstates[conv(old[bit])]):raise ValueError(('Indirect changed branch',q,bit))
# Someunchangedouter/macrostate>=1300?retainifneeded
for q in state.values():
 if(q,0)not in table:
  table[q,0]=oldtable[q,0];table[q,1]=oldtable[q,1]
for n,m,bit,h in folds:table[state[n],bit]=(bit,-1,state[h])
reach={74};todo=[74]
for q in todo:
 for bit in(0,1):
  nxt=table[q,bit][2]
  if nxt!=254 and nxt not in reach:reach.add(nxt);todo.append(nxt)
table={k:v for k,v in table.items() if k[0] in reach}
print('REJECTED_PREDECESSOR_TABLE',len(table)//2,'newnodes',len(newnodes),'newrep',len(newrep),'free',len(free),'changedouter',len(changing))
# Check every sourceprefix before finalprimitiveleaf row.
failures=[];maps={}
def visit(t,p=''):
 if not isinstance(t,tuple):return
 before={-1:1,**{i:int(x) for i,x in enumerate(p)}};tape=dict(before);head=0;q=84
 for step in range(1000):
  if head==len(p):break
  if head not in tape or (q,tape[head])not in table:break
  w,d,q=table[q,tape[head]];tape[head]=w;head+=d
 if (q!=state[t] and q not in oldstates[conv(t)]) or head!=len(p) or tape!=before:failures.append([p,q,state[t],head])
 maps[p]=q
 visit(t[0],p+'0');visit(t[1],p+'1')
visit(whole)
assert not failures,failures
print('PREFIX_REPRESENTATION_PASS',len(maps),'including inherited equivalent controls13/108')

# The nominal195 predecessor is rejected by its return scanner. Apply the
# eighth-zero repair and require byte-for-byte identity of the validated file.
import hashlib
assert len(table)==390
table[34,0]=(0,-1,2000);table[2000,0]=(0,-1,75);table[2000,1]=(1,-1,2)
rebuilt=b.table_bytes(table)
assert rebuilt==(ROOT/'data/variant196.native.tm').read_bytes()
assert s.compact(s.sites(conv(whole)))==(ROOT/'data/variant196_source.json').read_bytes()
(products/'variant196.native.tm').write_bytes(rebuilt)
print('EXACT_VARIANT196_RECONSTRUCTION_PASS',len(table)//2,hashlib.sha256(rebuilt).hexdigest())
