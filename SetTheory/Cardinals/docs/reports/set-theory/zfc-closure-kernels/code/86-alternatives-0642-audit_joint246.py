#!/usr/bin/env python3
"""Independent composition audit. Reads candidates; writes only verification/.
Ordinary reviewed symbolic certificates, not a proof-assistant kernel run.
"""
from pathlib import Path
import hashlib, importlib.util, json, re, sys, time
if not __debug__: raise SystemExit('Assertions must be enabled')
ROOT = Path(__file__).resolve().parents[1]
P = ROOT/'context_folds/recovered/67/research'
B = P/'sources/context246/zfc-context246'
O = Path(__file__).resolve().parent
sys.path.insert(0, str(P/'agent_logic'))
import verify_rotated246 as v
sys.path.insert(0, str(B/'code'))
paths = {'joint':ROOT/'joint_controls/joint246_old.tm', 'baseline': B/'machine/zfc_prefix246_old.tm',
 'rotated':P/'agent_state/rebracket/unshared246.tm',
 'detector':ROOT/'context_folds/recovered/64/experiments/decoder/detector8-context246.tm',
 'source':P/'root_search/rebracket202_minimal.json',
 'original':P/'sources/beyond252/beyond252/exploratory/data/original203.json',
 'literal':B/'sources/Prog254.v', 'macro':B/'code/check_macro_inductions.py',
 'affine':B/'sources/prior/prefix_affine.py', 'checker':Path(v.__file__),
 'source_checker':P/'agent_logic/verify_reassociation.py', 'rebuild':B/'code/rebuild_machines.py'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before={k:sha(p) for k,p in paths.items()}
for k in ('baseline','source','macro','affine'): assert before[k]==v.EXPECTED[k],k
assert before['rotated']==v.EXPECTED['candidate']
assert before['rebuild']==v.EXPECTED['rebuild_dependency']
assert before['literal']=='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
assert before['detector']=='2e4c60cf14947c9ebb8e4bf999f9cd0ac995d09d16bb8b84e5c2fba922f79b1b'
assert before['joint']=='29377d9d8abc876187cb3fdac430f9dc92999802a848c0c2403874763214951f'
base,start,halt=v.read_tm(paths['baseline']); table,js,jh=v.read_tm(paths['joint'])
rot,rs,rh=v.read_tm(paths['rotated']); det,ds,dh=v.read_tm(paths['detector'])
assert js==rs==ds==start==95 and jh==rh==dh==halt==254
assert set(base)==set(table)==set(rot)==set(det) and len(table)==492
rd={k:a for k,a in rot.items() if base[k]!=a}; dd={k:a for k,a in det.items() if base[k]!=a}
assert len(rd)==6 and len(dd)==8 and not(rd.keys()&dd.keys())
assert table==base|rd|dd
assert sum(a[2]==halt for a in table.values())==1 and table[77,1]==(1,'R',254)
# Independently implement full source parsing and exact RegisterPath arithmetic.
def json_nodes(p):
 d=json.loads(p.read_text());return {int(k):tuple(tuple(x) for x in z) for k,z in d['nodes'].items()},d['root']
def literal_nodes(p):
 body=p.read_text().split('Definition p254_tab',1)[1].split(':= [',1)[1].split('].',1)[0]
 pat=re.compile(r'\((CN|CI|CD|CB|CC|CH)(?: (\d+))?,\s*(CN|CI|CD|CB|CC|CH)(?: (\d+))?\)')
 edge=lambda op,n:(op[1],int(n)) if n else (op[1],)
 result=[(edge(a,b),edge(c,d)) for a,b,c,d in pat.findall(body)]
 assert len(result)==6459 and not re.sub(r'[\s;]','',pat.sub('',body))
 return dict(enumerate(result)),0
def expand(nodes,root):
 leaves=[];reached=set()
 def go(edge,path,anc):
  if edge[0]=='N':
   i=edge[1]; assert i not in anc and i in nodes and len(nodes[i])==2
   reached.add(i)
   return ('N',*(go(e,path+(b,),anc|{i}) for b,e in enumerate(nodes[i])))
  assert edge[0] in 'IDBCH' and len(edge)==(1 if edge[0]=='H' else 2)
  if edge[0] in 'ID': assert 0<=edge[1]<9
  if len(edge)==2: assert edge[1]>=0
  leaves.append((path,edge));return edge
 tree=go(('N',root),(),set());assert reached==set(nodes)
 return tree,leaves

def inc(path):
 result=list(path)
 for k in range(len(result)-1,-1,-1):
  result[k]=1-result[k]
  if result[k]:break
 return tuple(result)
def strip(path,bit,n):
 result=list(path)
 while n and result:
  if result.pop()==bit:n-=1
 return tuple(result)
def graph(nodes,root,leaves):
 lookup={p:i for i,(p,e) in enumerate(leaves)}
 def follow(path):
  e=('N',root);q=[]
  while e[0]=='N':
   b=path[len(q)] if len(q)<len(path) else 0;q.append(b);e=nodes[e[1]][b]
  return lookup[tuple(q)]
 result=[]
 for path,e in leaves:
  op=e[0]
  if op=='I': nexts=[inc(path)]
  elif op=='D':nexts=[inc(path),inc(strip(path,0,1))]
  elif op=='B':nexts=[inc(strip(path,0,e[1]))]
  elif op=='C':nexts=[strip(path,1,e[1])]
  else:nexts=[]
  result.append((e,tuple(follow(p) for p in nexts)))
 return result,follow(())
ln,lr=literal_nodes(paths['literal']);on,orr=json_nodes(paths['original']);sn,sr=json_nodes(paths['source'])
lt,ll=expand(ln,lr);ot,ol=expand(on,orr);st,sl=expand(sn,sr)
assert ot==lt
lg,li=graph(ln,lr,ll);og,oi=graph(on,orr,ol);sg,si=graph(sn,sr,sl)
assert lg==og==sg and li==oi==si==0
assert len(sl)==6460 and len(sn)==202
source=v.Decoder(sn,sr)
assert source.sites==[(''.join(map(str,p)),e) for p,e in sl]
# Existing universal box proofs replayed on the actual composed table.
macro=v.load_module(paths['macro'],'independent_joint_macro')
bp,bs=v.replay_inductions(macro,base);jp,jsupport=v.replay_inductions(macro,table)
assert bp==jp and bs==jsupport and len(bs)==42
assert all(base[k]==table[k] for k in bs)
aff=v.load_module(paths['affine'],'independent_joint_affine')
oracles=v.check_oracle(aff)
inst,used=v.check_instructions(aff,table,source)
assert used|bs==set(table)
# New sparse semantics, separate from the supplied dense bootstrap interpreter.
q,h,ones=start,0,set();steps=409449
for t in range(steps):
 assert q!=halt
 b=int(h in ones);w,d,nxt=table[q,b]
 if w:ones.add(h)
 else:ones.discard(h)
 h+=1 if d=='R' else -1;q=nxt
expected={-6,176};pos=177
for value in [0,0,0,3,0,0,3,0,0]+[1]*167:
 expected.update(range(pos+1,pos+value+2));pos+=value+2
assert q==96 and h==-5 and pos==702 and ones==expected and len(ones)==351
assert before=={k:sha(p) for k,p in paths.items()}
result={'status':'PASS','table_sha256':before['joint'],'working_states':246,
 'disjoint_changed_rows':14,'source_graph_equivalent_to_entire_literal_program':True,
 'source_equivalence_method':'Independent full literal parser, DFS leaves, exact list path increment/strip, every guarded successor, empty-root leaf.',
 'source_leaves':len(sl),'source_nodes':len(sn),'macro_theorems_identical':True,
 'protected_macro_pairs':len(bs),'oracle_positive_and_negative_checks':oracles,
 'instructions':inst,'complete_literal_or_macro_row_support':True,
 'independent_sparse_bootstrap':{'steps':steps,'state':q,'head':h,'one_count':len(ones),'whole_tape_support':sorted(ones)},
 'all_inputs_unchanged':True,'input_hashes':before,
 'conclusion':'Ordinary mathematical composition passes. Neither fewer than246 nor a fresh Lean kernel proof is claimed.'}
(O/'joint246_independent_audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:z for k,z in result.items() if k not in ('input_hashes','independent_sparse_bootstrap','instructions')},indent=2))
