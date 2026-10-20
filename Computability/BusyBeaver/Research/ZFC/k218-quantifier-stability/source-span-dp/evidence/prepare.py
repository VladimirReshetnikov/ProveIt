#!/usr/bin/env python3
"""Prepare an exact closed-macro interval DP, using only pinned pure utilities."""
from pathlib import Path
from functools import cache
import sys,json,itertools,hashlib,time
sys.dont_write_bytecode=True
import source_language as s
import build221 as b
import measure_pinned as m
P=Path(__file__).resolve().parent
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
seed=ROOT/'Computability/BusyBeaver/Research/ZFC/candidate-k218'
for name in ('source_language.py','build221.py'):
 assert m.sha((P/name).read_bytes())==m.PINS[name]
raw=(seed/'sites218.json').read_bytes();tab=(seed/'k218.native.tm').read_bytes()
assert m.sha(raw)=='b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9'
assert m.sha(tab)=='2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f'
tree=s.tree(json.loads(raw));table=b.read_table(tab);groups,_=b.decoder_map(table,tree);q=lambda k:b.sole(groups,k)
identity,im=m.compile_tree(s,b,table,tree,tree);assert identity==table and im['working_states']==218
macros={'a':q(98),'b':q(12),'c':q(166),'F':q(184)[0],'I':q(90),'Q':(q(90),(('CI',1),('CI',1)))}
assert all(s.boundary(t)==(0,0,False) for t in macros.values())
I=lambda x,y:('I',x,y);Q=lambda x,y:('Q',x,y);N=lambda x:I(x,'F')
forms=[I('a',I('b','a')),I(I('a',I('b','c')),I(I('a','b'),I('a','c'))),I(N(N(Q('a','b'))),Q('a','b'))]
def post(t):return post(t[1])+post(t[2])+t[0] if isinstance(t,tuple) else t
perms=list(itertools.permutations('abc'));recipes={}
for pp in itertools.product(perms,repeat=3):
 ws=[post(f).translate(str.maketrans('abc',''.join(p))) for f,p in zip(forms,pp)]
 for order in itertools.permutations(range(3)):
  w=''.join(ws[i] for i in order);assert w not in recipes
  recipes[w]={'permutations':pp,'order':order,'formula_postfix':[ws[i] for i in order]}
words=sorted(recipes);intervals={w[i:j] for w in words for i in range(len(w)) for j in range(i+1,len(w)+1)}
assert len(words)==1296 and len(intervals)==91002
nodes=[];ids={}
def intern(t):
 if t in ids:return ids[t]
 row={'leaf':list(t)} if s.leaf(t) else {'children':[intern(t[0]),intern(t[1])]}
 v=len(nodes);nodes.append(row);ids[t]=v;return v
intern(tree);old_count=len(nodes);old_trees=list(ids)
macro_ids={k:intern(t) for k,t in macros.items()}
HOLE=('HOLE',0);skeleton=m.splice(s,tree,135,486,HOLE)
base=set();context=[]
def fixed(t):
 v=ids[t];base.add(v)
 if not s.leaf(t):fixed(t[0]);fixed(t[1])
def mark(t):
 if t==HOLE:return True
 if s.leaf(t):fixed(t);return False
 left,right=mark(t[0]),mark(t[1]);assert not(left and right)
 if left:context.append([0,ids[t[1]]])
 elif right:context.append([1,ids[t[0]]])
 else:base.add(ids[t])
 return left or right
assert mark(skeleton)
# Both interval word and local guarded CFG must match before an old subtree is reused.
macro_flat={k:m.flat(t) for k,t in macros.items()};reused=[];rejected=[]
for old in old_trees:
 if s.boundary(old)!=(0,0,False):continue
 fl=m.flat(old)
 if len(fl)>1000:continue
 @cache
 def tile(i):
  if i==len(fl):return ('',)
  out=[]
  for k,f in macro_flat.items():
   if fl[i:i+len(f)]==f:
    out.extend(k+x for x in tile(i+len(f)) if len(x)<29)
  assert len(out)<100000,'Unexpected ambiguous macro tiling'
  return tuple(out)
 for w in tile(0):
  if w not in intervals:continue
  ref=m.serial([macros[k] for k in w]);assert m.flat(ref)==fl
  a=s.sites((old,('CH',None)));r=s.sites((ref,('CH',None)))
  ga=s.graph_arithmetic(a)[0];gr=s.graph_arithmetic(r)[0]
  assert ga==s.graph_intervals(a) and gr==s.graph_intervals(r)
  (reused if ga==gr else rejected).append({'word':w,'node':ids[old],'primitives':len(fl)})
for j,row in enumerate(nodes):row['base']=j in base
settings={'beam_per_leading_zero_run':2,'zero_limit':6,'seconds_cap':120}
header=f'{len(nodes)} {len(context)} {len(words)} {len(reused)} {len(base)} {old_count} 2 6 120\n'
lines=[header]
for row in nodes:
 l,r=row.get('children',[-1,-1]);lines.append(f'{l} {r} {int(row["base"])}\n')
lines.append(' '.join(str(macro_ids[k]) for k in 'abcFIQ')+'\n')
lines.extend(f'{side} {sib}\n' for side,sib in context)
lines.extend(w+'\n' for w in words)
lines.extend(f'{r["word"]} {r["node"]}\n' for r in reused)
(P/'input.txt').write_text(''.join(lines))
record={'status':'EXACT_DP_INPUT_PREPARED','seed':str(seed),'seed_source_sha256':m.sha(raw),'seed_table_sha256':m.sha(tab),'helper_pins':{x:m.sha((P/x).read_bytes()) for x in ('source_language.py','build221.py','measure_pinned.py')},'identity_compiler_control':im,'baseline_metrics':s.metrics(tree),'nodes':nodes,'macro_ids':macro_ids,'context_bottom_up':context,'base_nodes':sorted(base),'old_node_count':old_count,'recipes':recipes,'distinct_intervals':len(intervals),'reused_old_closed_subtree_patterns':reused,'rejected_word_only_patterns':rejected,'replacement':[135,486],'AX_output_count':12,'settings':settings,'input_sha256':m.sha((P/'input.txt').read_bytes()),'scope':'No candidate or runtime claim. Whole replacement is a sequence of closed macros; exact literal formula postfixes retained.'}
(P/'input.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':record['status'],'nodes':len(nodes),'fixed_base':len(base),'context':context,'words':len(words),'intervals':len(intervals),'old_closed_reuses':len(reused),'rejected':len(rejected),'macro_sizes':{k:len(v) for k,v in macro_flat.items()},'identity':im}))
