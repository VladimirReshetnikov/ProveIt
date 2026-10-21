#!/usr/bin/env python3
"""Integer-DAG allocation sweep of globally renamed nine-register sources.
No tuple-tree hashing in the inner loop. Implements exactly the inherited
incremental compiler allocation; all candidates at <=220 states get full replay.
"""
import itertools,json,time,argparse
from collections import Counter
import inverse_mp as q
s,b,z=q.s,q.b,q.z
ap=argparse.ArgumentParser()
ap.add_argument('--source',type=q.Path)
ap.add_argument('--table',type=q.Path)
ap.add_argument('--name',default='global_register_permutations')
ap.add_argument('--restricted-seed',action='store_true')
ap.add_argument('--allow-old-duplicates',action='store_true')
ap.add_argument('--all-registers',action='store_true')
ap.add_argument('--extend-direct',action='store_true',help='Exploratory opposite-PC-bit CI/CD entries; requires runtime proof')
args=ap.parse_args()
if args.source:
 q.ROWS=json.loads(args.source.read_text());q.TREE=s.tree(q.ROWS)
if args.table:q.T=b.read_table(args.table.read_bytes())
if args.allow_old_duplicates or args.extend_direct:
 import recompile219 as selected_compiler
else:selected_compiler=z
OUT=q.W/args.name;OUT.mkdir(exist_ok=True)
basegroups,_=b.decoder_map(q.T,q.TREE)
ids={};nodes=[];oldpairs={};leafs={}
def intern(n):
 if n in ids:return ids[n]
 if s.leaf(n):
  i=len(nodes);nodes.append(n);leafs[i]=n
 else:
  aa,bb=intern(n[0]),intern(n[1]);i=len(nodes);nodes.append((aa,bb));oldpairs[aa,bb]=i
 ids[n]=i;return i
ROOT=intern(q.TREE);N=len(nodes)
NODES=[i for i in range(N)if i not in leafs]
groups={k:{ids[n]for n in ns}for k,ns in basegroups.items()}
node_state={n:k for k,ns in groups.items()for n in ns}
leaf_id={v:k for k,v in leafs.items()}
leaf_actions={}
for l,ch in leafs.items():
 for bit in(0,1):
  choices=Counter(q.T[k,bit]for n,k in node_state.items()if nodes[n][bit]==l)
  direct=[a for a in choices if a[:2]==(bit,1)]
  if len(direct)==1:leaf_actions[l,bit]=direct[0]
  elif ch==('CC',1)and bit==1:leaf_actions[l,bit]=(0,-1,1)
  elif ch==('CC',2)and bit==1:leaf_actions[l,bit]=(0,-1,16)
  elif ch==('CB',1)and bit==1:leaf_actions[l,bit]=(0,-1,40)
if args.extend_direct:
 for l,ch in leafs.items():
  if ch[0]not in ('CI','CD'):continue
  for bit in (0,1):
   other=leaf_actions.get((l,1-bit))
   if (l,bit)not in leaf_actions and other is not None and other[:2]==(1-bit,1):
    leaf_actions[l,bit]=(bit,1,other[2])


def fast(perm):
 ren=[None]*N;newpairs={}
 for i in range(N):
  if i in leafs:
   op,arg=leafs[i];ren[i]=leaf_id[op,perm[arg]]if op in('CI','CD')else i
  else:
   aa,bb=nodes[i];children=ren[aa],ren[bb]
   ni=oldpairs.get(children,N+i);ren[i]=ni;newpairs[ni]=children
 live={ren[i]for i in NODES}
 origins={ren[i]:i for i in NODES if i!=ren[i]and i not in live}
 table=dict(q.T);mapped=dict(node_state);mapped[ren[ROOT]]=84;claimed={84:ren[ROOT]};firstfresh=max(300,max(k for k,bit in table)+1);fresh=firstfresh;reused=0
 def go(ni):
  nonlocal fresh,reused
  if ni in mapped:return mapped[ni]
  oi=origins.get(ni)
  if oi is not None and len(groups[node_state[oi]])==1 and node_state[oi]not in claimed:
   k=node_state[oi];reused+=1
  else:k=fresh;fresh+=1
  mapped[ni]=k;claimed[k]=ni
  for bit,ch in enumerate(newpairs[ni]):
   if ch not in leafs:table[k,bit]=(bit,1,go(ch))
   elif oi is not None and nodes[oi][bit]==ch:table[k,bit]=q.T[node_state[oi],bit]
   elif(ch,bit)in leaf_actions:table[k,bit]=leaf_actions[ch,bit]
   else:raise ValueError(('no leaf action',leafs[ch],bit))
  return k
 for bit,ch in enumerate(newpairs[ren[ROOT]]):table[84,bit]=(bit,1,go(ch))if ch not in leafs else leaf_actions[ch,bit]
 todo=[0];reach={0}
 for k in todo:
  for bit in(0,1):
   dest=table[k,bit][2]
   if dest!=254 and dest not in reach:reach.add(dest);todo.append(dest)
 table={key:v for key,v in table.items()if key[0]in reach}
 def maketree():
  memo={}
  def make(n):
   if n in memo:return memo[n]
   if n in leafs:v=leafs[n]
   else:a,bb=newpairs[n];v=make(a),make(bb)
   memo[n]=v;return v
  return make(ren[ROOT])
 return len(table)//2,table,maketree,dict(fresh=fresh-firstfresh,reused=reused)


def initial_logical_seed(perm):
 return [3 if perm[i]in(0,4)else 0 for i in range(9)]

def safe_seed(perm):
 seed=initial_logical_seed(perm)
 return all(seed[j]==0 for j in(3,6,7))


def main():
 st=time.time();hist=Counter();rows=[];errors=Counter();qualified=0;best=999
 # The only primitive that can occur as a right child and carries a register
 # argument is CI1. The supplied leaf-entry library has no CI r /read1 for r!=1.
 # Every skipped permutation is therefore known to fail the same compiler.
 skipped_unavailable=0;skipped_seed=0
 permutations=itertools.permutations(range(9))if args.all_registers else (list(pp[:1])+[1]+list(pp[1:])for pp in itertools.permutations((0,2,3,4,5,6,7,8)))
 for pp in permutations:
  perm=list(pp)
  if args.restricted_seed and not safe_seed(perm):skipped_seed+=1;continue
  row={'permutation':perm,'initial_logical_seed':initial_logical_seed(perm)}
  try:
   n,U,maker,meta=fast(perm);hist[n]+=1;row['working_states']=n;row.update(meta)
   if n<best:best=n;print('best',best,perm,flush=True)
   if n<=220:
    tree=maker()
    try:
     if args.extend_direct:V,vmeta=selected_compiler.compile_tree(q.T,q.TREE,tree,extend_direct=True)
     else:V,vmeta=selected_compiler.compile_tree(q.T,q.TREE,tree)
     assert V==U
     row['checked_compiler']=vmeta;qualified+=1
     d=OUT/('p'+''.join(map(str,perm)));d.mkdir(exist_ok=True)
     (d/'sites.json').write_bytes(s.compact(s.sites(tree)));(d/'candidate.tm').write_bytes(b.table_bytes(U));(d/'receipt.json').write_text(json.dumps(row,indent=2)+'\n')
     print('QUALIFY',json.dumps(row),flush=True)
    except Exception as exc:row['binding_error']=repr(exc)
  except Exception as exc:e=repr(exc);errors[e]+=1;row['error']=e
  rows.append(row)
  if len(rows)%2000==0:print('progress',len(rows),'elapsed',round(time.time()-st,2),'hist',dict(hist),flush=True)
 out={'tested_permutations':len(rows),'restricted_seed':args.restricted_seed,'all_registers':args.all_registers,'exploratory_direct_CI_CD_entries':args.extend_direct,'source':str(args.source)if args.source else 'baseline220','table':str(args.table)if args.table else 'baseline220','skipped_fixedtop_bootunsafe':skipped_seed,'outside_fixedtop_scope':0 if args.all_registers else 322560,'qualifying_tables':qualified,'minimum_unchecked_compiler_states':best,'elapsed_seconds':time.time()-st,'working_state_histogram':dict(hist),'errors':dict(errors),'results':rows}
 (OUT/'summary.json').write_text(json.dumps(out,indent=2)+'\n');print('finished',len(rows),'seconds',out['elapsed_seconds'],'best',best,flush=True)

if __name__=='__main__':main()
