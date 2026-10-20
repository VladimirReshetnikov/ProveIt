#!/usr/bin/env python3
"""Independent K218 facts. Standard library; imports no construction/proof code."""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json

TABLE='4dd4ca3893a80b99a1df52e4a57f0357eeb697255f86f43b859a1a97ef511651'
SOURCE='1dcd14a47c4f100316c71f8a346b84000f3d12efc29123d1cce212d4bbfa2efe'
NATIVE='3c64cf321c9ca11153901cdb19e7326b8bfbd0d3c8d94357ead127a9c9b491c1'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def read(p):return json.loads(p.read_text())
def table(p):
 out={};starts=[]
 for line in p.read_text().splitlines():
  if line.startswith('#! start '):starts.append(int(line.split()[-1]));continue
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
  assert(q,b)not in out and b in(0,1)and w in(0,1)and d in('L','R')
  out[q,b]=(w,-1 if d=='L'else 1,z)
 assert starts==[0];return out

def encode(t):return ('#! start 0\n'+''.join(f'{q} {b} {w} {"L"if d==-1 else"R"} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))).encode()

def syntax(s):
 paths=[p for p,o,a in s];assert paths==sorted(paths)and len(set(paths))==len(paths)
 leaves=set(paths);interior={p[:j]for p in paths for j in range(len(p))};domain=leaves|interior
 assert not leaves&interior and all(set(p)<={'0','1'}for p in paths)
 assert all(p+'0'in domain and p+'1'in domain for p in interior)
 for p,o,a in s:
  assert o in('CI','CD','CB','CC','CH')
  assert a is None if o=='CH'else type(a)is int and(a>=1 if o in('CB','CC')else 0<=a<=8)
 nodes={p:(o,a)for p,o,a in s}
 for p in sorted(interior,key=len,reverse=True):nodes[p]=(nodes[p+'0'],nodes[p+'1'])
 return nodes,interior

def interval_cfg(s):
 spans={p[:j]:[len(s),-1]for p,o,a in s for j in range(len(p)+1)}
 for i,(p,o,a)in enumerate(s):
  for j in range(len(p)+1):v=spans[p[:j]];v[0]=min(v[0],i);v[1]=max(v[1],i+1)
 def jump(p,bit,n):
  ancestors=[p[:j]for j,b in enumerate(p)if b==bit]
  if len(ancestors)<n:return 0
  lo,hi=spans[ancestors[-n]];return hi%len(s)if bit=='0'else lo
 return [[]if o=='CH'else[jump(p,'0',1),(i+1)%len(s)]if o=='CD'else[jump(p,'0',a)]if o=='CB'else[jump(p,'1',a)]if o=='CC'else[(i+1)%len(s)]for i,(p,o,a)in enumerate(s)]

def arithmetic_cfg(s):
 # Second derivation: exact dyadic cut arithmetic rather than prefix intervals.
 depth=max(len(p)for p,o,a in s);width=1<<depth;cuts={};end=0
 for i,(p,o,a)in enumerate(s):
  start=int(p,2)<<(depth-len(p));assert start==end;cuts[start]=i;end=start+(1<<(depth-len(p)))
 assert end==width
 def ancestor(p,bit,n):
  count=0
  for j in range(len(p)-1,-1,-1):
   if p[j]==bit:
    count+=1
    if count==n:
     a=int(p[:j]or'0',2)<<(depth-j)
     if bit=='0':a+=1<<(depth-j)
     return cuts[a%width]
  return 0
 out=[]
 for i,(p,o,a)in enumerate(s):
  if o=='CH':v=[]
  elif o=='CD':v=[ancestor(p,'0',1),(i+1)%len(s)]
  elif o=='CB':v=[ancestor(p,'0',a)]
  elif o=='CC':v=[ancestor(p,'1',a)]
  else:v=[(i+1)%len(s)]
  out.append(v)
 return out

def rotate_tree(tree,roots):
 def walk(t,p):
  if p in roots:
   assert not isinstance(t[0],str)and not isinstance(t[0][0],str)
   (a,b),c=t;return(a,(b,c))
  return t if isinstance(t[0],str)else(walk(t[0],p+'0'),walk(t[1],p+'1'))
 return walk(tree,'')

def serialize_tree(t):
 out=[]
 def visit(t,p):
  if isinstance(t[0],str):out.append([p,*t])
  else:visit(t[0],p+'0');visit(t[1],p+'1')
 visit(t,'');return out

def patch_delta(a,b):
 return dict(removed=[[*k,*a[k]]for k in sorted(a.keys()-b.keys())],added=[[*k,*b[k]]for k in sorted(b.keys()-a.keys())],changed=[dict(row=list(k),before=list(a[k]),after=list(b[k]))for k in sorted(a.keys()&b.keys())if a[k]!=b[k]])

def prefix_proof(t,s,binding):
 nodes,interior=syntax(s);assert set(binding)==interior
 total=0;longest=0;receipt=[]
 for p in sorted(interior):
  initial=[int(b)for b in p];tape=initial[:];q=84;h=0;n=0
  while(q,h)!=(binding[p],len(p)):
   assert 0<=h<len(p),(p,q,h,'read outside fixed prefix')
   w,d,q=t[q,tape[h]];tape[h]=w;h+=d;n+=1;assert n<1000
  assert tape==initial;total+=n;longest=max(longest,n)
  receipt.append([p,binding[p],n])
 return dict(prefixes=len(receipt),literal_steps=total,maximum_steps=longest,arbitrary_exterior_untouched=True,entire_prefix_restored=True,entries=receipt)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[2]);ap.add_argument('--out',type=Path,default=Path(__file__).resolve().parent);a=ap.parse_args();r=a.root;a.out.mkdir(parents=True,exist_ok=True)
 dirs=[r/'research_sub219/intake/K219_Construction_2026-10-20/machine',r/'research_sub219/allocation/startup37_pinned182/compiled',r/'research_sub219/allocation/single188_role98/compiled',r/'research_sub219/allocation/single188_pure_normalized',r/'research_sub219/decoder/single188_reuse12',r/'research_sub219/decoder/targeted_reuse_chain/1',r/'research_sub219/decoder/reuse12_focused_bfs/candidate_4dd4ca3893a80b99']
 names=['original219','startup37_182','single188_reparse220','direct188_219','reuse12_219','reuse150_219','candidate218'];sources=[read(p/('sites219.json'if i==0 else'sites.json'))for i,p in enumerate(dirs)];tables=[table(p/('k219.native.tm'if i==0 else'candidate.tm'))for i,p in enumerate(dirs)]
 input_hashes={}
 for i,p in enumerate(dirs):
  for name in(['sites219.json','k219.native.tm']if i==0 else['sites.json','candidate.tm']):input_hashes[str((p/name).relative_to(r))]=sha(p/name)
 assert sha(dirs[-1]/'candidate.tm')==TABLE and sha(dirs[-1]/'sites.json')==SOURCE
 original=sources[0];oldcfg=interval_cfg(original);assert oldcfg==arithmetic_cfg(original);source_results=[]
 for name,s in zip(names,sources):
  nodes,internal=syntax(s);g=interval_cfg(s);assert g==arithmetic_cfg(s)==oldcfg
  assert len(s)==4744 and[x[1:]for x in s]==[x[1:]for x in original]
  unique=set(nodes.values());source_results.append(dict(stage=name,leaves=len(s),interior_occurrences=len(internal),unique_dag_nodes=len(unique),unique_dag_interiors=sum(not isinstance(t[0],str)for t in unique),maxdepth=max(map(len,nodes)),address_changes_from_original=sum(x[0]!=y[0]for x,y in zip(original,s)),ordered_primitive_arguments_identical=True,both_cfg_derivations_equal_original=True))
 assert source_results[-1]['unique_dag_nodes']==205 and source_results[-1]['unique_dag_interiors']==182
 assert sum(len(v)for v in oldcfg)==6166 and sum(o=='CH'for p,o,v in original)==1
 # Certified direct188 source rotations: recompute roots from old binding, and
 # transform nested trees rather than using the constructor's string rewrite.
 binding0=read(dirs[3]/'full_prefix_binding.json')['entry'];binding1=read(dirs[4]/'source_binding.json');binding2=read(dirs[6]/'source_binding.json')
 roots188={p for p,q in binding0.items()if q==188};roots96={p for p,q in binding1.items()if q==96};assert len(roots188)==5 and len(roots96)==4
 rotations=[]
 for src,dst,roots,bind,reuse in[(sources[3],sources[4],roots188,binding0,12),(sources[4],sources[5],roots96,binding1,150)]:
  nodes,_=syntax(src);new=rotate_tree(nodes[''],roots);assert serialize_tree(new)==dst
  for p in roots:
   (aa,bb),cc=nodes[p];assert any(nodes[x]==(bb,cc)for x,q in bind.items()if q==reuse)
  rotations.append(dict(roots=sorted(roots),reused_state=reuse,exact_tree_rotation=True,existing_pair_exactly_matches=True,no_primitive_or_control_retagging=True))
 assert sources[2]==sources[3]and sources[5]==sources[6]
 # All exact table operations after reparse220, independent of constructor.
 t=dict(tables[2]);t={k:v for k,v in t.items()if k[0]!=190};t[188,0]=(0,1,165);t[188,1]=(1,1,20);assert t==tables[3]
 t[188,0]=(0,1,166);t[188,1]=(1,1,12);assert t==tables[4]
 t[96,0]=(0,1,98);t[96,1]=(1,1,150);assert t==tables[5]
 assert[k for k,v in t.items()if v[2]==96]==[(177,1)]
 t={k:(w,d,85 if z==96 else z)for k,(w,d,z)in t.items()if k[0]!=96};t[85,0]=(0,1,98);t[85,1]=(1,-1,221);assert t==tables[6]
 transitions=[dict(before=names[i],after=names[i+1],**patch_delta(tables[i],tables[i+1]))for i in range(1,6)]
 states={q for q,b in t};assert len(states)==218 and len(t)==436 and set(t)=={(q,b)for q in states for b in(0,1)}
 assert{z for w,d,z in t.values()}-states=={254}and 254 not in states and 79 in states and not {96,190}&states
 # Native301/302 export is exactly a bijection, not an unqualified alias hash.
 nt=table(dirs[-1]/'candidate.native.tm');assert sha(dirs[-1]/'candidate.native.tm')==NATIVE
 rename={301:102,302:120};assert len({rename.get(q,q)for q,b in nt})==218
 assert{(rename.get(q,q),b):(w,d,rename.get(z,z))for(q,b),(w,d,z)in nt.items()}==t
 norm=read(dirs[-1]/'normalization.json');assert(norm['native_sha256'],norm['normalized_sha256'],norm['source_sha256'])==(NATIVE,TABLE,SOURCE)
 order=[0];mp={0:0}
 for q in order:
  for b in(0,1):
   z=t[q,b][2]
   if z!=254 and z not in mp:mp[z]=len(mp);order.append(z)
 assert set(mp)==states;mp[254]=218
 canonical={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in t.items()};(a.out/'k218.canonical.tm').write_bytes(encode(canonical))
 # Whole blank startup, with unrelated sparse-set and dense-bytearray storage.
 steps=312701;ones=set();q=h=0;counts=Counter()
 for _ in range(steps):
  b=int(h in ones);counts[q,b]+=1;w,d,q=t[q,b]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
 logical=[3,0,0,0,3,0,0,0,0];perm=(6,2,0,4,3,7,8,5,1);physical=[None]*9
 for i,j in enumerate(perm):physical[j]=logical[i]
 expected={-6,139};pos=140
 for value in physical+[1]*130:
  pos+=1;expected.update(range(pos,pos+value+1));pos+=value+1
 assert(q,h,ones)==(84,-5,expected)and len(ones)==277
 offset=steps+1;tape=bytearray(2*steps+3);q2=0;h2=offset;counts2=Counter()
 for _ in range(steps):
  b=tape[h2];counts2[q2,b]+=1;w,d,q2=canonical[q2,b];tape[h2]=w;h2+=d
 assert(q2,h2-offset,{i-offset for i,v in enumerate(tape)if v})==(mp[84],-5,expected)
 assert counts2==Counter({(mp[q],b):v for(q,b),v in counts.items()})
 startup=dict(steps=steps,state=84,head=-5,ones=sorted(ones),all_other_cells_zero=True,logical_registers=logical,physical_registers=physical,physical_permutation=list(perm),spares=[1]*130,extra_gap=80,two_distinct_interpreters_agree=True,row_counts=[[*k,v]for k,v in sorted(counts.items())]);dump(a.out/'whole_blank_startup.json',startup)
 prefix=prefix_proof(t,sources[-1],binding2);dump(a.out/'prefix_contracts.json',prefix)
 # Contextual fold85: input0 is one step to98; input1 consults previous bit.
 contexts={p for p,q in binding2.items()if q==85};old85={p for p,q in binding1.items()if q==85}
 assert contexts==old85|roots96 and len(contexts)==13 and len(old85)==9
 local=[]
 for previous,target,length in[(0,12,3),(1,150,5)]:
  cells={-1:previous,0:1};initial=dict(cells);q=85;head=0;trace=[]
  while(q,head)!=(target,1):
   assert head in cells;bit=cells[head];w,d,z=t[q,bit];trace.append([q,head,bit,w,d,z]);cells[head]=w;head+=d;q=z;assert len(trace)<10
  assert cells==initial and len(trace)==length
  relevant=sorted(p for p in contexts if p[-1]==str(previous));assert len(relevant)==(9 if previous==0 else 4)
  assert all(binding2[p+'0']==98 and binding2[p+'1']==target for p in relevant)
  local.append(dict(previous_bit=previous,target_state=target,duration=length,contexts=relevant,trace=trace,only_two_cells_read=True,arbitrary_exterior_untouched=True,tape_restored=True))
 receipt=dict(status='INDEPENDENT_K218_SMALL_FACTS_PASS',proof_scope='Independent literal table, two source CFG derivations, exact rotations/patches, complete prefix contracts, contextual-fold local proof and whole-blank startup. No candidate/proof module imported. Full generic unbounded runtime remains a separate obligation.',table_sha256=TABLE,native_sha256=NATIVE,source_sha256=SOURCE,canonical_sha256=sha(a.out/'k218.canonical.tm'),states=218,rows=436,all_working_states_graph_reachable=True,search_to_canonical=mp,source_stages=source_results,source_rotations=rotations,table_transformations=transitions,fold_contexts=local,guarded_successor_edges=6166,halt_cases=1,generic_cases_required=6167,source_all_natural_lockstep=True,source_entry_condition='Every corresponding ordinal and every nine-tuple of natural registers; CI/CD updates and zero guards identical, all CB/CC ordinal destinations identical, CH identical.',prefix_summary={k:v for k,v in prefix.items()if k!='entries'},startup_summary={k:v for k,v in startup.items()if k not in('ones','row_counts','spares')},input_hashes=input_hashes,checker_sha256=sha(Path(__file__)))
 dump(a.out/'independent_facts.json',receipt);print(json.dumps({k:v for k,v in receipt.items()if k not in('input_hashes','search_to_canonical','table_transformations','fold_contexts','source_stages')},indent=2))
if __name__=='__main__':
 if not __debug__:raise RuntimeError('Run without -O, -OO or PYTHONOPTIMIZE')
 main()
