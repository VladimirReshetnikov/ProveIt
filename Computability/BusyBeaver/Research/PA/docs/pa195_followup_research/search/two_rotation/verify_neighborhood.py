#!/usr/bin/env python3
"""Independent Python enumeration and exact fold scoring of the two-rotation census.

No imports from the search code or vendored compiler. Python3 standard library.
Usage: python3 verify_neighborhood.py [PA195_reference_directory]
"""
import ast,csv,hashlib,itertools,json,re,struct,sys,time
from collections import Counter,defaultdict
from functools import lru_cache
from pathlib import Path
HERE=Path(__file__).resolve().parent
BASE=Path(sys.argv[1]) if len(sys.argv)>1 else HERE.parent/'pa195_conpa/pa195'
PREFIX=HERE/'pa195_neighborhood'
START=time.time()
INC=('leaf','inc',1);BREAK=('leaf','breakTo',1)
SYMBOLS=['node58','node55','node65',INC,'node72','node75','node70','node49','node142','node150',BREAK]
SYMBOL_ID={t:-i-1 for i,t in enumerate(SYMBOLS)}

def require(ok,message):
 if not ok:raise ValueError(message)
def node(t):return isinstance(t,tuple) and len(t)==2

def grammar(path):
 data=json.loads(path.read_text());rules=data['rules']
 @lru_cache(None)
 def ref(x):return tuple(convert(y) for y in rules[x]) if x in rules else x
 def convert(x):return tuple(x) if isinstance(x,list) else ref(x)
 return ref(data['root'])
seed=grammar(BASE/'grammar.json')

def treeword(t):return treeword(t[0])+treeword(t[1]) if node(t) else (t,)
ORIGINAL_WORD=treeword(seed)
require(len(ORIGINAL_WORD)==191,'unexpected original word size')

def positions(t,p=()):
 if node(t):
  yield t,p;yield from positions(t[0],p+(0,));yield from positions(t[1],p+(1,))

def replace_all(t,old,new):
 if t==old:return new
 return (replace_all(t[0],old,new),replace_all(t[1],old,new)) if node(t) else t

def replace_at(t,path,new):
 if not path:return new
 return (replace_at(t[0],path[1:],new),t[1]) if path[0]==0 else (t[0],replace_at(t[1],path[1:],new))

def rotations(x):
 a,b=x
 if node(a):yield a[0],(a[1],b)
 if node(b):yield (a,b[0]),b[1]

def neighbors(t):
 pp=list(positions(t))
 for x in set(x for x,p in pp):
  for new in rotations(x):yield replace_all(t,x,new),0
 for x,p in pp:
  for new in rotations(x):yield replace_at(t,p,new),1

first={};calls1=Counter()
for t,kind in neighbors(seed):first[t]=first.get(t,0)|(1<<kind);calls1[kind]+=1
second={};calls2=Counter()
for i,(t,mask) in enumerate(first.items()):
 for u,kind in neighbors(t):
  flags=sum(1<<(2*f+kind) for f in(0,1) if mask&(1<<f))
  second[u]=second.get(u,0)|flags;calls2[kind]+=1
alltrees=set(first)|set(second)|{seed}
print('ENUMERATED',len(first),len(second),len(alltrees),'seconds',round(time.time()-START,2),flush=True)

# The reference macros are parsed independently from the pinned Lean definitions.
rawnodes={}
for line in (BASE/'vendor/reference/PA196/Program.lean').read_text().splitlines():
 m=re.fullmatch(r'def (\w+) : Tree := \.node (.+)',line)
 if not m:continue
 tokens=re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b',m[2])
 require(len(tokens)==2,'reference macro parse')
 rawnodes[m[1]]=tuple(name if name else ('leaf',op,int(arg) if arg else None) for op,arg,name in tokens)

@lru_cache(None)
def attrs(t):
 if isinstance(t,str):return attrs(rawnodes[t])
 if not node(t):return 0,0,0,0,t[1]=='inc'
 a,b=attrs(t[0]),attrs(t[1])
 return 1+max(a[0],b[0]),1+a[1],max(1+a[1],a[2],b[2]),max(a[3],b[3],1+a[1] if a[4] else 0),a[4]

def gates(t):
 a=attrs(t);unique=set(x for x,p in positions(t));left=sum(x[0]=='node142' for x in unique);right=sum(x[1]=='node72' for x in unique)
 mask=(a[2]>6)*1+(a[3]>5)*2+(left>0)*4+(right>0)*8+(a[0]>39)*16
 return int(mask),(a[0],a[2],a[3],left,right)

def canonical_key(t):
 rules=[];seen={}
 def intern(x):
  if not node(x):return SYMBOL_ID[x]
  if x in seen:return seen[x]
  a=intern(x[0]);b=intern(x[1]);i=len(rules);seen[x]=i;rules.append((a,b));return i
 root=intern(t);values=[root,len(rules)]+[j for pair in rules for j in pair]
 return struct.pack('<'+'i'*len(values),*values)

raw=PREFIX.with_suffix('.keys.bin').read_bytes();keys=[];pos=0
while pos<len(raw):
 require(pos+4<=len(raw),'partial binary key length');length=struct.unpack_from('<I',raw,pos)[0];pos+=4
 require(pos+length<=len(raw),'partial binary key');keys.append(raw[pos:pos+length]);pos+=length
require(len(keys)==len(set(keys)),'duplicate C++ canonical key')
with PREFIX.with_suffix('.census.tsv').open() as f:census=[{k:int(v) for k,v in row.items()} for row in csv.DictReader(f,delimiter='\t')]
require(len(keys)==len(census),'key/census count differs')
lookup={key:census[i] for i,key in enumerate(keys)}
require(len(alltrees)==len(lookup),'independent grammar count differs')

# Independently reconstruct the physical allocation from the inherited rows.
labels=ast.literal_eval(re.search(r'def labels : List Nat := (\[[^\n]+\])',(BASE/'vendor/reference/PA196/Conjugacy.lean').read_text())[1])
ENGINE={}
for line in (BASE/'vendor/reference/data/pa196.tm').read_text().splitlines():
 q,r,w,d,n=line.split();q,r,w,n=map(int,(q,r,w,n));q=labels[q]
 if q<1300:ENGINE[q,r]=(w,d=='R',labels[n])
require(len(ENGINE)==268,'inherited state count')
pair=(INC,INC)
MACROS={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,'node72':69,'node75':213,'node142':194,'node150':221,INC:61,pair:99,(pair,pair):190}

def compile_table(t):
 rows=dict(ENGINE);allocated={}
 def root(x):
  if x in MACROS:return MACROS[x]
  if x in allocated:return allocated[x]
  require(node(x),'unknown macro');q=2000+len(allocated);allocated[x]=q
  for r,child in enumerate(x):rows[q,r]=(0,False,302) if child==BREAK else (r,True,root(child))
  return q
 rows[101,1]=(1,True,root(t));return rows,set(allocated.values())

def exact_fold_count(rows,newstates):
 incoming=defaultdict(set)
 for (q,r),(w,d,n) in rows.items():incoming[n].add((w,d))
 left=[q for q in newstates if incoming[q]=={(0,True)}]
 right=[q for q in newstates if incoming[q]=={(1,True)}]
 providers=[defaultdict(list),defaultdict(list)]
 for q in {q for q,r in rows}:
  w0,d0,u0=rows[q,0];w1,d1,u1=rows[q,1]
  if (w0,d0,w1,d1)!=(0,True,1,True):continue
  for r in(0,1):
   if (u0,r) in rows and(u1,r) in rows:providers[r][rows[u0,r],rows[u1,r]].append((q,u0,u1))
 ops=[];edges=defaultdict(list)
 for a in sorted(left):
  for b in sorted(right):
   choices=[]
   for r in(0,1):
    if rows[a,r]==rows[b,r]:choices.append([rows[a,r]])
    else:choices.append([(r,False,h) for h,u0,u1 in providers[r].get((rows[a,r],rows[b,r]),()) if not({a,b}&{h,u0,u1})])
   if all(choices):ops.append((a,b,choices));edges[a].append(b)
 match={}
 def augment(a,seen):
  for b in edges[a]:
   if b in seen:continue
   seen.add(b)
   if b not in match or augment(match[b],seen):match[b]=a;return True
  return False
 for a in edges:augment(a,set())

 def locally_valid(selected):
  alias={a:b for a,b,acts in selected};replacement={b:acts for a,b,acts in selected}
  for a,b,acts in selected:
   for src,pbit in ((a,0),(b,1)):
    for r in(0,1):
     w,d,n=rows[src,r];target=(alias.get(n,n),1 if d else -1,pbit,w)
     q,pos,one,two=b,0,pbit,r;seen=set();steps=0
     while True:
      if steps and(q,pos,one,two)==target:break
      if pos not in(-1,0):return False
      key=(q,pos,one,two)
      if key in seen:return False
      seen.add(key);read=one if pos==-1 else two
      action=replacement[q][read] if q in replacement else rows.get((q,read))
      if action is None:return False
      ww,dd,nn=action
      if pos==-1:one=ww
      else:two=ww
      pos+=1 if dd else-1;q=alias.get(nn,nn);steps+=1
  return True

 for count in range(len(match),0,-1):
  for chosen in itertools.combinations(ops,count):
   flat=[q for a,b,choices in chosen for q in(a,b)]
   if len(flat)!=len(set(flat)):continue
   for selectedacts in itertools.product(*[list(itertools.product(*choices)) for a,b,choices in chosen]):
    selected=[(a,b,acts) for(a,b,_),acts in zip(chosen,selectedacts)]
    if locally_valid(selected):return count
 return 0

hist=Counter();masks=Counter();checked=0;identities=0
for t in alltrees:
 key=canonical_key(t);require(key in lookup,'Python grammar absent from C++ key set');rec=lookup[key]
 require(treeword(t)==ORIGINAL_WORD,'word changed')
 require(first.get(t,0)==rec['first_types'],'first-neighbor reachability differs')
 require(second.get(t,0)==rec['second_types'],'second-neighbor reachability differs')
 mask,aa=gates(t);require(mask==rec['gate_mask'],'gate mask differs')
 require(aa==tuple(rec[k] for k in('ax_depth','max_zero','max_inc_zero','left_node142','right_node72')),'gate attribute differs')
 masks[mask]+=1;identities+=1
 if not mask:
  rows,newstates=compile_table(t);folds=exact_fold_count(rows,newstates);n=len(rows)//2-folds
  require((n,len(newstates),folds)==(rec['states'],rec['readers'],rec['folds']),'exact compatible score differs')
  hist[n]+=1;checked+=1
  if checked%1000==0:print('VERIFIED_SCORES',checked,'seconds',round(time.time()-START,2),flush=True)
summary=json.loads(PREFIX.with_suffix('.summary.json').read_text())
require({int(k):v for k,v in summary['state_histogram_union'].items()}==dict(hist),'histogram differs')
receipt={'independent_grammar_keys_checked':identities,'independent_compatible_scores_checked':checked,'one_step_distinct':len(first),'two_step_distinct':len(second),'union_with_baseline':len(alltrees),'first_operation_counts':dict(calls1),'second_operation_counts':dict(calls2),'state_histogram':dict(hist),'gate_mask_histogram':dict(masks),'canonical_key_sets_equal':True,'all_first_and_second_reachability_flags_equal':True,'all_encoding_gate_flags_equal':True,'all_compatible_scores_equal':True,'exact_cycle_detection_in_both_implementations':True,'minimum_working_states':min(hist),'runtime_contracts_checked':False,'scope_warning':'This is a bounded exclusion for the stated grammar rotations and enumerated contextual-fold allocator, not a lower bound for all machine constructions.','seconds':time.time()-START,'inputs_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [BASE/'grammar.json',HERE/'current_inputs.hpp',HERE/'two_rotation_search.cpp',PREFIX.with_suffix('.census.tsv'),PREFIX.with_suffix('.keys.bin')]}}
HERE.joinpath('independent_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2),flush=True)
