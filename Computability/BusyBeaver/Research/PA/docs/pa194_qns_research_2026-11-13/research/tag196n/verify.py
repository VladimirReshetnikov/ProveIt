from pathlib import Path
import sys,json,collections,itertools,hashlib
ROOT=Path(__file__).parent
sys.path.insert(0,str(ROOT/'vendor'))
import compiler as c,support as s
baseline=s.read_table(ROOT/'inputs/base201.native.tm')
INC=('leaf','inc',1)
baseline.update({(190,0):(0,True,61),(190,1):(1,True,330),
                 (330,0):(0,True,61),(330,1):(1,True,99),
                 (164,1):(1,True,114)})
c.machine=lambda:(baseline,[])
oldnodes=c.raw_nodes
def nodes():
 ns=oldnodes();ns['node61']=(INC,(INC,'node60'));ns['node163']=('node6','node54');return ns
c.raw_nodes=nodes
c.MACROS[(INC,INC)]=99;c.MACROS[((INC,INC),(INC,INC))]=190
c.MACROS[(INC,(INC,INC))]=330;c.MACROS[(INC,'node60')]=330
if not __debug__:raise SystemExit('Run without -O or PYTHONOPTIMIZE.')
t=c.read_grammar(Path(sys.argv[1]) if len(sys.argv)>1 else ROOT/'inputs/grammar.json')
raw,_,shape=c.build(t)
incoming=collections.defaultdict(set)
for (q,b),(w,d,n) in raw.items():incoming[n].add((w,d))
ops=[(a,b,o)for a,b,o in c.opportunities_fast(raw,set(q for q,b in raw))
     if a!=74 and incoming[a]=={(0,True)}and incoming[b]=={(1,True)}]
best=[]
def rec(i,sel,used):
 global best
 if len(sel)+len(ops)-i<=len(best):return
 if i==len(ops):
  try:
   child,aliases=s.apply_folds(raw,sel);local=s.check_local_folds(raw,child,aliases,sel)
  except (AssertionError,KeyError):return
  best=sel.copy();return
 a,b,choices=ops[i]
 if a not in used and b not in used:
  for acts in itertools.product(*choices):rec(i+1,sel+[[a,b,acts]],used|{a,b})
 rec(i+1,sel,used)
rec(0,[],set())
child,aliases=s.apply_folds(raw,best);count=len(child)//2
box_rows_unchanged=all(child[q,b]==baseline[q,b] for q in c.BOXSTATES for b in (0,1))
assert box_rows_unchanged
assert count==196
print('count',count,'raw',len(raw)//2,'shape',len(shape),'folds',len(best),flush=True)
sites,ins,cs=c.source(t)
valid=c.validate(child,cs);print('contracts',valid,flush=True)
assert valid['ok']
blank=s.startup(child,sites[25][0]);print('startup',blank['steps'],flush=True)
out=ROOT/'machine';out.mkdir(exist_ok=True)
dense,labels=s.dense_table(child,count)
(out/'machine.tm').write_text(s.table_text(dense));(out/'machine.native.tm').write_text(s.table_text(child))
for name,data in [('folds',best),('sites',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions',ins),('labels',labels)]:
 (out/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
(out/'receipt.json').write_text(json.dumps(dict(count=count,raw=len(raw)//2,shape=len(shape),folds=len(best),arithmetic_box_rows_checked=2*len(c.BOXSTATES),arithmetic_box_rows_unchanged=box_rows_unchanged,valid=valid,blank=blank),indent=2)+'\n')
