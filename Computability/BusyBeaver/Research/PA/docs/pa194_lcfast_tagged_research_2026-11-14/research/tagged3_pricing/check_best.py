from pathlib import Path
import json,sys,itertools,collections,hashlib
W=Path(__file__).resolve().parent;P=W.parents[1];sys.path.insert(0,str(P/'construction/vendor'))
import compiler as c,support as s
from check_algebra import word
INC=('leaf','inc',1)
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
raw=s.read_table(W/'raw.native.tm');raw={k:v for k,v in raw.items()if k[0]<1300}
ns={k:tup(v)for k,v in json.load(open(W/'nodes.json')).items()}
c.raw_nodes=lambda:ns;c.machine=lambda:(raw,[])
c.MACROS['nodeDouble']=400;c.MACROS[(INC,INC)]=99;c.MACROS[(INC,(INC,INC))]=190;c.MACROS[(INC,'node60')]=190
file=Path(sys.argv[1])if len(sys.argv)>1 else W/'search_run.best.grammar.json'
t=c.read_grammar(file);neww=word(json.loads(json.dumps(t)));oldw=word(json.load(open(W/'grammar.tree.json')))
bounds=[18,35,54,72,90,106,125];mapping=[]
assert neww[:18]==oldw[:18] and neww[125:]==oldw[125:]
for a,b in zip(bounds,bounds[1:]):
 for perm in itertools.permutations(['copyD','copyH','copyA']):
  mp=dict(zip(['copyD','copyH','copyA'],perm))
  if [mp.get(x,x)for x in oldw[a:b]]==neww[a:b]:mapping.append(mp);break
 else:raise AssertionError(('head not a parameter permutation',a,b))
rows,idx,shape=c.build(t);ops=c.opportunities_fast(rows,shape);bound=len(c.max_matching(ops));folds=None;local=None
# Search exactly the complete simultaneously valid choices, not just a matching count.
def search(i,used,chosen,goal):
 global folds,local
 if len(chosen)==goal:
  final,aliases=s.apply_folds(rows,chosen)
  try:case=s.check_local_folds(rows,final,aliases,chosen)
  except(AssertionError,KeyError):return False
  folds=chosen.copy();local=case;return True
 if i==len(ops)or len(chosen)+len(ops)-i<goal:return False
 a,b,choices=ops[i]
 if a not in used and b not in used:
  for actions in itertools.product(*choices):
   if search(i+1,used|{a,b},chosen+[[a,b,actions]],goal):return True
 return search(i+1,used,chosen,goal)
for goal in range(bound,-1,-1):
 if search(0,set(),[],goal):break
final,aliases=s.apply_folds(rows,folds)
sites,ins,contracts=c.source(t)
result=dict(fixed=len(raw)//2,readers=len(shape),folds=len(folds),states=len(final)//2,parameter_permutations=mapping,source_sites=len(ins),contracts=len(contracts))
print(json.dumps(result,indent=2),flush=True)
result['runtime']=c.validate(final,contracts);print(result['runtime'],flush=True)
try:result['startup']=s.startup(final,sites[25][0])
except AssertionError as e:result['startup_error']=str(e)
out=W/'best';out.mkdir(exist_ok=True)
for fn,x in [('grammar.tree.json',t),('instructions.json',ins),('sites.json',[[''.join(map(str,p)),o,a]for p,o,a in sites]),('folds.json',folds),('fold_cases.json',local)]:
 (out/fn).write_text(json.dumps(x,indent=2)+'\n')
(out/'machine.native.tm').write_text(s.table_text(final))
try:
 dense,labels=s.dense_table(final,len(final)//2);(out/'machine.tm').write_text(s.table_text(dense));(out/'labels.json').write_text(json.dumps(labels,indent=2)+'\n')
except AssertionError as e:result['graph_reachability_error']=str(e)
(out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2),flush=True)
