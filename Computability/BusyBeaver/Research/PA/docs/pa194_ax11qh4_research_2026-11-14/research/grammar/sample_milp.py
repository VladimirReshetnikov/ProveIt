from pathlib import Path
import sys,json,random,time,itertools
ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'construction/vendor'
sys.path.insert(0,str(BASE));import compiler as c;import support as s
inc=('leaf','inc',1)
c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
def tup_input(x):return tuple(map(tup_input,x))if isinstance(x,list)else x
rows0=s.read_table(Path(__file__).with_name('inputs')/'primary.raw.native.tm');c.machine=lambda:(rows0,[])
nodes0={k:tup_input(v)for k,v in json.loads((Path(__file__).with_name('inputs')/'primary.nodes.json').read_text()).items()};c.raw_nodes=lambda:nodes0
j=json.loads(Path(__file__).with_name('milp_result.json').read_text())
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
rules={tup(r['word']):tup(r['chunks'])for r in j['grammar']};word=tup(j['word'])
rng=random.Random(1428);best=999;trials=0;t0=time.time();out=Path(__file__).with_name('samples');out.mkdir(exist_ok=True)
oldins=c.source(c.read_grammar(Path(__file__).with_name('inputs')/'primary.grammar.json'))[1]
def tree():
 cache={}
 def go(w):
  if len(w)==1:return w[0]
  if w==(inc,inc):return (inc,inc)
  if w==(inc,inc,inc,inc):return ((inc,inc),(inc,inc))
  if w in cache:return cache[w]
  xs=[go(p)for p in rules[w]]
  while len(xs)>1:
   k=rng.randrange(len(xs)-1);xs[k:k+2]=[(xs[k],xs[k+1])]
  cache[w]=xs[0];return xs[0]
 return go(word)
while time.time()-t0<120:
 g=tree();trials+=1;raw,index,shape=c.build(g);ops=c.opportunities_fast(raw,shape);match=c.max_matching(ops);val=len(raw)//2-len(match)
 if val<best:
  best=val;print('BEST',best,'raw',len(raw)//2,'folds',len(match),'trial',trials,flush=True)
  (out/'best.tree.json').write_text(json.dumps(g))
 if val<=193:
  (out/f'hit{trials}.tree.json').write_text(json.dumps(g))
  try:
   sites,ins,cs=c.source(g)
   if ins!=oldins:continue
   folds=[]
   for a,b in match:
    acts=next(o for x,y,o in ops if x==a and y==b);folds.append([a,b,[a[0]for a in acts]])
   child,aliases=s.apply_folds(raw,folds);local=s.check_local_folds(raw,child,aliases,folds)
   ver=c.validate(child,cs)
   print('HIT',trials,val,ver,flush=True)
   if ver['ok']:
    (out/f'hit{trials}.native.tm').write_text(s.table_text(child));(out/f'hit{trials}.folds.json').write_text(json.dumps(folds))
    seed=s.startup(child,sites[25][0]);print('STARTUP PASS',seed['steps'],flush=True)
    break
  except Exception as e:print('failed',type(e).__name__,str(e)[:100],flush=True)
print('DONE',trials,best,time.time()-t0,flush=True)
