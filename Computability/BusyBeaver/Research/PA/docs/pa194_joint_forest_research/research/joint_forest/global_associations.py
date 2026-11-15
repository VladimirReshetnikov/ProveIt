"""Jointly hash-cons operand, MP and loop trees, then fold history contexts."""
from pathlib import Path
import sys,json,itertools,collections,time,argparse
HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parents[1]
sys.path.insert(0,str(PACKAGE/'construction/vendor'))
sys.path.insert(0,str(HERE/'vendor'))
import compiler as c, support as s, engine_foldscreen as fs
ap=argparse.ArgumentParser();ap.add_argument('--grammar',type=Path);ap.add_argument('--label',default='global_associations');ap.add_argument('--screen',action='store_true');ap.add_argument('--family',help='operand,mp,loop integers');ap.add_argument('--output',type=Path,help='output directory (default: runs/LABEL)');args=ap.parse_args()
M=HERE/'inputs';OUT=args.output or HERE/'runs'/args.label;OUT.mkdir(parents=True,exist_ok=True)
def tup(x):return tuple(map(tup,x)) if isinstance(x,list)else x
def trees(word):
 if len(word)==1:return [word[0]]
 return [(a,b)for k in range(1,len(word))for a in trees(word[:k])for b in trees(word[k:])]
def nodesof(t):
 if not c.isnode(t):return set()
 return {t}|nodesof(t[0])|nodesof(t[1])
INC=('leaf','inc',1)
original=s.read_table(M/'parent.native.tm')
oldnodes={k:tup(v) for k,v in json.loads((M/'nodes.json').read_text()).items()}
oldnodes['node75']=('node74','node65')
grammar=c.read_grammar(args.grammar or M/'grammar.json');c.raw_nodes=lambda:oldnodes
oldsites,oldins,_=c.source(grammar)
oldmacros=dict(c.MACROS)
hist=collections.Counter();hits=[];records=[];tick=time.monotonic()
for ai,operand in enumerate(trees(('node32','node53','node55','node65'))):
 for bi,mp in enumerate(trees(('node75','node37','node6','node54'))):
  for li,loop0 in enumerate(trees((INC,INC,INC,INC,'RET'))):
   if args.family and [ai,bi,li]!=list(map(int,args.family.split(','))):continue
   depth=0;last=loop0
   while c.isnode(last):last=last[1];depth+=1
   if depth not in (1,2):continue
   ret=('leaf','continueTo',depth+1)
   def replace(t):return tuple(map(replace,t))if c.isnode(t)else ret if t=='RET'else t
   loop=replace(loop0)
   n=dict(oldnodes);n['node75']=operand;n['node164']=mp;n['node62']=loop
   c.raw_nodes=lambda:n
   base={k:v for k,v in original.items()if k[0]<1300 and k[0]not in(92,185,213,100,174,164,139,190)}
   base[69,0]=(0,False,92);base[92,0]=(0,True,111);base[92,1]=(1,True,90)
   atoms={'node32':104,'node53':107,'node55':98,'node65':90,'node37':28,'node6':77,'node54':114,INC:61}
   used={};fresh=[330]
   def compile_t(t):
    if t in atoms:return atoms[t]
    if t in used:return used[t]
    def edge(u,b):
     if isinstance(u,tuple) and u[0]=='leaf' and u[1]=='continueTo':
      return (0,False,16) if u[2]==2 else (1,False,73)
     return (b,True,compile_t(u))
    a0,a1=edge(t[0],0),edge(t[1],1)
    for q,_ in base:
     if base[q,0]==a0 and base[q,1]==a1:used[t]=q;return q
    q=fresh[0];fresh[0]+=1;base[q,0]=a0;base[q,1]=a1;used[t]=q;return q
   opq=compile_t(operand);atoms['node75']=opq
   mpq=compile_t(mp);loopq=compile_t(loop)
   base[96,1]=(1,True,mpq);base[125,1]=(1,True,loopq)
   c.MACROS=dict(oldmacros);c.MACROS.pop('node61',None);c.MACROS['node75']=opq
   c.MACROS[(INC,INC)]=99
   c.MACROS.update(used)
   c.machine=lambda:(base,[])
   raw,index,shape=c.build(grammar)
   # Discard controls made structurally unreachable by this global construction.
   reach={74};todo=[74]
   for q in todo:
    for bit in(0,1):
     z=raw[q,bit][2]
     if z!=254 and z not in reach:reach.add(z);todo.append(z)
   raw={k:v for k,v in raw.items()if k[0]in reach}
   incoming=collections.defaultdict(list)
   for k,v in raw.items():incoming[v[2]].append((k,v))
   ops=[x for x in fs.opportunities(raw) if all(v[1] and v[0]==k[1] for q in x[:2]for k,v in incoming[q])]
   choices={(a,b):v for a,b,v in ops}
   folds=[[a,b,[o[0]for o in choices[a,b]]]for a,b in fs.matching(ops)]
   price=len(raw)//2-len(folds);hist[price]+=1
   rec={'operand':ai,'mp':bi,'loop':li,'raw':len(raw)//2,'folds':len(folds),'price':price}
   if price<=194 and not args.screen:
    try:
     child,aliases=s.apply_folds(raw,folds);lc=s.check_local_folds(raw,child,aliases,folds)
     sites,ins,contracts=c.source(grammar)
     assert ins==oldins,'source changed'
     runtime=c.validate(child,contracts);rec['runtime']=runtime
     if runtime['ok']:
      startup=s.startup(child,sites[25][0]);dense,labels=s.dense_table(child,price)
      name=f'A{ai}M{bi}L{li}_{price}';D=OUT/name;D.mkdir(exist_ok=True)
      for f,t in [('machine.native.tm',child),('machine.tm',dense),('raw.native.tm',raw)]:
       (D/f).write_text(s.table_text(t))
      for f,v in [('nodes.json',n),('grammar.tree.json',grammar),('macro_bindings.json',list(c.MACROS.items())),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',ins),('folds.json',folds),('labels.json',labels),('local.json',lc)]:
       (D/f).write_text(json.dumps(v,indent=2)+'\n')
      rec.update(name=name,startup=startup,changed_addresses=sum(a[0]!=b[0]for a,b in zip(sites,oldsites)))
      (D/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');hits.append(name)
      print('HIT',name,'changed',rec['changed_addresses'],flush=True)
    except(AssertionError,KeyError)as e:rec['failure']=str(e)
   records.append(rec)
summary={'families':len(records),'histogram':dict(hist),'hits':hits,'seconds':time.monotonic()-tick,'records':records}
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('DONE',{k:v for k,v in summary.items()if k!='records'},flush=True)
