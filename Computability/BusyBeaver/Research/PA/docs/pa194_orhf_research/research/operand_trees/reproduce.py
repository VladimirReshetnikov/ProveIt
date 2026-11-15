from pathlib import Path
import sys,json,argparse
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]/'reference/PA194ORH'
sys.path.insert(0,str(HERE.parent/'expanded_operand_reader/vendor'))
import compiler as c,support as s
parser=argparse.ArgumentParser(description='Enumerate five closed operand-tree associations; no consistency claim for generated raw tables.')
parser.add_argument('--output',type=Path,default=HERE/'replay')
O=parser.parse_args().output;O.mkdir(parents=True,exist_ok=True)
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
nodes0={k:tup(v)for k,v in json.loads((ROOT/'nodes.json').read_text()).items()}
g=c.read_grammar(ROOT/'grammar.json')
base={k:v for k,v in s.read_table(ROOT/'raw.native.tm').items()if k[0]<1300}
A,B,C,D='node32','node53','node55','node65'
variants={'balanced':((A,B),(C,D)),'right':(A,(B,(C,D))),'left':(((A,B),C),D),'left_right':((A,(B,C)),D),'right_left':(A,((B,C),D))}
leaf={A:104,B:107,C:98,D:90}
originalmacros=dict(c.MACROS);INC=('leaf','inc',1);originalmacros[(INC,INC)]=99;originalmacros[((INC,INC),(INC,INC))]=190
res=[]
for name,t in variants.items():
 nodes=dict(nodes0);nodes['node75']=t;fixed=dict(base);mp={t:213};ids=iter([185,333]);c.MACROS.clear();c.MACROS.update(originalmacros)
 def compile(t):
  if isinstance(t,str):return leaf[t]
  if t not in mp:mp[t]=next(ids)
  q=mp[t]
  for b,ch in enumerate(t):fixed[q,b]=(b,True,compile(ch))
  return q
 compile(t)
 for sub,q in mp.items():c.MACROS[sub]=q
 c.machine=lambda:(fixed,[]);c.raw_nodes=lambda:nodes
 raw,index,shape=c.build(g);sites,ins,contracts=c.source(g)
 assert ins==[tuple(x)for x in json.loads((ROOT/'instructions.json').read_text())]
 ops=c.opportunities_fast(raw,shape);match=c.max_matching(ops)
 # broader fixed-reader fold candidates, with exact incoming checks
 incoming={q:[]for q,b in raw}
 for(q,b),(w,d,u)in raw.items():
  if u in incoming:incoming[u].append((w==b and d,b))
 valid={q for q,es in incoming.items()if es and all(x for x,b in es)and q not in c.BOXSTATES}
 broad=c.opportunities_fast(raw,valid);bm=c.max_matching(broad)
 rec=dict(name=name,raw=len(raw)//2,readers=len(shape),ordinary_folds=len(match),score=len(raw)//2-len(match),broad_folds=len(bm),broad_score=len(raw)//2-len(bm))
 print(rec,flush=True);res.append(rec)
 (O/(name+'.raw.tm')).write_text(s.table_text(raw))
 (O/(name+'.opportunities.json')).write_text(json.dumps(ops))
(O/'summary.json').write_text(json.dumps(res,indent=2)+'\n')
