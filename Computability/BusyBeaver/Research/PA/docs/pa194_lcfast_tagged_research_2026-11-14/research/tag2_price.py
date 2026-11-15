from pathlib import Path
import sys,json,collections
W=Path(__file__).resolve().parent;P=W.parent;OUT=W/'tagged2_pricing';OUT.mkdir(exist_ok=True)
sys.path.insert(0,str(P/'construction/vendor'));import compiler as c,support as s
INC=('leaf','inc',1)
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
def expand(t):
 if t=='node60':return(INC,INC)
 if t=='node61':return((INC,INC),(INC,INC))
 return tuple(map(expand,t))if c.isnode(t)else t
def word(t):return word(t[0])+word(t[1])if c.isnode(t)else[t]
ns={k:tup(v)for k,v in json.load(open(P/'inputs/PA194AX11GH/nodes.json')).items()};raw=s.read_table(P/'inputs/PA194AX11GH/raw.native.tm')
t=expand(tup(json.load(open(P/'inputs/PA194AX11GH/grammar.tree.json'))));w=word(t);repl={};delete=set();hist=collections.Counter()
for i,z in enumerate(w):
 if z!='node65':continue
 j=i+1
 while j<len(w)and w[j]==INC:j+=1
 tag=j-i-1;hist[tag]+=1
 if tag==2:repl[i]='nodeConsOdd';delete|={i+1,i+2}
 if tag==3:repl[i]='nodeConsOdd';delete|={i+2,i+3}
it=iter(range(len(w)))
def replace(t):
 if c.isnode(t):
  a,b=map(replace,t)
  return b if a is None else a if b is None else(a,b)
 i=next(it);return None if i in delete else repl.get(i,t)
t=replace(t)
ns['nodeIncYY']=(('leaf','inc',7),('leaf','inc',7))
ns['nodeDoubleX']=((('leaf','dec',6),('nodeIncYY',('leaf','continueTo',2))),'node10')
ns['nodeDecodeDouble']=('node17','nodeDoubleX')
ns['node65']=('nodeDecodeDouble','node64')
ns['nodeConsOdd']=('nodeDecodeDouble',(('leaf','inc',6),'node64'))
ns['node62']=('node60',('leaf','continueTo',2))
# Reuse obsolete quadruple-increment state190 as the doubled-Y primitive.
raw[190,0]=(0,True,82);raw[190,1]=(1,True,82)
raw[139,0]=(0,True,99)
raw[90,0]=(0,True,403)
raw[400,0]=(0,True,401);raw[400,1]=(1,True,109)
raw[401,0]=(0,True,21);raw[401,1]=(1,True,402)
raw[402,0]=(0,True,190);raw[402,1]=(0,False,16)
raw[403,0]=(0,True,105);raw[403,1]=(1,True,400)
raw[404,0]=(0,True,403);raw[404,1]=(1,True,405)
raw[405,0]=(0,True,13);raw[405,1]=(1,True,106)
c.MACROS.pop('node61',None);c.MACROS['nodeConsOdd']=404;c.MACROS[(INC,INC)]=99
c.machine=lambda:(raw,[]);c.raw_nodes=lambda:ns
rows,idx,shape=c.build(t);ops=c.opportunities_fast(rows,shape);match=c.max_matching(ops)
sites,ins,cs=c.source(t)
r=dict(old_tokens=len(w),tokens=len(word(t)),fixed=len(rows)//2-len(shape),readers=len(shape),optimistic_folds=len(match),optimistic_total=len(rows)//2-len(match),source_sites=len(ins),contracts=len(cs),histogram=hist)
for fn,obj in [('grammar.tree.json',t),('nodes.json',ns),('instructions.json',ins),('sites.json',[[''.join(map(str,p)),o,a]for p,o,a in sites]),('initial_price.json',r)]:
 (OUT/fn).write_text(json.dumps(obj,indent=2)+'\n')
(OUT/'raw.native.tm').write_text(s.table_text(rows))
print(json.dumps(r,indent=2),flush=True)
print(c.validate(rows,cs),flush=True)
