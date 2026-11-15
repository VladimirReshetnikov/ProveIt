from pathlib import Path
import sys,json,itertools,collections,hashlib,shutil
W=Path(__file__).resolve().parent;ROOT=W/'tagged3_pricing';ROOT.mkdir(exist_ok=True)
P=W.parent;sys.path.insert(0,str(P/'construction/vendor'))
import compiler as c,support as s
INC=('leaf','inc',1)
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
def expanded(t):
 if t=='node60':return(INC,INC)
 if t=='node61':return((INC,INC),(INC,INC))
 return tuple(map(expanded,t))if c.isnode(t)else t
def word(t):return word(t[0])+word(t[1])if c.isnode(t)else[t]
def encode(t):
 rs={};idx={}
 def go(t):
  if not c.isnode(t):return t
  if t in idx:return idx[t]
  a,b=map(go,t);i='g'+str(len(rs));rs[i]=[a,b];idx[t]=i;return i
 r=go(t);return{'root':r,'rules':rs}
base=P/'inputs/PA194AX11GH'
raw=s.read_table(base/'raw.native.tm')
ns={k:tup(v)for k,v in json.loads((base/'nodes.json').read_text()).items()}
g=expanded(tup(json.loads((base/'grammar.tree.json').read_text())))
w=word(g);repls={};deletes=set();hist=collections.Counter()
for i,t in enumerate(w):
 if t!='node65':continue
 j=i+1
 while j<len(w)and w[j]==INC:j+=1
 tag=j-i-1;hist[tag]+=1;assert tag<4,(i,tag)
 if tag==1:repls[i]=('nodeDouble','node65')
 if tag==3:
  repls[i]=('nodeDouble',(INC,'node65'));deletes|={i+2,i+3}
it=iter(range(len(w)))
def replace(t):
 if c.isnode(t):
  a,b=map(replace,t)
  if a is None:return b
  if b is None:return a
  return(a,b)
 i=next(it)
 return None if i in deletes else repls.get(i,t)
t=replace(g);ww=word(t)
# DoubleT: transfer T to X, then transfer X to T with two increments per unit.
ns['nodeDouble']=('node37',(('leaf','dec',6),('node60',('leaf','continueTo',2))))
ns['node61']=(INC,'node60')
raw[190,0]=(0,True,61);raw[190,1]=(1,True,99)
raw[400,0]=(0,True,28);raw[400,1]=(1,True,401)
raw[401,0]=(0,True,21);raw[401,1]=(1,True,402)
raw[402,0]=(0,True,99);raw[402,1]=(0,False,16)
c.MACROS['nodeDouble']=400
c.MACROS[(INC,INC)]=99
c.MACROS.pop(((INC,INC),(INC,INC)),None)
c.MACROS[(INC,(INC,INC))]=190
c.machine=lambda:(raw,[]);c.raw_nodes=lambda:ns
rows,idx,shape=c.build(t)
ops=c.opportunities_fast(rows,shape)
match=c.max_matching(ops)
sites,ins,cs=c.source(t)
for fn,x in [('nodes.json',ns),('grammar.tree.json',t),('grammar.json',encode(t)),('instructions.json',ins),('sites.json',[[''.join(map(str,p)),op,arg]for p,op,arg in sites])]:
 (ROOT/fn).write_text(json.dumps(x,indent=2)+'\n')
(ROOT/'raw.native.tm').write_text(s.table_text(rows))
print(json.dumps({'oldword':len(w),'newword':len(ww),'cons_tag_histogram':hist,'fixed':len(rows)//2-len(shape),'readers':len(shape),'optimistic_folds':len(match),'optimistic_total':len(rows)//2-len(match),'source_sites':len(ins),'contracts':len(cs),'maxdepth':max(len(p)for p,op,a in sites),'extra_macro_states':[400,401,402]},indent=2),flush=True)
(ROOT/'initial_price.json').write_text(json.dumps({'oldword':len(w),'newword':len(ww),'cons_tag_histogram':hist,'fixed':len(rows)//2-len(shape),'readers':len(shape),'optimistic_folds':len(match),'optimistic_total':len(rows)//2-len(match),'source_sites':len(ins),'contracts':len(cs),'maxdepth':max(len(p)for p,op,a in sites),'extra_macro_states':[400,401,402]},indent=2)+'\n')
print(c.validate(rows,cs),flush=True)
