from pathlib import Path
import sys,json,itertools,hashlib,collections
F=Path(__file__).resolve().parent;O=F.parent/'reproduced';O.mkdir(parents=True,exist_ok=True);sys.path.insert(0,str(F));import complement_quantifier as c
s,m,b=c.s,c.m,c.b
pair=c.imp[1][0];swpair=m.rename(pair,{1:6,6:1});unpair=c.imp[0];swunpair=(m.rename(unpair[0],{6:7,7:6}),unpair[1]);u8=m.rename(unpair,{2:8});swu8=m.rename(swunpair,{2:8})
def repl(t,old,new):
 if t==old:return new
 return t if s.leaf(t)else(repl(t[0],old,new),repl(t[1],old,new))
swpush=repl(c.push,pair,swpair)
P=lambda a,b:(a+b)*(a+b+1)//2+b
for a,bb in itertools.product(range(8),repeat=2):
 regs=[0,bb,0,0,0,0,a,0,0];got,_=m.run_macro(s,swpair,regs);want=regs.copy();want[1]=want[6]=0;want[7]=P(bb,a);assert got==want
 regs=[0,0,P(bb,a),0,0,0,0,0,0];got,_=m.run_macro(s,swunpair,regs);want=regs.copy();want[2]=bb;want[6]=a;assert got==want
 regs=[0,a,bb,0,0,0,0,0,0];got,_=m.run_macro(s,swpush,regs);want=regs.copy();want[1]=0;want[2]=P(bb,a);assert got==want
results=[]
for f,st,p in itertools.product([0,1],repeat=3):
 newimp=((swunpair if st else unpair),((swpair if f else pair),c.imp[1][1]))
 hist=collections.Counter()
 def go(t):
  if t==c.imp:hist['I']+=1;return newimp
  if t==c.push:hist['push']+=1;return swpush if st else c.push
  if t==unpair:hist['unpair2']+=1;return swunpair if st else unpair
  if t==u8:hist['unpair8']+=1;return swu8 if p else u8
  return t if s.leaf(t)else(go(t[0]),go(t[1]))
 rr=go(c.tree);assert hist=={'I':81,'push':93,'unpair2':1,'unpair8':4};rows=s.sites(rr);assert s.graph_arithmetic(rows)[0]==s.graph_intervals(rows);raw=s.compact(rows);name=f'cantor-f{f}-s{st}-p{p}';(O/(name+'.sites.json')).write_bytes(raw);rec={'name':name,'formula_swap':f,'stack_swap':st,'program_swap':p,'metrics':s.metrics(rr),'source_sha256':hashlib.sha256(raw).hexdigest(),'macro_occurrences':dict(hist)}
 try:
  nt,meta=m.compile_tree(s,b,c.table,c.tree,rr);rec['allocation']=meta;(O/(name+'.tm')).write_bytes(b.table_bytes(nt))
 except Exception as e:rec['allocation_error']=repr(e)
 results.append(rec);print(rec,flush=True)
(O/'cantor_orientation_results.json').write_text(json.dumps(results,indent=2)+'\n')
