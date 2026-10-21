from pathlib import Path
import sys,json,itertools,hashlib,collections
F=Path(__file__).resolve().parent;O=F.parent/'reproduced/cantor-scratch';O.mkdir(parents=True,exist_ok=True);sys.path.insert(0,str(F));import complement_quantifier as c
s,m,b=c.s,c.m,c.b
I=lambda r:('CI',r)
D=lambda r:('CD',r)
move=lambda a,z:(D(a),(I(z),('CC',2)))
copy=lambda a,z,tmp:((D(a),(I(z),(I(tmp),('CC',3)))),move(tmp,a))
pair=c.imp[1][0];u=c.imp[0];u8=m.rename(u,{2:8});pop=(u,move(6,5))
reads={dest:(u8,move(6,dest))for dest in [1,3,4,5]}
oldcopies={(a,z):copy(a,z,6)for a,z in [(0,8),(3,1),(4,1),(5,1)]}
assert oldcopies[4,1]==c.q(98)[1];assert oldcopies[5,1]==c.q(12)[1];assert oldcopies[3,1]==c.q(166)[1]
def inverse(head,dest):
 # Old loop leaves first coordinate in6 and second in7; reversed pair
 # needs second coordinate as head and first as restored tail.
 loop=u[0] if head==7 else m.rename(u[0],{6:7,7:6})
 return m.rename(loop,{2:dest}),move(13-head,dest)
results=[];best=999
for h,phead in itertools.product([6,7],repeat=2):
 acc=13-h;pcore=m.rename(pair,{6:h,7:acc});push=(move(2,h),(pcore,move(acc,2)));imp=(inverse(h,2),(pcore,m.rename(c.imp[1][1],{7:acc})));newpop=(inverse(h,2),move(h,5));newreads={d:(inverse(phead,8),move(phead,d))for d in reads}
 for mask in range(16):
  cp={k:copy(*k,6+((mask>>j)&1))for j,k in enumerate(oldcopies)};hist=collections.Counter()
  def go(t):
   if t==c.imp:hist['I']+=1;return imp
   if t==c.push:hist['push']+=1;return push
   if t==pop:hist['pop']+=1;return newpop
   for d,n in reads.items():
    if t==n:hist[f'read{d}']+=1;return newreads[d]
   for k,n in oldcopies.items():
    if t==n:hist[f'copy{k}']+=1;return cp[k]
   return t if s.leaf(t)else(go(t[0]),go(t[1]))
  rr=go(c.tree);assert hist['I']==81 and hist['push']==93 and hist['pop']==1 and sum(hist[f'read{d}']for d in reads)==3,hist
  rr=m.splice(s,rr,9,23,newreads[3]);hist['read3']=1
  if mask&1:
   for i in [4,7]:
    pth,op,arg=c.rows[i];assert arg==6;rr=s.replace(rr,pth,(op,7))
  met=s.metrics(rr);name=f'cantor-scratch-h{h}-p{phead}-c{mask}';rec={'name':name,'stack_head_register':h,'program_head_register':phead,'copy_scratch_bits':mask,'metrics':met,'macro_occurrences':dict(hist)}
  if met['dag_nodes']<=206:
   raw=s.compact(s.sites(rr));(O/(name+'.sites.json')).write_bytes(raw);rec['source_sha256']=hashlib.sha256(raw).hexdigest()
   try:
    nt,meta=m.compile_tree(s,b,c.table,c.tree,rr);rec['allocation']=meta;(O/(name+'.tm')).write_bytes(b.table_bytes(nt))
   except Exception as e:rec['allocation_error']=repr(e)
  if met['dag_nodes']<best:best=met['dag_nodes'];print('BEST',rec,flush=True)
  results.append(rec);m.flat.cache_clear();s.boundary.cache_clear()
(O/'results.json').write_text(json.dumps(results,indent=2)+'\n');print('DONE',len(results),'best',best,flush=True)
