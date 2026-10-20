from search_relaxed import *

def extra_rotations(t,lr):
 qs=collect(lr);ports=collections.Counter(z for w,d,z in t.values());out=[]
 fresh=next(q for q in range(230,254)if(q,0)not in t)
 for q,ns in qs.items():
  if len(ns)!=1 or any(t[q,b][:2]!=(b,1)for b in(0,1)):continue
  n=next(iter(ns))
  for bit in(0,1):
   r=t[q,bit][2]
   if r not in qs or len(qs[r])!=1 or ll(n[bit+1])or r!=n[bit+1][0]:continue
   if ports[r]<2 or any(t[r,b][:2]!=(b,1)for b in(0,1)):continue
   ch=n[bit+1];a,b,cc=(ch[1],ch[2],n[2])if bit==0 else(n[1],ch[1],ch[2])
   if all(c.boundary(unlabel(k))==(0,0,False)for k in(a,b,cc)):
    out.append((q,r,bit,fresh,'clone'))
 return out

def rotate_extra(t,lr,rot):
 tt,lrr=rotate(t,lr,rot)
 if len(rot)==5:
  q,r,bit,s,_=rot
  if bit==0:tt[s,0]=(0,1,t[r,1][2]);tt[s,1]=(1,1,t[q,1][2])
  else:tt[s,0]=(0,1,t[q,0][2]);tt[s,1]=(1,1,t[r,0][2])
 return tt,lrr

def gc_quotient(t,lr):
 seen={0};todo=[0]
 while todo:
  q=todo.pop()
  if q==254:continue
  for b in(0,1):
   z=t[q,b][2]
   if z not in seen:seen.add(z);todo.append(z)
 tt={(q,b):a for(q,b),a in t.items()if q in seen};states=sorted(seen-{254})
 partition={q:0 for q in states};partition[254]=-1
 while True:
  classes={};new={254:-1}
  for q in states:
   sig=tuple((w,d,partition[z])for w,d,z in(tt[q,0],tt[q,1]))
   new[q]=classes.setdefault(sig,len(classes))
  if all(partition[q]==new[q]for q in states):break
  partition=new
 groups=collections.defaultdict(list)
 for q in states:groups[partition[q]].append(q)
 phi={q:min(g)for g in groups.values()for q in g};phi[254]=254
 result={(phi[q],b):(w,d,phi[z])for(q,b),(w,d,z)in tt.items()}
 @c.cache
 def change(n):return n if ll(n)else(phi.get(n[0],n[0]),change(n[1]),change(n[2]))
 return result,change(lr),dict(removed=sorted({q for q,b in t}-{q for q,b in result}),mapping=phi)

def zeros(lr):
 ss=c.sites(unlabel(lr));return sum('000000'in p for p,op,arg in ss),sum('000000'in p and op in('CI','CD')for p,op,arg in ss)

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--iterations',type=int,default=5000);ap.add_argument('--seed',type=int,default=991);ap.add_argument('--scan',action='store_true');ap.add_argument('--basis',type=Path);a=ap.parse_args()
 if a.basis:
  t,_=v.parse_table((a.basis/'candidate225.klabels.tm').read_bytes());root=c.tree(json.loads((a.basis/'sites225.json').read_text()))
 lr=labeled(t,root);out=Path(__file__).parent
 if a.scan:
  print('extra',len(extra_rotations(t,lr)))
  for rot in extra_rotations(t,lr):
   tt,lrr=rotate_extra(t,lr,rot);tt,lrr,rec=gc_quotient(tt,lrr)
   bad=bad_mapping(tt,lrr);zs=zeros(lrr);hits,score=folds(tt)
   print(rot,'n',len(tt)//2,'bad',len(bad),'z6',zs,'hits',hits,'score',score,flush=True)
  raise SystemExit
 rng=random.Random(a.seed);base=t;base_lr=lr;history=[];bad=set();n=len(t)//2;zz=zeros(lr)[0];curcost=zz/8
 accepted=0;valid=0;tic=time.monotonic();seen=set();best=(225,48);bestscore=0
 for step in range(a.iterations):
  if step%300==0:t=base;lr=base_lr;history=[];bad=set();n=len(t)//2;zz=zeros(lr)[0];curcost=zz/8
  rs=rotations(t,lr)
  if n<227:rs+=extra_rotations(t,lr)
  rot=rng.choice(rs);tt,lrr=rotate_extra(t,lr,rot);tt,lrr,gc=gc_quotient(tt,lrr);key=tuple(sorted(tt.items()))
  if key in seen:continue
  seen.add(key);nn=len(tt)//2
  if nn>227:continue
  newbad=bad_mapping(tt,lrr)
  if len(newbad)>6:continue
  metrics=c.metrics(unlabel(lrr));znew=zeros(lrr)[0]
  if metrics['maximum_zero_run']>7:continue
  cost=len(newbad)*2+(nn-225)*1.5+znew/8
  if cost>curcost and rng.random()>math.exp((curcost-cost)/1.3):continue
  t,lr,bad,n,zz,curcost=tt,lrr,newbad,nn,znew,cost;history.append(dict(rotation=rot,gc=gc));accepted+=1
  if not bad and metrics['maximum_zero_run']<=6:
   valid+=1;hits,score=folds(t)
   if (n,zz)<best or(score>bestscore and n<=225):
    best=min(best,(n,zz));bestscore=max(bestscore,score)
    print('BEST',step,'n',n,'z6',zz,'score',score,'history',history,flush=True)
    stamp=f'best_clone_{a.seed}';(out/(stamp+'.tm')).write_bytes(encode(t));c.dump(out/(stamp+'_sites.json'),c.sites(unlabel(lr)));c.dump(out/(stamp+'_history.json'),history)
   if n<=224 or n<=225 and zz==0:
    stamp=f'candidate_clone_{a.seed}_{step}';(out/(stamp+'.tm')).write_bytes(encode(t));c.dump(out/(stamp+'_sites.json'),c.sites(unlabel(lr)));c.dump(out/(stamp+'_history.json'),history);print('CANDIDATE',stamp,'n',n,'z6',zz,flush=True);raise SystemExit
   for q0,q1,h0,h1 in hits:
    final={(q,b):(w,d,q1 if z==q0 else z)for(q,b),(w,d,z)in t.items()if q!=q0};final[q1,0]=(0,-1,h0);final[q1,1]=(1,-1,h1)
    proof=v.prove(t,final,0,0,q1,q0,0,None,8,65,20000)
    if proof['status'].startswith('PASS'):
     @c.cache
     def alias(node):return node if ll(node)else(q1 if node[0]==q0 else node[0],alias(node[1]),alias(node[2]))
     t,lr=final,alias(lr);n=len(t)//2;curcost-=1.5;history.append(dict(fold=[q0,q1,h0,h1]));print('FOLD',step,n,(q0,q1,h0,h1),flush=True)
     stamp=f'folded_clone_{a.seed}_{step}';(out/(stamp+'.tm')).write_bytes(encode(t));c.dump(out/(stamp+'_sites.json'),c.sites(unlabel(lr)));c.dump(out/(stamp+'_history.json'),history);c.dump(out/(stamp+'_foldproof.json'),proof)
     if n<=224 or n<=225 and zz==0:print('CANDIDATE',stamp,flush=True);raise SystemExit
     break
  if step%100==0:print('PROGRESS',step,'accepted',accepted,'valid',valid,'n',n,'z6',zz,'bad',len(bad),'secs',time.monotonic()-tic,flush=True)
 print('DONE',a.iterations,'accepted',accepted,'valid',valid,'seen',len(seen),'secs',time.monotonic()-tic,flush=True)
