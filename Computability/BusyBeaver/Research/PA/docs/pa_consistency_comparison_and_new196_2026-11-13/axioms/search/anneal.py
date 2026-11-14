from support import *
import math,random,time
pair=(INC,INC);quad=(pair,pair);c.MACROS[pair]=99;c.MACROS[quad]=190
random.seed(5678882)
def cost(t):
 h,l,m,mi,_=attrs(t);choices=list(nodes(t));rows,index,shape=c.build(t);n=len(shape);ops=c.opportunities_fast(rows,shape);optim=len(c.max_matching(ops));penalty=3*bad(t)+3*max(0,m-6)+3*max(0,mi-5)+max(0,h-38)
 if n-optim>66 or penalty>4:return n-optim+penalty,n,optim,choices
 chosen=bestcompatible_all(rows,shape);return n-len(chosen)+penalty,n,len(chosen),choices
pool=[(c.read_grammar(f+'.grammar.json'),f)for f in('verified196','separate196')]
seen=set(t for t,f in pool)
start=time.time();best=62;print('start',[(f,cost(t)[:3])for t,f in pool],flush=True)
for cycle in range(160):
 t,family=random.choice(pool);v,n,f,ch=cost(t)
 for j in range(1600):
  x=random.choice(ch);opts=list(rotations(x))
  if not opts:continue
  nt=repl(t,x,random.choice(opts));nv,nn,nf,nch=cost(nt);temp=.04+.48*(1-j/1600)
  if nv<=v or random.random()<math.exp((v-nv)/temp):
   t,v,n,f,ch=nt,nv,nn,nf,nch
   if v<=best:
    if v<best:
     best=v;print('NEW',best,n,f,family,'cycle',cycle,'iteration',j,'seconds',time.time()-start,flush=True);Path('allcost_'+str(v)+'.grammar.json').write_text(json.dumps(encode(t),indent=2));Path('allcost_'+str(v)+'.family.txt').write_text(family)
    if t not in seen and len(pool)<100 and random.random()<.1:
     seen.add(t);pool.append((t,family));Path('alltie_'+str(len(pool))+'.grammar.json').write_text(json.dumps(encode(t),indent=2))
    if v<=61:
     rows,idx,sh=c.build(t);cho=bestcompatible_all(rows,sh);rr,ali=apply(rows,cho);ss,ins,cs=c.source(t);check=c.validate(rr,cs);print('FULL CHECK',check,flush=True)
     if check['ok']:
      Path('candidate195.grammar.json').write_text(json.dumps(encode(t),indent=2));Path('candidate195.folds.json').write_text(json.dumps(cho,indent=2));Path('candidate195.family.txt').write_text(family);Path('candidate195.validation.json').write_text(json.dumps(check,indent=2));Path('candidate195.native.tm').write_text(''.join(f'{q} {b} {w} {"R"if d else"L"} {n}\n'for(q,b),(w,d,n)in sorted(rr.items())));raise SystemExit()
 print('cycle',cycle,'best',best,'current',v,n,f,'pool',len(pool),'seconds',time.time()-start,flush=True)
