from support import *
import random,math,time
pair=(INC,INC);c.MACROS[pair]=99;c.MACROS[(pair,pair)]=190
@lru_cache(None)
def leaves(t):
 if isinstance(t,str):return leaves(raw[t])
 return leaves(t[0])+leaves(t[1]) if c.isnode(t) else 1
@lru_cache(None)
def scanner_bad(t,k=0):
 if k>=6:return leaves(t)
 if isinstance(t,str):return scanner_bad(raw[t],k)
 return scanner_bad(t[0],k+1)+scanner_bad(t[1],0)if c.isnode(t)else 0

def cost(t):
 h,l,m,mi,_=attrs(t);r,idx,sh=c.build(t);ops=c.opportunities_fast(r,sh);lower=len(sh)-len(c.max_matching(ops))
 eff=len(sh)-len(bestcompatible_all(r,sh)) if lower<=65 else lower
 bc=scanner_bad(t);pen=50*(bad(t)+max(0,m-6)+max(0,mi-5))+max(0,h-38)
 return bc+8*max(eff-62,0)+pen,eff,bc,list(nodes(t)),pen
random.seed(799138)
starts=sorted((scanner_bad(c.read_grammar(p)),str(p))for p in Path('ties').glob('alltie_*.grammar.json'))[:10]
pool=[c.read_grammar(p) for b,p in starts];seen=set(pool);best=min(b for b,p in starts);start=time.time()
print('START',starts,'budget',30,1000,flush=True)
for cycle in range(30):
 t=random.choice(pool);v,eff,bc,ns,pen=cost(t)
 for j in range(1000):
  x=random.choice(ns);rot=list(rotations(x))
  if not rot:continue
  nt=repl(t,x,random.choice(rot));nv,ne,nb,nn,np=cost(nt);temp=.1+1.2*(1-j/1000)
  if nv<=v or random.random()<math.exp((v-nv)/temp):
   t,v,eff,bc,ns,pen=nt,nv,ne,nb,nn,np
   if eff<=62 and pen==0:
    if bc<best:
     best=bc;print('BEST',best,'eff',eff,'cycle',cycle,'j',j,'sec',time.time()-start,flush=True);Path('scanner_'+str(best)+'.grammar.json').write_text(json.dumps(encode(t),indent=2))
    if bc<=best+1 and t not in seen and len(pool)<70:pool.append(t);seen.add(t)
    if bc==0 or eff<=61:
     r,idx,sh=c.build(t);ch=bestcompatible_all(r,sh);rr,ali=apply(r,ch);ss,ins,cs=c.source(t);check=c.validate(rr,cs);print('FULL',eff,bc,check,flush=True)
     if check['ok']:
      Path('scanner_candidate.grammar.json').write_text(json.dumps(encode(t),indent=2));Path('scanner_candidate.folds.json').write_text(json.dumps(ch,indent=2));Path('scanner_candidate.validation.json').write_text(json.dumps(check,indent=2));Path('scanner_candidate.native.tm').write_text(''.join(f'{q} {b} {w} {"R"if d else"L"} {n}\n'for(q,b),(w,d,n)in sorted(rr.items())));Path('scanner_candidate.sites.json').write_text(json.dumps([{'ordinal':i,'path':''.join(map(str,p)),'op':op,'arg':a,'instruction':ins[i]}for i,(p,op,a)in enumerate(ss)],indent=2));raise SystemExit()
 print('cycle',cycle,'best',best,'current',eff,bc,'pool',len(pool),'sec',time.time()-start,flush=True)
