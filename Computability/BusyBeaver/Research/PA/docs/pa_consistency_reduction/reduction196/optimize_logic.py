"""Safe logical/presentation dimensions beyond mere AX bracketing."""
from optimize_antecedents import *

def rewrite_gate(ast,exchange=False,rename=False):
 if exchange:
  tag,inside,one=ast;tag2,a,bc=inside;tag3,b,c=bc
  assert tag==tag2==tag3==0 and one==1
  ast=(0,(0,b,(0,a,c)),1)
 if rename:
  def rec(q):
   if isinstance(q,str):return {'H':'A','A':'H'}.get(q,q)
   if isinstance(q,int):return q
   z,a,b=q;return z,rec(a),rec(b)
  ast=rec(ast)
 return ast

def recode_ast(ast,flipM,flipE):
 if isinstance(ast,(str,int)):return ast
 tag,a,b=ast;a=recode_ast(a,flipM,flipE);b=recode_ast(b,flipM,flipE)
 if(tag==1 and flipM)or(tag==3 and flipE):a,b=b,a
 return tag,a,b

def replace_word(t,word):
 it=iter(word)
 def go(q):return next(it)if isinstance(q,str)else(go(q[0]),go(q[1]))
 out=go(t)
 try:next(it);raise AssertionError('too many tokens')
 except StopIteration:return out

def change(t,order,flipM=False,flipE=False,exchange=False,rename=False):
 word=expand(t);new=word[:18];offset=18
 for i in order:
  last=offset+SIZES[i];ast=expression(word[offset:last]);ast=recode_ast(ast,flipM,flipE)
  new+=code(ast);offset=last
 gate=expression(word[offset:-3]);gate=recode_ast(gate,flipM,flipE);gate=rewrite_gate(gate,exchange,rename)
 new+=code(gate)+word[-3:];assert len(new)==len(word)
 return replace_word(t,new)

def main():
 budget=int(sys.argv[1])if len(sys.argv)>1 else 400000
 rng=random.Random(int(sys.argv[2])if len(sys.argv)>2 else 205197)
 base=tree('x67');order0=tuple(range(6));best=196;start=time.monotonic()
 designs={}
 for fm in[False,True]:
  for fe in[False,True]:
   for gx in[False,True]:
    d=(fm,fe,gx);t=change(base,order0,fm,fe,gx);s=O.evaluate(t)[0]
    designs[d]=[s,t,order0,[(t,order0)]]
    print('DESIGN',d,s,len(nodes(t)),flush=True)
 seen=set();dkeys=list(designs)
 for it in range(budget):
  if it%5000==0:
   d=dkeys[(it//5000)%len(dkeys)];score,t,order,ties=designs[d]
   t,order=rng.choice([(t,order)]+ties[-20:]);score=O.evaluate(t)[0]
  neworder=order;u=rng.random()
  if u<.015:cand,neworder=O.headswap(t,order,rng)
  elif u<.05:cand=change(t,order,rename=True)
  elif u<.10:cand=antecedent_change(t,order,rng)
  elif u<.17:cand=O.parameter_change(t,order,rng)
  else:
   cand=t
   for _ in range(2 if rng.random()<.15 else 1):
    p,q=rng.choice(paths(cand));a,b=q
    if rng.randrange(2):
     if not isinstance(a,tuple):continue
     u,v=a;alt=(u,(v,b))
    else:
     if not isinstance(b,tuple):continue
     u,v=b;alt=((a,u),v)
    cand=replace(cand,q,alt)if rng.random()<.75 else replace_one(cand,p,alt)
  if cand in seen:continue
  seen.add(cand)
  if len(nodes(cand))>85:continue
  s,n,c,ds=O.evaluate(cand)
  temp=.9*(1-(it%5000)/5000)+.1
  if s<1000 and(s<=score or rng.random()<math.exp((score-s)/temp)):t=cand;order=neworder;score=s
  if s<=designs[d][0]:
   if s<designs[d][0]:
    designs[d]=[s,cand,neworder,[]]
    print('DESIGN_BEST',d,s,n,c,it,round(time.monotonic()-start,1),flush=True)
   designs[d][3].append((cand,neworder))
   if len(designs[d][3])>100:designs[d][3].pop(rng.randrange(80))
  if s<best:
   best=s
   print('BEST',best,n,c,neworder,'design',d,'iteration',it,'seconds',round(time.monotonic()-start,1),flush=True)
   path=Path(__file__).with_name(f'logic_safe_{s}_{it}.json');O.output(cand,neworder,path)
   data=json.loads(path.read_text());data['global_M_reversed']=d[0];data['global_E_reversed']=d[1];data['gate_exchange']=d[2]
   path.write_text(json.dumps(data,indent=2));print('TARGET',path.name,ds,flush=True)
   if s<=194:break
  if it%10000==0:print('progress',it,'best',best,'current',score,'design',d,'seconds',round(time.monotonic()-start,1),flush=True)
 print('DONE','best',best,'visited',len(seen),'designs',[(d,v[0])for d,v in designs.items()],'seconds',round(time.monotonic()-start,1),flush=True)
if __name__=='__main__':main()
