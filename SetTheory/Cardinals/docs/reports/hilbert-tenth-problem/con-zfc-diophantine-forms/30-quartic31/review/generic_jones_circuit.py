if not __debug__: raise SystemExit('Optimized Python is not permitted: assertions are audit checks.')
"""Fresh parameterized binary circuit for the displayed Jones nine-variable formulas.
Newly authored; reads coefficient recipes as inert JSON. Uses shared powers and
sparse Horner arithmetic, not upstream Python code.
"""
from pathlib import Path
from functools import lru_cache
import json,random
from optimize_nine_circuit import Circuit,evaluate,audit_body
BASE=Path(__file__).resolve().parent

def construct(constants):
 d=Circuit();names={};nu=constants['nu'];L=5**(nu+1);assert L==constants['L']
 c=d.const
 def add(*xs):
  v=c(0)
  for x in xs:v=d.add(v,x)
  return v
 def mul(*xs):
  v=c(1)
  for x in xs:v=d.mul(v,x)
  return v
 def sub(a,b):return d.op('sub',a,b)
 @lru_cache(None)
 def power(a,n):
  if n==0:return c(1)
  if n==1:return a
  v=power(a,n//2);v=mul(v,v)
  return mul(v,a) if n%2 else v
 def save(k,v):names[k]=v;return v
 variables=['epsilon','g0','h0','s0','w0','phi','i0','j0','n'];v={x:d.leaf('variable',name=x) for x in variables};z=d.leaf('fixed',name='z_index');yi=d.leaf('fixed',name='y_index')
 b=save('b',add(yi,c(1),v['epsilon']));B=save('B',power(b,5));g,h,s,w,i,j=(add(v[x],c(1)) for x in ('g0','h0','s0','w0','i0','j0'))
 p5=[B]
 for _ in range(nu+1):p5.append(power(p5[-1],5))
 @lru_cache(None)
 def digit_run(lo,hi,digit):
  x=power(p5[lo],digit)
  return x if hi==lo+1 else mul(x,digit_run(lo+1,hi,digit))
 @lru_cache(None)
 def Tpow(n):
  if n==0:return c(1)
  digits=[]
  while n:digits.append(n%5);n//=5
  lo=0;acc=c(1)
  while lo<len(digits):
   digit=digits[lo]
   if digit==0:lo+=1;continue
   hi=lo+1
   while hi<len(digits) and digits[hi]==digit:hi+=1
   acc=mul(acc,digit_run(lo,hi,digit));lo=hi
  return acc
 q=save('q',p5[nu+1]);ell=save('ell',add(*p5[1:nu+1]))
 # S_(5^(nu+1))(B)=product_j(1+p_j+...+p_j^4).
 geom=c(1)
 for pj in p5[:nu+1]:geom=mul(geom,add(mul(add(c(1),pj),add(c(1),power(pj,2))),power(pj,4)))
 lam=save('lambda',mul(geom,add(c(1),q),add(c(1),power(q,2))))
 gap=[c(1)]*(nu+1)
 for k in range(nu-1,-1,-1):gap[k]=mul(gap[k+1],power(p5[k],4))
 hs=[c(1)]+[c(0)]*4
 for weight in [p5[nu]]+gap:
  for k in range(1,5):hs[k]=add(hs[k],mul(weight,hs[k-1]))
 base=mul(p5[nu],hs[4])
 terms=sorted(((L-r['expo'],r['name']) for r in constants['coefficient_records']),reverse=True)
 assert terms
 exp,name=terms[0];correction=d.leaf('fixed',name=name)
 for ee,name in terms[1:]:correction=add(mul(correction,Tpow(exp-ee)),d.leaf('fixed',name=name));exp=ee
 correction=mul(correction,Tpow(exp));e=save('e',add(mul(z,base),correction))
 theta=sub(B,mul(c(2),z));N=save('N',power(q,16));Gcap=save('Gcap',mul(c(32),b,p5[nu]))
 rleft=add(g,mul(e,power(q,3)),mul(ell,power(q,5)),mul(add(mul(c(2),sub(e,mul(z,lam)),power(add(c(1),B,g),4)),mul(lam,B),mul(lam,B,power(q,4))),power(q,7)))
 rright=add(sub(power(q,3),mul(b,ell)),ell,mul(theta,lam,power(q,3)),mul(sub(B,c(2)),power(q,8)))
 R=save('R',add(mul(rleft,sub(power(N,2),N)),mul(rright,sub(power(N,2),c(1)))))
 U=save('U',mul(power(N,2),w));Y=save('Y',mul(power(N,2),s));M=save('M',mul(R,Y));P=save('P',mul(c(2),power(M,2),U));K=save('K',add(R,c(1),mul(h,sub(P,c(1)))))
 A=save('A',mul(M,add(U,c(1))));Bp=add(mul(c(2),R),c(1));Ws=save('Wsmall',mul(b,w));C=save('C',add(Bp,Ws,v['phi']));J=save('J',sub(mul(c(4),A),c(5)))
 Q=save('Q',sub(mul(c(3),Ws,C),mul(c(2),sub(power(Ws,2),c(1)))));D=save('D',add(mul(sub(power(A,2),c(1)),power(C,2)),c(1)));E=save('E',mul(i,J,D,power(C,2)));F=save('F',add(mul(sub(power(A,2),c(1)),power(E,2)),c(1)))
 Gp=save('Gp',add(A,mul(F,sub(add(mul(C,D),c(1)),A))));H=save('H',add(Bp,mul(j,C)));I=save('I',add(mul(sub(power(Gp,2),c(1)),power(H,2)),c(1)))
 a0=save('a0',add(mul(sub(power(P,2),c(1)),power(K,2)),c(1)));a1=save('a1',mul(D,F,I));div=save('divisor',power(mul(J,F),2));dvnd=save('dividend',power(add(mul(Q,F),mul(J,sub(H,C))),2))
 margin=save('margin',sub(sub(mul(power(K,2),Gcap),mul(c(4),power(sub(C,mul(K,Y)),2),Gcap)),mul(c(8),g,power(K,2))))
 V0=save('V0',add(power(P,2),power(K,2),c(2)));V1=save('V1',add(mul(add(power(A,2),power(C,2),c(1)),add(power(A,2),power(E,2),c(1)),add(power(Gp,2),power(H,2),c(1))),c(1)))
 W=save('W',mul(div,sub(mul(c(2),margin),c(1))));T=save('T',sub(add(mul(div,v['n']),dvnd),mul(W,add(dvnd,mul(V0,V1)))))
 output=save('output',sub(power(sub(power(T,2),mul(power(W,2),add(a0,mul(power(V0,2),a1)))),2),mul(c(4),power(W,4),power(V0,2),a0,a1)))
 packet=d.pack(output,names);packet.update(nu=nu,L=L,weights='majorant',model='Binary +,-,*; constants free, scalar multiplication charged; comparisons and reuse free.',construction='Fresh parameterized Jones formulas; sparse Horner; radix-five runs; factored geometric sum.')
 return packet

def main():
 con=json.loads((BASE/'18-jones9/nine/generated/constants.json').read_text());old=json.loads((BASE/'18-jones9/nine/generated/nine_majorant_dag.json').read_text());new=construct(con);rng=random.Random(20261023);count=0
 for p in (101,1009,65537,1000000007):
  for _ in range(16):
   fixed={n['name']:rng.randrange(p) for n in old['nodes'] if n['kind']=='fixed'};variables={n:rng.randrange(p) for n in old['variables']};a=evaluate(old,fixed,variables,p);b=evaluate(new,fixed,variables,p)
   for name in old['named_nodes']:assert a[old['named_nodes'][name]]==b[new['named_nodes'][name]],name;count+=1
 path=BASE/'nine_optimized/nine_generic32_majorant.json';path.write_text(json.dumps(new,separators=(',',':'))+'\n');receipt=audit_body(new);receipt['named_node_comparisons']=count;(BASE/'nine_optimized/GENERIC_AUDIT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
