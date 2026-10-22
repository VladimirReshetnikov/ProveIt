"""Owned independent finite count and layout checks. Reads downloaded JSON as data only."""
import json
from collections import Counter,defaultdict
from pathlib import Path
ROOT=Path(__file__).parent
rows=json.loads((ROOT/'sources/k215_transitions.json').read_text())['transitions']
table={(q,b):(w,d,nq) for q,b,w,d,nq in rows}
table[215,0]=(0,0,215); table[215,1]=(1,0,215)
L,Q,R,V,H=434,435,436,437,438

def decode(x):
 if x<434:
  z,b=divmod(x,2);return (b,None if z==0 else z-1,None)
 if x in (L,Q,R):return(0,0 if x==Q else None,x)
 return(None,None,None)
dec=[decode(x) for x in range(439)]
phases={(L,L),(L,Q),(Q,R),(R,R)}
classes=defaultdict(list)
for c in range(439):
 b,q,p=dec[c]
 key=('boundary',c) if c in (V,H) else ('phase',c) if p is not None else ('headless',b) if q is None else ('halt',b) if q==215 else ('working',table[q,b][:2])
 classes[key].append(c)
assert len(classes)==13
incomingL=[None if dec[x][1] is None or table[dec[x][1],dec[x][0]][1]!=1 else table[dec[x][1],dec[x][0]][2] for x in range(439)]
incomingR=[None if dec[x][1] is None or table[dec[x][1],dec[x][0]][1]!=-1 else table[dec[x][1],dec[x][0]][2] for x in range(439)]
by_payload=defaultdict(list)
for x,(b,q,p) in enumerate(dec):
 if x not in(V,H):by_payload[b,q].append(x)

def follows(l,c,r,shape):
 # All exact centered constraints that do not refer to the prior-time cell.
 b,q,p=dec[c]
 if c==V:
  return 0 if r==V else 1
 if r!=V and (c==H)!=(r==H):return 0
 if c==H:return 3 if shape=='T4' else 437
 if p is not None:
  if (l==V and p!=L) or (r==V and p!=R):return 0
  if r!=V and (p,dec[r][2]) not in phases:return 0
 if q is not None:
  move=table[q,b][1]
  if move==-1 and l==V or move==1 and r==V:return 0
 count=int(q is None or q==215) # next H, no payload update.
 if l==H or r==H:return count
 arrivals=[x for x in (incomingL[l], q if q==215 else None,incomingR[r]) if x is not None]
 if len(arrivals)>1:return count
 outb=b if q is None else table[q,b][0]
 outq=arrivals[0] if arrivals else None
 # T4 puts initialization control on the outgoing temporal edge.
 count += 1 if shape=='T4' else len(by_payload[outb,outq])
 return count

def count_all(shape,single_head):
 result={}
 for key,cs in classes.items():
  c=cs[0]; n=0
  for l in range(439):
   if single_head and (dec[l][1] is not None)+(dec[c][1] is not None)>1:continue
   for r in range(439):
    if single_head and sum(dec[x][1] is not None for x in (l,c,r))>1:continue
    n+=follows(l,c,r,shape)
  prior=1 if shape=='T4' else 439 if c in(V,H) else 1 if c in(L,Q,R) else 438
  result[str(key)]={'centers':len(cs),'per_center':n*prior,'total':n*prior*len(cs)}
 return {'shape':shape,'single_head':single_head,'total':sum(x['total'] for x in result.values()),'classes':result}

def layout(k,copies,groups):
 a=439;ell=max(2,(k+1).bit_length())
 # pc(mu)=ell+copies*a+3+p; m=2pc(mu)+groups*a+2.
 mbase=2*ell+(2*copies+groups)*a+8
 p=max(0,(k+copies*a+4-mbase+1)//2)
 m=mbase+2*p;jmax=copies*a+4+p;npos=m+1;nd=npos-k-copies*a-4
 M=k+15*a+nd;emax=27*M;Hc=emax+24*M+3*a+1
 t1=Hc+2*emax+a+1;t2=t1+2*emax+4
 U=4*(npos+2)*(2*(copies+5)*(k+copies*a+4)+6)+8
 bmin=max(ell*(jmax+1)+3,ell*(copies*a+4)+U.bit_length()+1,4)
 b=1;be=0
 while b<bmin:b*=5;be+=1
 Lcell=1;le=0
 while Lcell<t2+2*emax+2:Lcell*=5;le+=1
 return dict(k=k,ell=ell,p=p,m=m,jmax=jmax,npos=npos,nd=nd,M=M,Emax=emax,Hc=Hc,T1=t1,T2=t2,bmin=bmin,b=b,b_exponent=be,L=Lcell,L_exponent=le,d=b*Lcell,d_exponent=be+le)

if __name__=='__main__':
 out=[]
 for shape in('cross5','T4'):
  for sh in(False,True):
   r=count_all(shape,sh);r['layout']=layout(r['total'],5 if shape=='cross5' else 4,4 if shape=='cross5' else 3);out.append(r)
 assert out[0]['total']==38256607897
 (ROOT/'cross_count_receipt.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps([{k:r[k] for k in ('shape','single_head','total','layout')} for r in out],indent=2))
