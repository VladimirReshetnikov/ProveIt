"""Independent literal T4 predicate, full filtered alphabet, geometry, and seams.
Only input is literal transition JSON. No downloaded program is imported or run.
"""
import hashlib,itertools,json
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).parent
rows=json.loads((ROOT/'sources/k215_transitions.json').read_text())['transitions']
delta={(q,b):(w,d,nq) for q,b,w,d,nq in rows};delta.update({(215,b):(b,0,215) for b in (0,1)})
L,Q,R,V,H=434,435,436,437,438
PSET={(L,L),(L,Q),(Q,R),(R,R)}
def data(x):
 if x<434:
  v,b=divmod(x,2);return b,None if v==0 else v-1,None
 if x in(L,Q,R):return 0,0 if x==Q else None,x
 return None,None,None
D=[data(x) for x in range(439)]
HEADLESS=[x for x in range(439) if D[x][1] is None]
HEADED=[x for x in range(439) if D[x][1] is not None]

def valid(w,transition=delta):
 l,c,r,n=w
 if sum(D[x][1] is not None for x in (l,c,r))>1:return False
 if (c==V)!=(n==V) or c==V and r==V or c==H and n==H:return False
 if c!=V and r!=V and (c==H)!=(r==H):return False
 if c==V:return True
 if c==H:return D[n][2] is not None
 b,q,p=D[c]
 if p is not None:
  if l==V and p!=L or r==V and p!=R:return False
  if r!=V and (p,D[r][2]) not in PSET:return False
 if q is not None:
  _,move,_=transition[q,b]
  if move==-1 and l==V or move==1 and r==V:return False
 if n==H:return q is None or q==215
 if D[n][2] is not None or l==H or r==H:return False
 expected_b=b if q is None else transition[q,b][0]
 arrivals=[]
 for x,move in((l,1),(c,0),(r,-1)):
  bx,qx,_=D[x]
  if qx is not None and transition[qx,bx][1]==move:arrivals.append(transition[qx,bx][2])
 return len(arrivals)<=1 and D[n][:2]==(expected_b,arrivals[0] if arrivals else None)

def enumerate_windows():
 # Exhaust precisely all triples surviving the head filter, with every successor.
 triples=set(itertools.product(HEADLESS,repeat=3))
 for pos in range(3):
  for head in HEADED:
   for a,b in itertools.product(HEADLESS,repeat=2):
    w=[a,b];w.insert(pos,head);triples.add(tuple(w))
 out=[]
 for triple in sorted(triples):
  for n in range(439):
   w=triple+(n,)
   if valid(w):out.append(w)
 start=(L,Q,R,1);forbidden=(H,0,0,H)
 assert start in out and forbidden in out
 out.remove(start);out.remove(forbidden)
 return [start,forbidden]+out,len(triples)

def geometry(windows):
 k=len(windows);a=439;ell=(k+1).bit_length();base=2*ell+11*a+8
 p=max(0,(k+4*a+4-base+1)//2);m=base+2*p
 nd=m+1-k-4*a-4;es=k+12*a;M=k+15*a+nd
 emax=27*M;Hc=51*M+3*a+1;t1=Hc+2*emax+a+1;t2=t1+2*emax+4
 assert emax%2==1
 coordinates=((1,0),(1,1),(1,2),(2,1))
 def e(rc,s):
  r,c=rc;return k+3*a+(2-r)*3*a+(2-c)*a+s
 copies={e(rc,s) for rc in coordinates for s in range(a)}
 anchors={M,3*M,9*M,27*M}
 support=set(range(k))|copies|set(range(es,es+nd))|anchors
 assert len(support)==m+1
 Lcell=1
 while Lcell<t2+2*emax+2:Lcell*=5
 bmin=max(ell*(4*a+5+p)+3,ell*(4*a+4)+(4*(m+3)*(18*(k+4*a+4)+6)+8).bit_length()+1,4)
 b=1
 while b<bmin:b*=5
 expand=support|{es+1}
 assert not ({(t1-e)%Lcell for e in expand}&{(t2-e)%Lcell for e in expand})
 assert {(9*M-e)%Lcell for e in support}&{(27*M-e)%Lcell for e in support}=={0}
 bare=(3*a,Hc+a,8*M,24*M)
 target=[]
 for s in range(a):
  target.append((e((1,1),s),{e((2,1),s)},set(),{e((1,1),s)}))
  for rc,src in(((1,0),(1,1)),((1,1),(1,2))):
   target.append((Hc+e(rc,s),{e(src,s)},{e(rc,s)},set()))
 target += [(9*M,{M},set(),{9*M}),(27*M,{3*M},set(),{27*M})]
 assert len({t for t,*_ in target})==3*a+2
 for t,at0,at1,at2 in target:
  assert {t-v for v in bare if t-v in support}==at0
  assert ({t-Hc} if t-Hc in support else set())==at1
  assert ({t} if t in support else set())==at2
  assert t<t1-emax # no clause term can reach these target positions.
 for t,other in((t1,t2),(t2,t1)):
  assert not {t-v for v in bare}&support
  assert all(other+x-t not in support for x in support)
 # Exact all-enumeration mod-5 test without any huge numeral expansion.
 # c_i=1+sum A^j over four payloads + four anchors; c_copy and c_anchor=A^j.
 A5=pow(2,ell,5)
 coeff={}
 for i,w in enumerate(windows):
  coeff[i]=(1+sum(pow(A5,1+j*a+s,5) for j,s in enumerate(w))+sum(pow(A5,4*a+t,5) for t in range(1,5)))%5
 for j,rc in enumerate(coordinates):
  for s in range(a):coeff[e(rc,s)]=pow(A5,1+j*a+s,5)
 for j,x in enumerate((M,3*M,9*M,27*M),1):coeff[x]=pow(A5,4*a+j,5)
 dc=(sum(pow(2,x,5) for x in bare)+sum(v*(pow(2,t1-x,5)+pow(2,t2-x,5)) for x,v in coeff.items()))%5
 assert (2*dc-pow(2,Hc,5))%5==3
 # Exact manageable integer checks: mu is only 299889 bits; these are not final coefficients.
 A=1<<ell
 mu=A-2+(pow(A,4*a+5+p)-A)//(A-1)
 census=Counter((j,s) for w in windows for j,s in enumerate(w))
 sum_v=k+sum((census[j,s]+1)*pow(A,1+j*a+s) for j in range(4) for s in range(a))+sum((k+1)*pow(A,4*a+t) for t in range(1,5))
 mass=(len(support)+2)*(2*sum_v+6)
 assert mu.bit_count()==18758 and 2*mu.bit_count()+3*a+2==m
 assert 4*mass+8 < (1<<b) and 2*mu+4 < (1<<b)
 assert t2+2*emax+2<=Lcell and t2-t1>2*emax and (t2-t1)%4==2
 return dict(mu_bit_length=mu.bit_length(),mu_population=mu.bit_count(),clause_mass_bit_length=sum_v.bit_length(),carry_threshold_bit_length=(4*mass+8).bit_length(),k=k,ell=ell,p=p,m=m,dummy_count=nd,dummy_start=es,M=M,Emax=emax,Hc=Hc,T1=t1,T2=t2,bmin=bmin,b=b,L=Lcell,d=b*Lcell,native_support=len(support),target_positions=len(target),mod5_unit=3,band_and_anchor_all_rotation_checks=True,convolution_target_checks=True)

def seam_checks():
 checked=0
 for control in(0,1):
  tr=dict(delta)
  tr[93,0]=(0,0,215) if control==0 else (1,-1,2)
  tr[2,1]=(0,-1,3);tr[3,0]=(1,1,215)
  tape={};head=state=0;history=[]
  for _ in range(10):
   history.append((dict(tape),head,state))
   if state==215:break
   write,move,state=tr[state,tape.get(head,0)];tape[head]=write;head+=move
  assert history[-1][2]==215
  lm=max(2,2-min(h for _,h,_ in history));rm=max(2,2+max(h for _,h,_ in history))
  for dw,dh in itertools.product(range(3),repeat=2):
   width=lm+rm+2+dw;height=len(history)+1+dh;xs=lm+1
   grid=[]
   for y in range(height):
    row=[V]
    for x in range(1,width):
     if y==0:cell=H
     elif y==1:cell=L if x<xs else Q if x==xs else R
     else:
      tape,head,state=history[min(y-1,len(history)-1)];pos=x-xs
      cell=tape.get(pos,0)+(2*(state+1) if pos==head else 0)
     row.append(cell)
    grid.append(row)
   word=[None]*(width*height)
   for y,row in enumerate(grid):
    for x,v in enumerate(row):word[(-(x-xs)-width*(y-1))%len(word)]=v
   windows=[(word[(i+1)%len(word)],word[i],word[(i-1)%len(word)],word[(i-width)%len(word)]) for i in range(len(word))]
   assert all(valid(w,tr) for w in windows)
   assert windows[0]==(L,Q,R,1) and windows.count((L,Q,R,1))==1
   assert (H,0,0,H) not in windows
   checked+=len(windows)
 return checked

if __name__=='__main__':
 windows,triples=enumerate_windows();assert len(windows)==37075
 dest=ROOT/'t4_windows.json';dest.write_text(json.dumps(windows,separators=(',',':'))+'\n')
 result={'status':'PASS','window_count':len(windows),'horizontal_triples_exhausted':triples,'quadruples_checked':triples*439,'windows_sha256':hashlib.sha256(dest.read_bytes()).hexdigest(),'geometry':geometry(windows),'toy_helical_windows_checked':seam_checks(),'scope':'Finite exact data and geometry checks; not an end-to-end formal proof or test of K215 halting.'}
 (ROOT/'t4_verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

