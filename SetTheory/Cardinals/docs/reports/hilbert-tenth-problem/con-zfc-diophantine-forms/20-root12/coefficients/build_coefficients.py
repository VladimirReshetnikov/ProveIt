"""Independent exact T4 collar/preimage alphabet and binary-copy compiler.
No final giant integer is expanded. Only literal K215 transition JSON is read.
"""
import collections, hashlib, itertools, json, math
from pathlib import Path
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT/'sources/k215_transitions.json'
assert hashlib.sha256(SOURCE.read_bytes()).hexdigest()=='880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755'
rows=json.loads(SOURCE.read_text())['transitions']
delta={(q,b):(w,d,nq) for q,b,w,d,nq in rows}
pred=collections.defaultdict(set)
for q,b,w,d,nq in rows:pred[nq].add((d,w))
delta.update({(215,b):(b,0,215) for b in(0,1)})
L,Q,R,V,H=434,435,436,437,438
START=(L,Q,R,1); EXCLUDED=(H,0,0,H)
PHASES={L,Q,R};PAIRS={(L,L),(L,Q),(Q,R),(R,R)}
def data(x):
 if x<434:return x%2,None if x<2 else x//2-1,None
 if x in PHASES:return 0,0 if x==Q else None,x
 return None,None,None
D=[data(x) for x in range(439)]

def horizontal(l,r):
 if l==V:return r in(0,L,H)
 if r==V:return l in(0,R,H)
 if l==H or r==H:return l==r==H
 if l in PHASES or r in PHASES:return (l,r) in PAIRS
 return True

def valid(w,transition=delta,incoming=pred):
 l,c,r,n=w
 if w==EXCLUDED:return True
 if sum(D[x][1] is not None for x in(l,c,r))>1:return False
 if not horizontal(l,c) or not horizontal(c,r) or l==r==V:return False
 if (c==V)!=(n==V) or c==H and n==H:return False
 if c==V:return True
 if c==H:return n in PHASES and (l!=V or n==L) and (r!=V or n==R)
 if c in PHASES and n==H:return False
 if c not in PHASES:
  if l==V and (r not in(0,1) or n not in(0,H)):return False
  if r==V and (l not in(0,1) or n not in(0,H)):return False
 if n==H:
  return all(x in(0,1,V,432,433) for x in(l,c,r)) and predecessor_ok((l,c,r),incoming)
 if n>=434:return False
 if not predecessor_ok((l,c,r),incoming):return False
 b,q,_=D[c]
 if q is not None:
  _,move,_=transition[q,b]
  if move==-1 and l==V or move==1 and r==V:return False
 expected_b=b if q is None else transition[q,b][0]
 arrivals=[]
 for x,m in((l,1),(c,0),(r,-1)):
  bx,qx,_=D[x]
  if qx is not None and transition[qx,bx][1]==m:arrivals.append(transition[qx,bx][2])
 return len(arrivals)<=1 and D[n][:2]==(expected_b,arrivals[0] if arrivals else None)

def predecessor_ok(triple,incoming):
 for pos,c in enumerate(triple):
  if 2<=c<434:
   if not any(not 0<=pos-m<3 or triple[pos-m]==written for m,written in incoming[c//2-1]):return False
 return True

def enumerate_tiles():
 headless=[0,1,L,R,V,H];headed=[x for x in range(439) if x not in headless]
 triples=set(itertools.product(headless,repeat=3))
 for p in range(3):
  for h in headed:
   for a,b in itertools.product(headless,repeat=2):
    w=[a,b];w.insert(p,h);triples.add(tuple(w))
 result=[]
 for l,c,r in sorted(triples):
  if (l,c,r)!=EXCLUDED[:3] and (not horizontal(l,c) or not horizontal(c,r) or l==r==V):continue
  for n in range(439):
   w=(l,c,r,n)
   if valid(w):result.append(w)
 result.remove(START);result.remove(EXCLUDED)
 return [START,EXCLUDED]+result

def old_valid(w):
 """Literal old T4 condition, independently checked on every new tuple."""
 l,c,r,n=w
 if sum(D[x][1] is not None for x in(l,c,r))>1:return False
 if (c==V)!=(n==V) or c==V and r==V or c==H and n==H:return False
 if c!=V and r!=V and (c==H)!=(r==H):return False
 if c==V:return True
 if c==H:return n in PHASES
 b,q,p=D[c]
 if p is not None:
  if l==V and p!=L or r==V and p!=R:return False
  if r!=V and (p,D[r][2]) not in PAIRS:return False
 if q is not None:
  _,m,_=delta[q,b]
  if m==-1 and l==V or m==1 and r==V:return False
 if n==H:return q is None or q==215
 if D[n][2] is not None or l==H or r==H:return False
 expected=b if q is None else delta[q,b][0]
 arrivals=[]
 for x,m in((l,1),(c,0),(r,-1)):
  bx,qx,_=D[x]
  if qx is not None and delta[qx,bx][1]==m:arrivals.append(delta[qx,bx][2])
 return len(arrivals)<=1 and D[n][:2]==(expected,arrivals[0] if arrivals else None)

def ceil5(n):
 q,e=1,0
 while q<n:q*=5;e+=1
 return q,e

def geometry(tiles):
 k=len(tiles);a=11;ell=(k+1).bit_length();A=1<<ell
 # 9 binary symbol digits, one permanent occupancy digit, one zero guard.
 def code(symbol):return [int(bool(symbol&(1<<i))) for i in range(9)]+[1,0]
 vectors=[code(s) for s in range(439)]
 assert len({tuple(v) for v in vectors})==439 and all(sum(v)>0 for v in vectors)
 copies=[k+8*a,k+7*a,k+6*a,k+4*a]
 dummy=k+12*a;M=k+15*a+1
 anchors=[M,M+a+1,M+2*a,2*M+4*a+1]
 emax=anchors[-1];s1=anchors[2]-anchors[0];s2=anchors[3]-anchors[1]
 Hc=emax+s2+3*a+1;T1=Hc+2*emax+a+1;T2=T1+2*emax+4
 E=set(range(k))|{off+t for off in copies for t in range(a)}|{dummy}|set(anchors)
 assert len(E)==k+4*a+5
 coeff={i:1+sum(A**(1+j*a+t) for j,s in enumerate(w) for t,x in enumerate(vectors[s]) if x)+sum(A**(4*a+t) for t in range(1,5)) for i,w in enumerate(tiles)}
 for j,off in enumerate(copies):
  for t in range(a):coeff[off+t]=A**(1+j*a+t)
 for t,e in enumerate(anchors,1):coeff[e]=A**(4*a+t)
 coeff[dummy]=0
 mu=A-2+sum(A**j for j in range(1,4*a+5))
 targets=[]
 for t in range(a):
  targets.append((copies[1]+t,{copies[3]+t},set(),{copies[1]+t}))
  targets.append((Hc+copies[0]+t,{copies[1]+t},{copies[0]+t},set()))
  targets.append((Hc+copies[1]+t,{copies[2]+t},{copies[1]+t},set()))
 targets.extend([(anchors[2],{anchors[0]},set(),{anchors[2]}),(anchors[3],{anchors[1]},set(),{anchors[3]})])
 bare=(3*a,Hc+a,s1,s2)
 assert len(set(bare))==4
 for target,c0,c1,c2 in targets:
  assert {target-v for v in bare if target-v in E}==c0,(target,'DC')
  assert ({target-Hc} if target-Hc in E else set())==c1,(target,'DR')
  assert ({target} if target in E else set())==c2,(target,'Y')
  assert target<T1-emax
 for t,other in((T1,T2),(T2,T1)):
  assert not({t-v for v in bare}&E)
  assert all(other+x-t not in E for x in E)
 padding_count=len(E)-(2*mu.bit_count()+3*a+3)
 assert padding_count>=0
 pad_start=T2+emax+1;pad_end=pad_start+padding_count
 Lcell,le=ceil5(max(T2+2*emax+2,pad_end+1))
 mass=(len(E)+2)*(2*sum(coeff.values())+6)
 bmin=max((4*mass+8).bit_length(),(2*mu+4).bit_length(),4)
 b,be=ceil5(bmin);rho=1<<b
 assert 4*mass+8<rho and 2*mu+4<rho
 expanded=E|{dummy+1}
 assert not({(T1-e)%Lcell for e in expanded}&{(T2-e)%Lcell for e in expanded})
 assert {(anchors[2]-e)%Lcell for e in E}&{(anchors[3]-e)%Lcell for e in E}=={0}
 assert max(bare)+emax<pad_start and Hc+emax<pad_start and emax<pad_start
 assert T2+emax<pad_start and pad_end<Lcell
 assert all(x>0 for x in bare)
 dc5=(sum(pow(2,e,5) for e in bare)+sum((v%5)*(pow(2,T1-e,5)+pow(2,T2-e,5)) for e,v in coeff.items()))%5
 unit=(2*dc5-pow(2,Hc,5))%5
 assert unit!=0
 # Exhaust selector cardinalities and individual component parity constraints.
 assert k+1<A
 assert all((n&(A-2)==0)==(n in(0,1)) for n in range(k+1))
 assert all((((x+y)&1)==0)==(x==y) for x,y in itertools.product((0,1),repeat=2))
 assert max(sum(code(s)) for s in range(439))<=10
 d=b*Lcell
 return dict(k=k,a=a,ell=ell,A=A,copy_offsets=copies,dummy=dummy,M=M,anchors=anchors,Emax=emax,Hc=Hc,T1=T1,T2=T2,bare_shifts=list(bare),support_size=len(E),mu_top=4*a+4,mu_population=mu.bit_count(),mu_bit_length=mu.bit_length(),padding_count=padding_count,padding_start=pad_start,padding_stop=pad_end,bmin=bmin,b=b,b_exponent=be,L=Lcell,L_exponent=le,d=d,d_exponent=be+le,beta_bit_length=d,K_bit_length=b*(Lcell+Hc)+1,MF_source_bit_length=d+1,MC_bit_length=d,mass_threshold_bit_length=(4*mass+8).bit_length(),mod5_unit=unit,convolution_targets=len(targets),all_rotation_anchor_check=True,all_rotation_clean_band_check=True,population_MF=2*mu.bit_count()+3*a+3+padding_count,population_MC=d-len(E))

def seam_checks():
 count=0;presentations=0
 for control in range(3):
  tr=dict(delta)
  tr[93,0]=(0,1,68) if control==0 else (1,-1,2)
  tr[2,1]=(0,-1,3);tr[3,0]=(1,1,68);tr[68,0]=(1,1,215)
  inc=collections.defaultdict(set)
  for (q,b),(w,m,t) in tr.items():
   if q!=215:inc[t].add((m,w))
  tape={};head=state=0;history=[]
  for _ in range(20):
   history.append((dict(tape),head,state))
   if state==215:break
   w,m,state=tr[state,tape.get(head,0)];tape[head]=w;head+=m
  assert history[-1][2]==215
  lm=max(3,3-min(h for _,h,_ in history));rm=max(3,3+max(h for _,h,_ in history))
  for dw,dh in itertools.product(range(4),repeat=2):
   width=lm+rm+2+dw;height=len(history)+1+dh;xs=lm+1
   word=[None]*(width*height)
   for y in range(height):
    for x in range(width):
     if x==0:cell=V
     elif y==0:cell=H
     elif y==1:cell=L if x<xs else Q if x==xs else R
     else:
      tape,head,state=history[min(y-1,len(history)-1)];pos=x-xs
      cell=tape.get(pos,0)+(2*(state+1) if pos==head else 0)
     word[(-(x-xs)-width*(y-1))%len(word)]=cell
   windows=[(word[(i+1)%len(word)],word[i],word[(i-1)%len(word)],word[(i-width)%len(word)]) for i in range(len(word))]
   assert all(valid(w,tr,inc) for w in windows)
   assert windows[0]==START and windows.count(START)==1 and EXCLUDED not in windows
   count+=len(windows);presentations+=1
 return dict(presentations=presentations,windows=count)

if __name__=='__main__':
 tiles=enumerate_tiles();assert len(tiles)==4094
 assert all(old_valid(w) for w in tiles)
 out=ROOT/'tiles4094.json';out.write_text(json.dumps(tiles,separators=(',',':'))+'\n')
 g=geometry(tiles)
 receipt=dict(status='PASS',construction='T4-4094-binary-copy-zero-padding-5pow11',source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),tiles_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),geometry=g,seams=seam_checks(),center_classes=dict(collections.Counter('headless' if w[1]<2 else 'working_head' if w[1]<432 else 'halt_head' if w[1]<434 else str(w[1]) for w in tiles)),scope='Exact finite language, geometry and arithmetic checks; ordinary mathematical compiler adapter, not a full Lean/Rocq formalization or an unbounded K215 execution.')
 (ROOT/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
 spec=dict(schema='proveit-k215-t4-binary-copy-fixed-coefficients-v1',status='Audited ordinary mathematical adapter with fully materialized numeric coefficients; no fresh end-to-end kernel proof',repository='VladimirReshetnikov/ProveIt',repository_commit='f0ae4e0991ca44a7bb4e5671d42e33d775e48035',machine='raw blank-input K215, original430 transitions plus stationary halt padding',transition_file='sources/k215_transitions.json',transition_sha256=receipt['source_sha256'],tiles_file='tiles4094.json',tiles_sha256=receipt['tiles_sha256'],scalars=g,code='chi(s)=(bit0(s),...,bit8(s),1,0)',definitions={
  'rho':'2^625','B':'rho^78125 = 2^(5^11)','A':'4096','mu':'A-2+sum(A^j,j=1..48)',
  'E':'0..4093;4182..4192;4171..4181;4160..4170;4138..4148;4226;4260,4272,4282,8565',
  'v_selector(i)':'1+sum(chi(tile_i[j])[t]*A^(1+11*j+t),j=0..3,t=0..10)+sum(A^(44+t),t=1..4)',
  'v_copy(j,t)':'A^(1+11*j+t), at copy_offsets[j]+t',
  'v_anchor(t)':'A^(44+t), at anchors[t-1],t=1..4','v_dummy':'0',
  'DC':'rho^33+rho^12903+rho^22+rho^4293+sum(v_e*(rho^(30034-e)+rho^(47168-e)),e in E)',
  'DR':'rho^12892',
  'MF0':'mu*(rho^30034+rho^47168)+sum(rho^(4171+t)+rho^(17074+t)+rho^(17063+t),t=0..10)+rho^4282+rho^8565+sum(rho^z,z=55734..59722)',
  'MC':'B-1-sum(rho^e,e in E except1)-2*rho^4226',
  'MF_native':'MF0+4','beta':'B-1','K':'DC+B*DR','MF_source':'MF_native+B-1'},polynomial_ports=['beta','K','MC','MF_source'],expanded_directory='expanded',expanded_manifest='expanded/MANIFEST.json',proof='COEFFICIENT_PROOF.md',old_beta_bit_length=5**18,new_beta_bit_length=g['d'],beta_bit_length_improvement_factor=5**7)
 spec['tuple_id']='T4-4094-binary-copy-zero-padding-5pow11'
 spec['canonical_witness_contract']={'d_and_N':'odd powers of5','R_mod4':3,'rank_population':'3*d*N+2','actual_rank_congruence':'R=d*width mod d*N','dummy_unit_mod5':1,'power_scale':'w_scale=2^(R-d*N), a positive integer square','auxiliary_multiplier':'can be chosen positive and odd by strong index c*R'}
 manifest_path=ROOT/'expanded/MANIFEST.json'
 if manifest_path.exists():
  numeric=json.loads(manifest_path.read_text())
  spec['numeric_encoding']=numeric['encoding']
  spec['numeric_coefficients']={name:dict(meta,file='expanded/'+meta['file']) for name,meta in numeric['files'].items()}
  spec['numeric_total_bytes']=numeric['sum_file_bytes']
  digest_input=''.join(numeric['files'][name]['sha256'] for name in spec['polynomial_ports']).encode('ascii')
  spec['tuple_sha256']=hashlib.sha256(digest_input).hexdigest()
  spec['tuple_sha256_definition']='SHA256 of ASCII concatenation of the four lowercase file SHA256 hex strings in polynomial_ports order'
 (ROOT/'COEFFICIENTS.json').write_text(json.dumps(spec,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
