#!/usr/bin/env python3
"""Independent exact audit of signed source216 and its four-base pools.

Does not import the producer. The unbounded sign/growth/pooling theorem is
recorded separately. Every finite source identity below is checked exactly.
"""
import json,hashlib
from pathlib import Path
from collections import defaultdict
ROOT=Path(__file__).resolve().parent.parent
SOURCE_SHA='2a8ee90a0d11eccba1956ac31d12992807a6cd2db8ef3d06cd2226d30dc196b9'
def need(b,m):
 if not b:raise ValueError(m)
def enc(o):return(json.dumps(o,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(o):return hashlib.sha256(enc(o)).hexdigest()
def P(raw):
 out={}
 for c,m in raw:
  need(type(c)is int and c!=0,'nonintegral or zero coefficient');need(type(m)is list and m==sorted(m),'bad monomial')
  need(tuple(m) not in out,'duplicate monomial');out[tuple(m)]=c
 return out
def V(i):return{(i,):1}
def C(c):return{():c}if c else{}
def add(a,b,sign=1):
 out=dict(a)
 for m,c in b.items():
  out[m]=out.get(m,0)+sign*c
  if out[m]==0:del out[m]
 return out
def mul(a,b):
 out=defaultdict(int)
 for m,c in a.items():
  for n,d in b.items():out[tuple(sorted(m+n))]+=c*d
 return{m:c for m,c in out.items()if c}
def scale(p,c):return{m:c*d for m,d in p.items()if c*d}
def product(fs):
 out=C(1)
 for f in fs:out=mul(out,f)
 return out
def sq(p):return mul(p,p)
def check(variant):
 raw=(ROOT/'source/pell216.json').read_bytes();need(hashlib.sha256(raw).hexdigest()==SOURCE_SHA,'source216 hash mismatch')
 original=json.loads(raw);parent=json.loads((ROOT/'source/signed216.json').read_bytes())
 need(len(original['variables'])==216 and len(original['residuals'])==156,'wrong original dimensions')
 expected=json.loads(raw);expected['residuals'][131]['terms']=[[-2,[]],[1,[0]],[-4,[184]]]
 expected['variables'][184]['name']='cofinal.horizon_parameter';expected['schema']='signed-pell-growth-v1'
 need(expected==parent,'signed source differs from the authorized horizon change')
 source=json.loads((ROOT/'sources'/variant/'equation.json').read_bytes());cert=json.loads((ROOT/'sources'/variant/'certificate.json').read_bytes())
 need(cert['parent_byte_sha256']==SOURCE_SHA and cert['parent_canonical_sha256']==digest(parent),'wrong parent binding')
 need(cert['equation_sha256']==digest(source),'wrong output binding')
 need(source['domain']=='unrestricted integers','wrong domain')
 need(cert['removed_variables']==[144,145,146,147,208,209,210,211],'wrong private variable deletion')
 need(cert['removed_rows']==[102,103,104,105,148,149,150,151],'wrong private row deletion')
 retained=[i for i in range(216) if i not in cert['removed_variables']]
 need(cert['retained_old_indices']==retained,'wrong index projection')
 inverse=dict(enumerate(retained));forward={v:k for k,v in inverse.items()}
 def old(raw):return {tuple(inverse[i] for i in m):c for m,c in P(raw).items()}
 rows=[P(r['terms'])for r in parent['residuals']]
 A=add(V(137),C(1));need(old(cert['A'])==A,'wrong common Pell center')
 # Bind every actual common-Pell pair, request and square-frame atom. This
 # check uses the source216 coordinates rather than names or a producer map.
 t,F=V(0),V(2);q=add(V(100),C(-1));Cindex=scale(V(16),2)
 radix=add(add(C(2),scale(F,2)),scale(V(16),4))
 pdata=[(141,142,143,t,0,0),(148,149,150,add(F,t),0,0),
  (151,152,153,add(V(8),C(-1)),-1,0),(154,155,156,V(9),0,0),
  (157,158,159,V(10),0,0),(160,161,162,V(11),0,0),
  (163,164,165,V(12),0,0),(166,167,168,V(4),0,0),
  (169,170,171,V(13),0,0),(172,173,174,V(14),0,0),
  (175,176,177,V(1),0,1),(178,179,180,V(15),0,0),
  (181,182,183,Cindex,0,0)]
 pairs=[];orient={};cap=add(add(sq(V(182)),sq(Cindex),-1),C(-1))
 cap=add(cap,add(add(sq(V(201)),sq(V(202))),mul(V(203),add(V(203),C(1)))),-1)
 for di,yi,zi,k,yo,zo in pdata:
  Dp,Yp,Zp=V(di),add(V(yi),C(yo)),add(V(zi),C(zo));Xp=add(Dp,Zp)
  norm=add(add(add(sq(Dp),scale(mul(Dp,Zp),2)),sq(Yp)),C(-1))
  need(add(Zp,mul(A,Yp),-1)in rows,'missing actual main-Pell wire')
  need(norm in rows,'missing actual main-Pell norm')
  orient=add(orient,add(add(sq(add(Xp,C(-1))),sq(add(Yp,k,-1))),norm,-1))
  if yi!=182:cap=add(cap,sq(Yp),-1)
  pairs.append((Dp,Yp,Zp,k))
 need(add(orient,mul(V(137),V(198)),-1)==rows[142],'main-Pell signed orientation mismatch')
 need(cap==rows[145],'dominant CRT anchor cap mismatch')
 atoms=[t,add(t,C(1)),add(F,t),V(1),t,V(3),F,V(4),add(V(8),C(-1))]
 atoms += [V(i)for i in range(9,16)]+[Cindex,V(17),q,V(100),radix]
 atoms += [V(i)for i in [101,102,106,109,112,115,118,119,122,125,126,130,133]]
 frame=C(2)
 for atom in atoms:frame=add(frame,sq(atom))
 need(add(V(136),frame,-1)==rows[130],'actual square-frame mismatch')
 requests=[(V(3),V(1),V(17)),(radix,V(1),q)]
 for b,positions,outputs,ki,li,ra,rb in [
  (q,[0,7,10],[102,119,126],210,211,150,151),
  (V(100),[1,2,3,4,5,6,8,9,11,12],[101,106,109,112,115,118,122,125,130,133],208,209,148,149)]:
  H={};S={}
  for pi,mi in zip(positions,outputs):
   Dp,Yp,Zp,k=pairs[pi];m=V(mi);Xp=add(Dp,Zp)
   H=add(H,mul(Yp,add(m,Xp,-1)));S=add(S,add(sq(add(m,Dp,-1)),sq(Yp),-1))
   requests.append((b,k,m))
  need(add(add(V(ki),scale(H,2),-1),mul(add(scale(A,2),b,-1),V(li)),-1)==rows[ra],'request bilinear aggregate mismatch')
  need(add(add(S,mul(b,V(ki)),-1),V(li))==rows[rb],'request square aggregate mismatch')
 need(len(atoms)==34 and len(requests)==15,'request/frame dimension mismatch')
 for request in requests:
  for atom in request:need(atom in atoms,'actual power request omitted from frame')
 specs=[(V(3),V(17),144,145,102,103),(add(add(C(2),scale(V(2),2)),scale(V(16),4)),add(V(100),C(-1)),146,147,104,105)]
 D,Y,Z=V(175),V(176),add(V(177),C(1));wire=add(Z,mul(A,Y),-1)
 need(rows[124]==wire,'shifted A*Y wire is missing')
 for i,(b,m,ti,qi,rt,rq)in enumerate(specs):
  g=cert['groups'][i];T=add(add(scale(mul(A,b),2),sq(b),-1),C(-1));delta=add(add(m,D,-1),mul(b,Y),-1)
  need(g['removed_modulus']==ti and g['removed_quotient']==qi and g['removed_rows']==[rt,rq],'singleton binding mismatch')
  for f,p in [('base',b),('m',m),('D',D),('Y',Y),('Z',Z),('T',T),('delta',delta),('Y_square_sum',sq(Y))]:need(old(g[f])==p,'singleton macro mismatch: '+f)
  rT=add(V(ti),T,-1);need(rows[rt]in(rT,scale(rT,-1)),'modulus row mismatch')
  need(rows[rq]==add(delta,mul(V(ti),V(qi))),'private power quotient mismatch')
  E=old(g['E']);need(add(add(E,sq(delta),-1),mul(T,sq(Y)),-1)==scale(mul(mul(b,Y),wire),2),'square-error identity mismatch')
 for j,(name,ki,li,ia,ib,b) in enumerate([('radix',210,211,150,151,add(V(100),C(-1))),('radix_plus_one',208,209,148,149,V(100))],2):
  g=cert['groups'][j];need(g['name']==name and g['removed_K']==ki and g['removed_L']==li and g['removed_rows']==[ia,ib],'same-base pool binding mismatch')
  T=add(add(scale(mul(A,b),2),sq(b),-1),C(-1));E=old(g['E'])
  need(old(g['base'])==b and old(g['T'])==T,'same-base modulus mismatch')
  need(add(E,mul(T,V(li)),-1)==add(rows[ib],mul(b,rows[ia])),'same-base residual combination mismatch')
 private=set(cert['removed_variables']);removed=set(cert['removed_rows']);ordinary=[]
 for i,r in enumerate(rows):
  if i not in removed:
   need(all(not(set(mon)&private)for mon in r),'deleted coordinate not private')
   ordinary.append({tuple(forward[k]for k in mon):co for mon,co in r.items()})
 need(len(source['residuals'])==len(ordinary)+len(cert['blocks']),'wrong residual count')
 need([P(r['terms'])for r in source['residuals'][:len(ordinary)]]==ordinary,'retained row changed')
 expectblocks={'staged':[([0,1],'base'),([2,3],'one')],'all4':[([0,1,2,3],'base')],'separate':[([0],'direct'),([1],'direct'),([2,3],'one')]}
 need([(b['groups'],b['weights'])for b in cert['blocks']]==expectblocks[variant],'wrong pool partition')
 need(source['variables'][:208]==[parent['variables'][j]for j in retained],'wrong retained variables')
 for j,b in enumerate(cert['blocks']):
  need(b['quotient_index']==208+j,'wrong pool quotient index');idx=b['groups'];gs=cert['groups'];Ts=[P(gs[i]['T'])for i in idx]
  if b['weights']=='direct':want=add(P(gs[idx[0]]['delta']),mul(V(208+j),Ts[0]))
  else:
   want=scale(product([V(208+j)]+Ts),-1)
   for at,i in enumerate(idx):
    fs=([P(gs[i]['base'])]if b['weights']=='base'else[])+[P(gs[i]['E'])]+[T for k,T in enumerate(Ts)if k!=at]
    want=add(want,product(fs))
  need(P(source['residuals'][len(ordinary)+j]['terms'])==want,'wrong oriented pool row')
 return {'variant':variant,'status':'PASS','source_variables':216,'source_residuals':156,'result_variables':len(source['variables']),'result_residuals':len(source['residuals']),'retained_rows_checked':len(ordinary),'private_rows_combined':8,'exact_power_requests':15,'principal_common_pell_pairs':13,'actual_square_frame_atoms':34}
if __name__=='__main__':print(json.dumps([check('staged'),check('all4')],indent=2))
