#!/usr/bin/env python3
"""Independent standard-library algebra/semantic-edit audit; imports no producer."""
from pathlib import Path
from collections import defaultdict
import copy,hashlib,json,sys
ROOT=Path(__file__).resolve().parent

def need(c,msg):
 if not c:raise ValueError(msg)
def add(*ps):
 o=defaultdict(int)
 for p in ps:
  for m,c in p.items():o[m]+=c
 return {m:c for m,c in o.items()if c}
def neg(p,k=-1):return {m:k*c for m,c in p.items()if k*c}
def mul(p,q):
 o=defaultdict(int)
 for m,c in p.items():
  for n,d in q.items():o[tuple(sorted(m+n))]+=c*d
 return {m:c for m,c in o.items()if c}
def val(i):return {(i,):1}
def const(i):return {():i}if i else{}
def parse(ts):
 p={}
 for c,m in ts:
  need(type(c)is int and c!=0 and m==sorted(m),'noncanonical coefficient');need(tuple(m)not in p,'duplicate');p[tuple(m)]=c
 return p
def terms(p):return [[c,list(m)]for m,c in sorted(p.items())]
def subst(p,mp):
 out={}
 for m,c in p.items():
  term=const(c)
  for i in m:term=mul(term,mp.get(i,val(i)))
  out=add(out,term)
 return out
def digest(x):return hashlib.sha256((json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()).hexdigest()
def read(p):return json.loads((ROOT/p).read_text())

def verify(base=None,sc=None,cc=None):
 parent=read('sources/parent217.json');old=[parse(r['terms'])for r in parent['residuals']];ns={v['name']:i for i,v in enumerate(parent['variables'])}
 sc=copy.deepcopy(sc if sc is not None else read('semantic_certificate.json'));cc=copy.deepcopy(cc if cc is not None else read('consumer_certificate.json'));base=copy.deepcopy(base if base is not None else read('base215/equation.json'))
 need(hashlib.sha256((ROOT/'sources/parent217.json').read_bytes()).hexdigest()==sc['source_sha256'],'parent digest');need(sc['old_frame']['path']=='sources/parent217.json','portable source locator')
 V=lambda s:val(ns[s]);t=V('t0');F=V('crt.growth_majorant_F');A=add(V('shared.A'),const(1));W=V('shared.W');Y=V('index0.Y');Yb=V('index2.Y');U=V('mul.450');Z=V('shared.Zminus1');d=add(t,const(2))
 oldatoms=[parse(a['terms'])for a in sc['old_frame']['actual_atoms']]
 oldtarget=add(W,const(-2),*(neg(mul(a,a))for a in oldatoms));combo=sc['old_frame']['row_combination'];need(add(*(neg(old[i],k)for k,i in combo))==oldtarget,'old exact frame')
 # Independently derive the actual canonical power ports.
 Jidx=neg(add(old[143],neg(V('cap.R')),neg(mul(V('index15.Y'),V('cap.h')),4)))
 q=add(const(1),neg(V('radix.odd_square_root_half'),4));ports={0:(d,t,F),1:(V('choose0.output'),V('x'),V('pow1.output')),2:(V('self_radix.BH'),V('x'),q)}
 pairs={3:add(F,t),4:t,5:add(V('crt.encoded.a'),const(-1)),7:V('crt.encoded.b'),8:V('crt.encoded.c'),9:V('crt.encoded.d'),10:V('crt.encoded.S'),11:V('y'),12:V('crt.encoded.Sp'),13:V('crt.encoded.u'),14:V('x'),15:V('crt.encoded.vq'),16:V('crt.encoded_index_minus_one'),17:Jidx}
 for k,index in pairs.items():ports[k]=(q if k in [4,11,14]else add(q,const(1)),index,V('pow'+str(k)+'.output'))
 st={0:neg(t,8)};need(sc['horizon_substitution']==[[0,terms(st[0])]] and sc['strong_frame_scale']==4,'frame and horizon declaration');atoms=[parse(a['terms'])for a in sc['atoms']]
 for k,triple in ports.items():
  for p in triple:need(subst(p,st)in atoms,'missing actual power port '+str(k))
 underlying=sorted({m[0]for a in atoms for m in a if m});need(underlying==sc['underlying_coordinates'],'frame coverage')
 bounds=[abs(a.get((),0))+sum(c*c//4 for m,c in a.items()if m)for a in atoms];need(bounds==[r['constant_bound']for r in sc['atoms']],'integer affine bound')
 need(max(bounds)+1==sc['frame_constant']==22 and len(underlying)==43,'frame counts')
 private=[i for i,v in enumerate(parent['variables'])if any(s in v['name']for s in ['shared.A','index','cap.'])and v['name']!='crt.encoded_index_minus_one'];need(not(set(private)&set(underlying)),'private Pell frame circularity')
 eold=add(Yb,neg(t),neg(F));enew=add(Yb,neg(Y),neg(F));need(parse(sc['orientation_old_error'])==eold and parse(sc['orientation_new_error'])==enew,'difference-error identity')
 rs=[subst(r,st)for r in old]
 target={94:add(U,neg(W,4),neg(mul(W,Z),-8)),95:add(V('mul.451'),neg(mul(W,U),-4),neg(U)),99:subst(add(V('base0.T'),mul(d,d),const(1),neg(mul(A,d),-2)),st),100:subst(add(old[100],neg(Y,-2)),st),131:add(W,const(-22),*(neg(mul(val(i),val(i)))for i in underlying)),144:subst(add(old[144],mul(enew,enew),neg(mul(eold,eold))),st)}
 for item in sc['edits']:
  i=item['row'];need(parse(item['old'])==rs[i],'old semantic mutation');need(parse(item['new'])==target[i],'new semantic mutation');rs[i]=target[i]
 need(set(target)=={e['row']for e in sc['edits']},'edit census');root=ns['cofinal.horizon_root'];need(sc['deleted_root']==root and sc['deleted_horizon_row']==133,'horizon projection');need(old[133]==add(t,const(-16),neg(mul(val(root),val(root)))),'old horizon literal');need(all(root not in m for i,r in enumerate(rs)if i!=133 for m in r),'private horizon root')
 p=ns['mul.337'];r=ns['mul.340'];n=217;J=val(n);S=V('crt.encoded.S');Sp=V('crt.encoded.Sp');K=V('mul.314');a=V('crt.encoded.a');b=V('crt.encoded.b');s=V('mul.40');dd=add(neg(a,2),neg(b,4),neg(s,2));rJ=add(J,neg(mul(F,S)))
 need(cc['deleted_coordinates']==[p,r]and cc['deleted_rows']==[60,62]and cc['new_coordinate']==n and cc['retained_K_row']==47 and cc['retained_factor_row']==63,'consumer census')
 forward={i:parse(pol)for i,pol in cc['forward']};reverse={i:parse(pol)for i,pol in cc['reverse']};need(forward=={n:mul(F,S)},'consumer forward');need(reverse=={p:add(const(1),mul(F,b)),r:add(const(1),mul(F,add(a,const(-1))))},'consumer reverse')
 changed={i:parse(pol)for i,pol in cc['edited_consumers']};need(parse(cc['new_row'])==rJ,'new shared product')
 identities={61:add(old[61],mul(Sp,old[60]),neg(mul(b,old[47]))),64:add(old[64],mul(S,old[62]),neg(mul(add(a,const(-1)),rJ))),65:add(old[65],mul(b,rJ),mul(add(neg(Sp,8),neg(S)),old[60]),neg(mul(Sp,old[62]),4),mul(Sp,old[63]),neg(mul(dd,old[47])))}
 for i,z in changed.items():need(z==identities[i],'full consumer ideal identity '+str(i));rs[i]=z
 rs.append(rJ)
 # Explicit reverse identities and complete consumer privacy.
 for i in [60,62]:need(not subst(old[i],reverse),'private factor restoration')
 rev={61:add(changed[61],mul(b,old[47])),64:add(changed[64],mul(add(a,const(-1)),rJ)),65:add(changed[65],neg(mul(b,rJ)),neg(mul(Sp,old[63])),mul(dd,old[47]))}
 for i,z in rev.items():need(subst(old[i],reverse)==z,'reverse consumer identity')
 for i,z in enumerate(old):
  if i not in [60,61,62,64,65]:need(not any(p in m or r in m for m in z),'undeclared private consumer')
 omitted={60,62,133};removed={p,r,root};keep=[i for i in range(218)if i not in removed];rn={i:j for j,i in enumerate(keep)}
 expected=[{tuple(rn[i]for i in m):c for m,c in z.items()}for j,z in enumerate(rs)if j not in omitted];need(expected==[parse(r['terms'])for r in base['residuals']],'complete base reconstruction');need(len(base['variables'])==215 and base['domain']=='unrestricted integers','base dimension and domain');need(read('coordinate_map.json')=={'retained_old_coordinates':keep,'old_to_new':[[i,j]for i,j in rn.items()],'retained_old_rows':[j for j in range(len(rs))if j not in omitted]},'complete coordinate map')
 results={}
 for tag in ['integer215','integer215_sparse']:
  final=read(tag+'/equation.json');cert=read(tag+'/row_certificate.json');rr=copy.deepcopy(expected);need(cert['input_sha256']==digest(base),'basis parent')
  for i,j,k in cert['operations']:
   need(i!=j and type(k)is int and k!=0,'invertible row operation');rr[i]=add(rr[i],neg(rr[j],k))
  need(rr==[parse(r['terms'])for r in final['residuals']]and cert['output_sha256']==digest(final),'basis replay')
  back=copy.deepcopy(rr)
  for i,j,k in reversed(cert['operations']):back[i]=add(back[i],neg(back[j],-k))
  need(back==expected,'inverse row replay');exp=add(*(mul(z,z)for z in rr));need(parse(read(tag+'/expanded_polynomial.json')['terms'])==exp,'complete expansion')
  metric={'variables':215,'rows':152,'residual_terms':sum(map(len,rr)),'row_height':max(abs(c)for z in rr for c in z.values()),'degree':max(map(len,exp)),'monomials':len(exp),'height':max(map(abs,exp.values()))};need(metric==read(tag+'/metrics.json'),'literal metrics');need({i for m in exp for i in m}==set(range(215)),'liveness');results[tag]=metric
 return results
if __name__=='__main__':
 results=verify();controls=[]
 for name,where in [('frame','semantic'),('growth','base'),('restoration','consumer')]:
  b=read('base215/equation.json');s=read('semantic_certificate.json');c=read('consumer_certificate.json')
  if where=='semantic':s['frame_constant']+=1
  elif where=='consumer':c['reverse'][0][1][0][0]*=-1
  else:b['residuals'][98]['terms'][0][0]+=1
  try:verify(b,s,c)
  except ValueError:controls.append(name)
  else:raise ValueError('negative control escaped '+name)
 print(json.dumps({'status':'PASS','optimized':bool(sys.flags.optimize),'endpoints':results,'negative_controls':controls,'producer_imports':False},indent=2))
