#!/usr/bin/env python3
"""Atomic fixed-matrix arithmetic emitter; predecessor inputs are inert JSON."""
import argparse, hashlib, json, random
from collections import Counter
from pathlib import Path

PINS = {
 'matrix193_synchronized_rows.json':'9ce8537fc12bff3a2d3d91297d65a47ee6a7af193ff4bb08f474216260ef4233',
 'matrix193_uniform_context_packing.md':'58b941cc2970908c7865cd80dfbeee179e3907954891b8c8fd4073d58b357cf9',
 'group_projective_tail_quotient_shift.md':'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a',
 'group_range_projective_compiler.md':'2c71f229f791a12c63d701adcfe56dcfe44601e124566562fc67aeb8a2398f2f',
 'u15_unary_block_interface.md':'cdc686700af3545609796034e0a2c906bd0438b6bcabc0c0b267954cc9d20452',
 'matrix193_gamma1_recode.md':'6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742',
 'matrix193_context_absorption.md':'d7492809ba00a011c8280172bb016f96f3f6c240de6a823ed717d82bda5e4f4b',
 'matrix193_synchronized_rows.md':'ab768aa392841add5dc6dfcd8ed62564ca17fae2fe80e5ec39f1f4ceb36559d2',
 'matrix193_unit_shear_controller.py':'a1023d53f49a087c1861a67ceeb1a5c7de46ee59bccf62acaa49cacb8c2f1866',
 'matrix193_unit_shear_controller.json':'9c48903d2bb227169d9984d24230e9dfcd46cf03b89511bf29dd0347284c9cbc',
 'matrix193_unit_shear_controller.md':'303ae00247cf5d05f6509e86ca2acf520b7354541a493d41442ccebef11dad59',
 'matrix193_marked_loader_packing.json':'2d9e99f33e12049be2b2228e388072df6ae024115d7942d9dbc4afc4e6f93475',
 'matrix193_marked_loader_packing.md':'0a093975e246141a4b4938f76bba1f4a74fec3ce4355534b363d7f28d42e36ac',
 'group_projective_general_separate_range.md':'2e0744fd1aad96cc3a1e94ad47237e3c81f2d73705dca72998daf422cf2c3614',
}
FIXED=['initial_X0','initial_X1','R00_minus_one','R10','R01','R11_minus_one','radix_multiplier','Hfix']

def check(v,s):
 if not v: raise ValueError(s)
def digest(v):return hashlib.sha256(v).hexdigest()
def parse(path):
 def obj(items):
  out={}
  for k,v in items:
   check(k not in out,'duplicate key');out[k]=v
  return out
 return json.loads(path.read_text(),object_pairs_hook=obj)
def exact(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(u,v) for u,v in zip(a,b))
 return a==b

class DAG:
 def __init__(self):self.rows=[];self.cache={}
 def op(self,op,a,b):
  if type(a)is int and type(b)is int:return a*b if op=='*' else a+b if op=='+' else a-b
  if op=='*' and (a==0 or b==0):return 0
  if op=='*' and a==1:return b
  if op=='*' and b==1:return a
  if op in ('+','-') and b==0:return a
  if op=='+' and a==0:return b
  key=(op,a,b)
  if key not in self.cache:
   name='v'+str(len(self.rows));self.rows.append([name,op,a,b]);self.cache[key]=name
  return self.cache[key]
 def add(self,a,b):return self.op('+',a,b)
 def sub(self,a,b):return self.op('-',a,b)
 def mul(self,a,b):return self.op('*',a,b)
 def sum(self,xs):
  s=0
  for x in xs:s=self.add(s,x)
  return s
 def poly(self,xs,p):
  s=0
  for x in reversed(xs):s=self.add(self.mul(s,p),x)
  return s

def groups_for(macros):
 groups=[]
 for side,offset in [('K',0),('G',2)]:
  classes={}
  for i,macro in enumerate(macros[1:]):
   mat=tuple(macro[side])
   if mat==(1,0,0,1):continue
   if mat not in classes:
    classes[mat]=len(groups);groups.append({'source_coordinate':offset,'matrix':list(mat),'edges':[],'kind':side})
   groups[classes[mat]]['edges'].append(i+2)
 groups.append({'source_coordinate':2,'matrix':macros[0]['G'],'edges':[0],'kind':'LOAD'})
 groups.append({'source_coordinate':2,'matrix':['R00_minus_one','R01','R10','R11_minus_one'],'edges':[1],'kind':'SWITCH','matrix_is_increment':True})
 return groups

def emit(macros,m,native,name):
 n=len(macros)+2;edges=[[0,0,0,'LOAD'],[1,0,1,'SWITCH']]+[[i+2,1,1,'TILE'] for i in range(len(macros)-1)]+[[n-1,1,1,'IDLE']]
 groups=groups_for(macros);L=2*len(groups);nx=sum(g['source_coordinate']==0 for g in groups);ny=len(groups)-nx
 check(all(g['source_coordinate']==(0 if j<nx else 2) for j,g in enumerate(groups)),'contiguous source groups')
 check(m>=n and m>=4 and m&(m-1)==0,'controller width')
 Eports=['edge_hat'+str(i) for i in range(n)]
 witnesses=['height_slack']+['H'+str(i) for i in range(4)]+['Zhat'+str(i) for i in range(L)]+['bound_global','F_even','F_odd','population_quotient']+Eports+native['independent_native_ports']
 b=DAG();D=b.add(b.add('x','Hfix'),'height_slack');c=b.sub(D,1);B=b.mul('radix_multiplier',D);bm=b.sub(B,1)
 E=[b.sub(p,1) for p in Eports];J=b.sum(E);P=b.add(b.mul(bm,J),1);powcache={0:1,1:P};repcache={0:0,1:1}
 def power(k):
  if k not in powcache:
   z=power(k//2);sq=b.mul(z,z);powcache[k]=b.mul(sq,P) if k%2 else sq
  return powcache[k]
 def rep(k):
  if k not in repcache:
   h=k//2;v=b.mul(rep(h),b.add(power(h),1));repcache[k]=b.add(v,power(2*h)) if k%2 else v
  return repcache[k]
 # Pair repetition in P^2 uses its own finite addition chain.
 rep2cache={0:0,1:1}
 def rep2(k):
  if k not in rep2cache:
   h=k//2;v=b.mul(rep2(h),b.add(power(2*h),1));rep2cache[k]=b.add(v,power(4*h)) if k%2 else v
  return rep2cache[k]
 S=[b.sum(E[e] for e in g['edges']) for g in groups];Zs=[b.sub('Zhat'+str(i),1) for i in range(L)]
 pairX=b.add('H0',b.mul(P,'H1'));pairY=b.add('H2',b.mul(P,'H3'));Hrange=b.add(pairX,b.mul(power(2),pairY))
 Hphys=b.add(b.mul(pairX,rep2(nx)),b.mul(power(2*nx),b.mul(pairY,rep2(ny))))
 Mb=b.mul(bm,b.mul(b.add(P,1),b.poly(S,power(2))));Zb=b.poly(Zs,P);C=b.poly(E,P);O=b.mul(J,rep(m));O4=b.mul(J,rep(4))
 T=power(L+m);T2=power(L+m+4);M4=b.mul(b.add(D,c),O4);cs=b.mul(power(L),C);hs=b.mul(T,Hrange)
 H=b.add(b.add(b.add(Hphys,cs),hs),b.mul(B,T2));M=b.add(b.add(b.add(Mb,b.mul(power(L),O)),b.mul(T,M4)),T2);Z=b.add(b.add(Zb,cs),hs);q=b.mul(32,b.mul(B,T2))
 cut_values=[q,b.add(b.mul(16,H),13),b.add(b.mul(16,M),10),b.add(b.mul(16,Z),8),b.sum(['H'+str(i) for i in range(4)]+['Zhat'+str(i) for i in range(L)]+['bound_global']),P]
 cuts=dict(zip(native['cut_ports'],cut_values));stage={'packing':len(b.rows)}
 for nm,op,l,r in native['rows']:b.rows.append([nm,op,cuts.get(l,l),cuts.get(r,r)])
 stage['native']=len(b.rows)-stage['packing'];terms=[[] for _ in range(4)]
 for j,g in enumerate(groups):
  mat=g['matrix'];a,bb,cc,d=mat if g.get('matrix_is_increment') else [mat[0]-1,mat[1],mat[2],mat[3]-1]
  shift=b.mul(c,S[j]);u=b.sub(Zs[2*j],shift) if a!=0 or bb!=0 else 0;v=b.sub(Zs[2*j+1],shift) if cc!=0 or d!=0 else 0
  o=g['source_coordinate'];terms[o].append(b.add(b.mul(a,u),b.mul(cc,v)));terms[o+1].append(b.add(b.mul(bb,u),b.mul(d,v)))
 deltas=[b.sum(ts) for ts in terms];initial=[b.add(c,'initial_X0'),b.add(c,'initial_X1'),D,c];end=[b.mul('F_even',P),b.mul('F_odd',P)];comparisons=[]
 for i in range(4):comparisons.append([b.mul(B,b.add('H'+str(i),deltas[i])),b.sub(b.add('H'+str(i),end[i%2]),initial[i])])
 dst=b.sub(J,E[0]);src=b.sub(dst,E[1]);comparisons.append([b.add(src,P),b.mul(B,dst)])
 comparisons.append([b.mul(bm,'population_quotient'),b.sub(b.add(E[0],bm),'x')]);stage['outer_producers']=len(b.rows)-sum(stage.values())
 squares=[]
 for l,r in comparisons:
  res=b.sub(l,r);squares.append(b.mul(res,res))
 output=b.sub(b.mul('eight_units',b.add(b.sum(squares),1)),1);stage['finalizer']=len(b.rows)-sum(stage.values())
 return {'name':name,'free':['x']+FIXED+witnesses,'fixed_numerals':FIXED,'ordinary_input':'x','witnesses':witnesses,'source':b.rows,'output':output,'native_cut_bindings':cuts,'outer_comparisons':comparisons,'stage_counts':stage,'n':n,'m':m,'L':L,'matrix_macros':macros,'groups':groups,'controller_edges':edges,'marked_edge':0,'switch_edge':1,'ports':dict(D=D,c0=c,B=B,bminus=bm,E=E,J=J,P=P,Hrange=Hrange,Hphys=Hphys,Mb=Mb,Zb=Zb,C=C,O=O,O4=O4,T=T,T2=T2,M4=M4,H=H,M=M,Z=Z,q=q,selectors=S,selected=Zs,global_sum=cut_values[4],deltas=deltas)}

def audit(p):
 known=set(p['free']);by={};degree={v:0 if v in FIXED else 1 for v in known}
 for n,op,l,r in p['source']:
  check(n not in known and op in '+-*','valid row');check(all(type(v)is int or type(v)is str and v in known for v in (l,r)),'topology')
  dl=degree.get(l,0);dr=degree.get(r,0);degree[n]=dl+dr if op=='*' else max(dl,dr);by[n]=[l,r];known.add(n)
 live=set();todo=[p['output']]
 while todo:
  x=todo.pop()
  if type(x)is str and x not in live:live.add(x);todo.extend(by.get(x,[]))
 check(known<=live,'all ports/rows live: '+str(known-live));ct=Counter(row[1] for row in p['source'])
 return {'total':len(p['source']),'M':ct['*'],'A':ct['+']+ct['-'],'positive_witnesses':len(p['witnesses']),'naive_degree_upper':degree[p['output']],'proved_exact_degree':72*(p['m']+p['L']+4)+61,'all_live':True}

def evaluate(p,values,mod):
 env=dict(values)
 for n,op,l,r in p['source']:
  l=env[l] if type(l)is str else l;r=env[r] if type(r)is str else r
  env[n]=(l*r if op=='*' else l+r if op=='+' else l-r)%mod
 return env

def bindings(init,R,p):
 mats=[g['matrix'] for g in p['groups'] if not g.get('matrix_is_increment')]+[R];limit=1+max(max(abs(a)+abs(c),abs(b)+abs(d)) for a,b,c,d in mats);K=32
 while K<=limit:K*=2
 return dict(zip(FIXED,[init[0],init[1],R[0]-1,R[2],R[1],R[3]-1,K,max(p['m'],p['L'],abs(init[0]),abs(init[1]))+1]))

def direct(p,v,mod):
 r=lambda x:x%mod;D=v['x']+v['Hfix']+v['height_slack'];c=D-1;B=v['radix_multiplier']*D;bm=B-1
 E=[v['edge_hat'+str(i)]-1 for i in range(p['n'])];J=sum(E);P=r(bm*J+1);m=p['m'];L=p['L'];S=[sum(E[i] for i in g['edges']) for g in p['groups']]
 ZZ=[v['Zhat'+str(i)]-1 for i in range(L)];HH=[v['H'+str(i)] for i in range(4)]
 def word(coeff):
  total=0;pw=1
  for a in coeff:total=r(total+a*pw);pw=r(pw*P)
  return total
 Hphys=word([HH[g['source_coordinate']+z] for g in p['groups'] for z in [0,1]]);Hrange=word(HH);Mb=r(bm*word([s for s in S for _ in [0,1]]));Zb=word(ZZ);C=word(E);O=r(J*word([1]*m));O4=r(J*word([1]*4));T=pow(P,L+m,mod);T2=pow(P,L+m+4,mod);M4=r((2*D-1)*O4)
 H=r(Hphys+pow(P,L,mod)*C+T*Hrange+B*T2);M=r(Mb+pow(P,L,mod)*O+T*M4+T2);Z=r(Zb+pow(P,L,mod)*C+T*Hrange);q=r(32*B*T2);global_sum=sum(HH)+sum(ZZ)+L+v['bound_global']
 values=dict(D=D,c0=c,B=B,bminus=bm,J=J,P=P,Hrange=Hrange,Hphys=Hphys,Mb=Mb,Zb=Zb,C=C,O=O,O4=O4,T=T,T2=T2,M4=M4,H=H,M=M,Z=Z,q=q,global_sum=global_sum)
 k=v['selection__eta']+v['selection__zeta'];Y=r((2*v['selection__odd_half']+1)*q);cc=r(k*Y+v['selection__eta']);f=v['selection__f'];ii=v['selection__i'];tau=v['selection__tau_gap'];auxroot=r(v['selection__o']*f-cc)
 F3=r(16*Z+8);X=r((v['selection__w']+(q-1)*F3)*q);a=r(Y*(X+1));Delta=r(a*a+4*a+3);index=r(k-v['selection__h']*X*Y);packed=r((q-1)*(16*H+13+(q+1)*(16*M+10+(q-1)*F3)))
 factors=[r(tau*tau+4*X*Y*k*Y*(tau-k)),r((X+a*cc+v['selection__ga']*(4*a+3))**2-Delta*cc*cc),r(ii*ii*cc**4*(auxroot**2-v['selection__y_aux']**2)+v['selection__y_aux']**2),r(index-packed),r(auxroot-v['selection__j']*cc+2*index),r(ii*ii*cc**4-Delta*(f*f-1)+1),r(global_sum-P)]
 ds=[0]*4
 for j,g in enumerate(p['groups']):
  u=ZZ[2*j]-c*S[j];vv=ZZ[2*j+1]-c*S[j];mat=g['matrix'];a,b,cc,d=[v[z] for z in mat] if g.get('matrix_is_increment') else [mat[0]-1,mat[1],mat[2],mat[3]-1];o=g['source_coordinate'];ds[o]+=a*u+cc*vv;ds[o+1]+=b*u+d*vv
 initial=[c+v['initial_X0'],c+v['initial_X1'],D,c];end=[v['F_even'],v['F_odd']]*2
 residuals=[r(B*(HH[i]+ds[i])-HH[i]-end[i]*P+initial[i]) for i in range(4)]
 residuals += [r(sum(e[1]*E[e[0]] for e in p['controller_edges'])+P-B*sum(e[2]*E[e[0]] for e in p['controller_edges'])),r(bm*v['population_quotient']-E[0]-bm+v['x'])]
 out=1
 for f0 in factors:out=r(out*f0)
 return values,factors,residuals,r(out*(1+sum(z*z for z in residuals))-1)

def modular_checks(p):
 rng=random.Random(19613004+p['n']);record=[]
 for modulus in [1000000007,1000000009]:
  for seed in range(8):
   v={name:rng.randrange(-31,32) for name in p['free']};v.update(p['fixture_fixed_bindings'])
   if seed>=4:
    for name in FIXED:v[name]=rng.randrange(-31,32)
   env=evaluate(p,v,modulus);vs,fs,rs,out=direct(p,v,modulus)
   for name,value in vs.items():check(env[p['ports'][name]]==value%modulus,'direct port '+name)
   nf=1
   for f in fs:nf=nf*f%modulus
   check(env['eight_units']==nf,'seven native factors')
   for (l,r),res in zip(p['outer_comparisons'],rs):check((env[l]-env[r])%modulus==res,'outer residual')
   check(env[p['output']]==out,'whole source modular output');record.append({'modulus':modulus,'seed':seed,'output':out})
 return record

def fixture(p,x,idles,tile_word=None):
 tile_edges={ma['tile_id']:i+1 for i,ma in enumerate(p['matrix_macros']) if i};seq=[0]*x+[1]+([2]*x if tile_word is None else [tile_edges[t] for t in tile_word])+[p['n']-1]*idles;bind=p['fixture_fixed_bindings'];state=[bind['initial_X0'],bind['initial_X1'],1,0];states=[];code=0;R=[bind['R00_minus_one']+1,bind['R01'],bind['R10'],bind['R11_minus_one']+1]
 def act(row,M):return [row[0]*M[0]+row[1]*M[2],row[0]*M[1]+row[1]*M[3]]
 for eid in seq:
  e=p['controller_edges'][eid];check(e[1]==code,'fixture path');code=e[2];states.append(state[:])
  if eid==1:state[2:]=act(state[2:],R)
  elif eid!=p['n']-1:
   macro=p['matrix_macros'][0 if eid==0 else eid-1];state[:2]=act(state[:2],macro['K']);state[2:]=act(state[2:],macro['G'])
 check(code==1 and state[:2]==state[2:],'fixture endpoint');D=1
 while D<=max(x+bind['Hfix'],max(abs(z) for s in states+[state] for z in s)+1):D*=2
 B=bind['radix_multiplier']*D;c=D-1;t=len(seq);P=B**t;L=p['L'];E=[0]*p['n'];Hs=[0]*4;Zs=[0]*L;pw=1
 for eid,s in zip(seq,states):
  E[eid]+=pw
  for i in range(4):check(0<s[i]+c<2*D,'fixture positive range');Hs[i]+=(s[i]+c)*pw
  for j,g in enumerate(p['groups']):
   if eid in g['edges']:
    Zs[2*j]+=(s[g['source_coordinate']]+c)*pw;Zs[2*j+1]+=(s[g['source_coordinate']+1]+c)*pw
  pw*=B
 check((E[0]-x)%(B-1)==0,'population');v=dict(bind,x=x,height_slack=D-x-bind['Hfix'],F_even=state[0]+c,F_odd=state[1]+c,population_quotient=1+(E[0]-x)//(B-1),bound_global=P+1-sum(Hs)-sum(Zs)-L)
 v.update({'H'+str(i):z for i,z in enumerate(Hs)});v.update({'Zhat'+str(i):z+1 for i,z in enumerate(Zs)});v.update({'edge_hat'+str(i):z+1 for i,z in enumerate(E)})
 native=set(p['free'])-set(v);check(all(v[name]>0 for name in p['witnesses'] if name not in native),'positive outer');start=p['stage_counts']['packing'];end=start+p['stage_counts']['native'];rows=p['source'][:start]+p['source'][end:end+p['stage_counts']['outer_producers']];env=v.copy()
 for nm,op,l,r in rows:
  l=env[l] if type(l)is str else l;r=env[r] if type(r)is str else r;env[nm]=l*r if op=='*' else l+r if op=='+' else l-r
 check(all(env[l]==env[r] for l,r in p['outer_comparisons']),'fixture six residuals');ports=p['ports'];H,M,Z,q=[env[ports[n]] for n in ['H','M','Z','q']];check(H&M==Z,'fixture joined AND');truth=[q-16*H-16*M+16*Z-15,16*(H-Z)+4,16*(M-Z)+2,16*Z+8];check(min(truth)>0 and sum(truth)==q-1,'positive native fields')
 return {'x':x,'idles':idles,'duration':t,'D_bits':D.bit_length(),'B_bits':B.bit_length(),'q_bits':q.bit_length(),'ordinary_input_preserved':True,'all_six_comparisons_zero':True,'joined_AND':True,'strictly_positive_native_fields':True,'native_Pell_tuple_materialized':False,'max_coordinate_bits':max(abs(z).bit_length() for row in states+[state] for z in row),'positive_input_fixture':x>0,'tile_ids':tile_word if tile_word is not None else [1]*x,'outer_fields_sha256':digest(json.dumps([hex(H),hex(M),hex(Z),hex(q)]).encode())}

def dense_degree(p):
 mod=1000000007;env={n:[v%mod] for n,v in p['fixture_fixed_bindings'].items()}
 for i,n in enumerate(p['free']):
  if n not in env:env[n]=[(i+2)%mod,(i*i+3)%mod]
 for name,op,l,r in p['source']:
  a=env[l] if type(l)is str else [l%mod];b=env[r] if type(r)is str else [r%mod]
  if op=='*':
   c=[0]*(len(a)+len(b)-1)
   for i,u in enumerate(a):
    if u:
     for j,v in enumerate(b):
      if v:c[i+j]=(c[i+j]+u*v)%mod
  else:
   c=[0]*max(len(a),len(b));sgn=1 if op=='+' else -1
   for i,u in enumerate(a):c[i]=u
   for i,v in enumerate(b):c[i]=(c[i]+sgn*v)%mod
  while len(c)>1 and c[-1]==0:c.pop()
  env[name]=c
 out=env[p['output']];check(len(out)-1==p['ledger']['proved_exact_degree'],'diagnostic degree attained')
 return {'degree':len(out)-1,'modulus':mod,'coefficient':out[-1],'all_coefficients_sha256':digest(json.dumps(out,separators=(',',':')).encode()),'scope':'full diagnostic only; full original-table degree uses homogeneous proof'}

def build(root):
 for name,pin in PINS.items():check(digest((root/name).read_bytes())==pin,'pin '+name)
 base=parse(root/'matrix193_marked_loader_packing.json');native=base['native_source_contract'];factor=parse(root/'matrix193_unit_shear_controller.json');real=factor['packets'][1]
 macros=[{k:v for k,v in ma.items() if k in ('K','G','name','tile_id')} for ma in real['macros']]
 diag=[dict(K=[1,0,0,1],G=[1,-1,0,1],name='LOAD',tile_id=None),dict(K=[0,-1,1,2],G=[1,0,0,1],name='TILE1',tile_id=1)]
 packets=[emit(diag,8,native,'diagnostic'),emit(macros,128,native,'uniform_atomic_original_table')]
 check(len(packets[1]['groups'])==170 and packets[1]['L']==340,'authenticated group count')
 for p in packets:p['ledger']=audit(p)
 context=factor['fixture_context'];bindingsets=[bindings([2,1],[2,1,1,1],packets[0]),bindings(context['original_initial_coordinates'],context['R'],packets[1])]
 for p,v in zip(packets,bindingsets):p['fixture_fixed_bindings']=v
 return {'status':'PASS','pins':PINS,'source_sha256':digest(Path(__file__).read_bytes()),'packets':packets,'modular_checks':[modular_checks(p) for p in packets],'diagnostic_outer_fixtures':[fixture(packets[0],x,idles) for x in range(5) for idles in [0,2]],'diagnostic_dense_degree':dense_degree(packets[0]),'actual_atomic_outer_fixture':fixture(packets[1],0,0,parse(root/'matrix193_synchronized_rows.json')['accepting_fixture']['tile_sequence']),'scope':'Complete atomic original-table grammar; valid fixed program coefficients inherit universality; arbitrary ports and diagnostic do not'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();result=build(a.root)
 if a.output:a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 else:check(exact(result,parse(a.expect)),'receipt replay')
 print(json.dumps([p['ledger'] for p in result['packets']]))
if __name__=='__main__':main()
