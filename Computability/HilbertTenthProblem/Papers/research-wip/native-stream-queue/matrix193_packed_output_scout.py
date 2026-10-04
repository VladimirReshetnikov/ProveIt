#!/usr/bin/env python3
"""Fresh bounded packed-output scout. All predecessor artifacts are inert JSON."""
import argparse, hashlib, json
from collections import Counter
from pathlib import Path
PINS={'matrix193_atomic_context_packing.json':'7f9f9614f3862d08fa2645a5944a4567f4f268e4e93a57c5dec6e59d5a9fe8c9','matrix193_atomic_context_packing.md':'b19f3a7188eac22055323ecc277522e18d68f0818c6f5d2da3a05ceea94262ca','matrix193_marked_loader_packing.json':'2d9e99f33e12049be2b2228e388072df6ae024115d7942d9dbc4afc4e6f93475'}
def ck(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def parse(path):
 def obj(items):
  out={}
  for k,v in items:
   ck(k not in out,'duplicate JSON key');out[k]=v
  return out
 return json.loads(path.read_text(),object_pairs_hook=obj)
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
class DAG:
 def __init__(self):self.rows=[];self.cache={}
 def op(self,op,a,b):
  if isinstance(a,int) and isinstance(b,int):return a*b if op=='*' else a+b if op=='+' else a-b
  if op=='*' and (a==0 or b==0):return 0
  if op=='*' and a==1:return b
  if op=='*' and b==1:return a
  if op in '+-' and b==0:return a
  if op=='+' and a==0:return b
  key=(op,a,b)
  if key not in self.cache:
   n='r'+str(len(self.rows));self.rows.append([n,op,a,b]);self.cache[key]=n
  return self.cache[key]
 def add(self,a,b):return self.op('+',a,b)
 def sub(self,a,b):return self.op('-',a,b)
 def mul(self,a,b):return self.op('*',a,b)
 def sum(self,ls):
  v=0
  for a in ls:v=self.add(v,a)
  return v
 def poly(self,ls,q):
  v=0
  for a in reversed(ls):v=self.add(self.mul(v,q),a)
  return v

def emit(parent,native):
 b=DAG();groups=parent['groups'];L=parent['L'];m=parent['m'];n=parent['n'];nx=sum(g['source_coordinate']==0 for g in groups);fixedgroups=groups[:-1];ny=len(fixedgroups)-nx
 ck(groups[-1]['kind']=='SWITCH' and len(groups[-1]['edges'])==1,'switch last')
 layouts=[('X',groups[:nx],0),('Y',groups[nx:-1],2)]
 Ms=[max(abs(v-(1 if k in (0,3) else 0)) for g in gs for k,v in enumerate(g['matrix']))+1 for _,gs,_ in layouts]
 lengths=[2*len(gs) for _,gs,_ in layouts];padding=1
 while padding<=max(2*M*l for M,l in zip(Ms,lengths)):padding*=2
 fixed=parent['fixed_numerals'];wit=['height_slack']+['H'+str(i) for i in range(4)]+['Zswitch0_hat','Zswitch1_hat','bound_global','F_even','F_odd','population_quotient']+['edge_hat'+str(i) for i in range(n)]+native['independent_native_ports']
 for side,_,_ in layouts:
  wit += [side+'_block_hat',side+'_block_slack',side+'_sum_hat',side+'_sum_slack',side+'_sum_quot_hat']
  for j in range(2):wit += [side+'_dot'+str(j)+'_'+s for s in ['hat','slack','low_hat','low_slack','high_hat']]
 D=b.add(b.add('x','Hfix'),'height_slack');c=b.sub(D,1);B=b.mul('radix_multiplier',D);bm=b.sub(B,1);E=[b.sub('edge_hat'+str(i),1) for i in range(n)];J=b.sum(E);P=b.add(b.mul(bm,J),1);Q=b.mul(padding,P)
 pw={0:1,1:Q};rp={0:0,1:1};rp2={0:0,1:1}
 def power(k):
  if k not in pw:
   v=b.mul(power(k//2),power(k//2));pw[k]=b.mul(v,Q) if k%2 else v
  return pw[k]
 def rep(k):
  if k not in rp:
   h=k//2;v=b.mul(rep(h),b.add(power(h),1));rp[k]=b.add(v,power(2*h)) if k%2 else v
  return rp[k]
 def rep2(k):
  if k not in rp2:
   h=k//2;v=b.mul(rep2(h),b.add(power(2*h),1));rp2[k]=b.add(v,power(4*h)) if k%2 else v
  return rp2[k]
 S=[b.sum(E[e] for e in g['edges']) for g in groups]
 pairX=b.add('H0',b.mul(Q,'H1'));pairY=b.add('H2',b.mul(Q,'H3'));Hr=b.add(pairX,b.mul(power(2),pairY));Hp=b.add(b.mul(pairX,rep2(nx)),b.mul(power(2*nx),b.mul(pairY,rep2(ny+1))))
 Mb=b.mul(bm,b.mul(b.add(Q,1),b.poly(S,power(2))));blocks=[b.sub(side+'_block_hat',1) for side,_,_ in layouts];zs=[b.sub('Zswitch'+str(i)+'_hat',1) for i in range(2)]
 Zb=b.add(b.add(blocks[0],b.mul(power(lengths[0]),blocks[1])),b.mul(power(L-2),b.add(zs[0],b.mul(Q,zs[1]))))
 C=b.poly(E,Q);O=b.mul(J,rep(m));O4=b.mul(J,rep(4));T=power(L+m);T2=power(L+m+4);M4=b.mul(b.add(D,c),O4);cs=b.mul(power(L),C);hs=b.mul(T,Hr)
 H=b.add(b.add(b.add(Hp,cs),hs),b.mul(B,T2));M=b.add(b.add(b.add(Mb,b.mul(power(L),O)),b.mul(T,M4)),T2);Z=b.add(b.add(Zb,cs),hs);q=b.mul(32,b.mul(B,T2));G=b.sum(['H'+str(i) for i in range(4)]+['Zswitch0_hat','Zswitch1_hat','bound_global'])
 cuts=dict(zip(native['cut_ports'],[q,b.add(b.mul(16,H),13),b.add(b.mul(16,M),10),b.add(b.mul(16,Z),8),G,P]));stages={'packing':len(b.rows)}
 for name,op,l,r in native['rows']:b.rows.append([name,op,cuts.get(l,l),cuts.get(r,r)])
 stages['native']=len(b.rows)-stages['packing'];comp=[];deltas=[];extract=[];qm=b.sub(Q,1);at=0
 for (side,gs,coord),mag,length,block in zip(layouts,Ms,lengths,blocks):
  comp.append([b.add(block,side+'_block_slack'),power(length)])
  total=b.sub(side+'_sum_hat',1);quot=b.sub(side+'_sum_quot_hat',1)
  comp.append([block,b.add(b.mul(qm,quot),total)]);comp.append([b.add(total,side+'_sum_slack'),qm])
  shift=b.mul(mag,total);records=[]
  for j in range(2):
   co=[];sc=[]
   for k,g in enumerate(gs):
    a=g['matrix'][j]-(j==0);cc=g['matrix'][j+2]-(j==1);co.extend([mag+a,mag+cc]);sc.append(b.mul(a+cc,S[at+k]))
   pol=b.poly(list(reversed(co)),Q);dot=b.sub(side+'_dot'+str(j)+'_hat',1);low=b.sub(side+'_dot'+str(j)+'_low_hat',1);high=b.sub(side+'_dot'+str(j)+'_high_hat',1)
   comp.append([b.mul(pol,block),b.add(low,b.mul(power(length-1),b.add(dot,b.mul(Q,high))))]);comp.append([b.add(low,side+'_dot'+str(j)+'_low_slack'),power(length-1)]);comp.append([b.add(dot,side+'_dot'+str(j)+'_slack'),Q])
   deltas.append(b.sub(b.sub(dot,shift),b.mul(c,b.sum(sc))))
   records.append({'coefficients':co,'polynomial':pol,'dot':dot,'low':low,'high':high})
  extract.append({'side':side,'length':length,'magnitude_shift':mag,'block':block,'sum':total,'sum_quotient':quot,'products':records});at+=len(gs)
 sw=b.mul(c,S[-1]);su=b.sub(zs[0],sw);sv=b.sub(zs[1],sw)
 deltas[2]=b.add(deltas[2],b.add(b.mul('R00_minus_one',su),b.mul('R10',sv)));deltas[3]=b.add(deltas[3],b.add(b.mul('R01',su),b.mul('R11_minus_one',sv)))
 initials=[b.add(c,'initial_X0'),b.add(c,'initial_X1'),D,c];ends=[b.mul('F_even',P),b.mul('F_odd',P)]
 for i in range(4):comp.append([b.mul(B,b.add('H'+str(i),deltas[i])),b.sub(b.add('H'+str(i),ends[i%2]),initials[i])])
 dst=b.sub(J,E[0]);src=b.sub(dst,E[1]);comp.append([b.add(src,P),b.mul(B,dst)]);comp.append([b.mul(bm,'population_quotient'),b.sub(b.add(E[0],bm),'x')]);stages['outer_producers']=len(b.rows)-sum(stages.values())
 sq=[]
 for l,r in comp:
  v=b.sub(l,r);sq.append(b.mul(v,v))
 out=b.sub(b.mul('eight_units',b.add(b.sum(sq),1)),1);stages['finalizer']=len(b.rows)-sum(stages.values())
 p={'name':parent['name'],'source':b.rows,'output':out,'free':['x']+fixed+wit,'witnesses':wit,'fixed_numerals':fixed,'fixture_fixed_bindings':parent['fixture_fixed_bindings'],'padding':padding,'groups':groups,'n':n,'m':m,'L':L,'stage_counts':stages,'native_cut_bindings':cuts,'extraction':extract,'comparisons':comp,'ports':{'D':D,'B':B,'P':P,'Q':Q,'J':J,'E':E,'selectors':S,'H':H,'M':M,'Z':Z,'q':q,'global_sum':G,'deltas':deltas}}
 known=set(p['free']);dep={};deg={x:0 if x in fixed else 1 for x in known}
 for name,op,l,r in b.rows:
  ck(name not in known,'duplicate');ck(all(type(x)is int or x in known for x in (l,r)),'topology');known.add(name);dep[name]=(l,r);deg[name]=deg.get(l,0)+deg.get(r,0) if op=='*' else max(deg.get(l,0),deg.get(r,0))
 live=set();stack=[out]
 while stack:
  x=stack.pop()
  if type(x)is str and x not in live:live.add(x);stack.extend(dep.get(x,()))
 ck(known<=live,'dead '+str(known-live));ct=Counter(row[1] for row in b.rows);p['ledger']={'proved_exact_degree':72*(L+m+4)+55+4*max(lengths)+2,'literal_count':len({v for row in b.rows for v in row[2:] if type(v)is int}),'total':len(b.rows),'M':ct['*'],'A':ct['+']+ct['-'],'positive_witnesses':len(wit),'residuals':len(comp),'all_live':True,'syntactic_degree_upper':deg[out]}
 return p

def evaluate(p,v,mod=None,omit_native=False):
 env=dict(v);start=p['stage_counts']['packing'];end=start+p['stage_counts']['native'];stop=len(p['source'])-p['stage_counts']['finalizer']
 rows=p['source'][:start]+p['source'][end:stop] if omit_native else p['source']
 for name,op,l,r in rows:
  a=env[l] if type(l)is str else l;c=env[r] if type(r)is str else r
  value=a*c if op=='*' else a+c if op=='+' else a-c
  env[name]=value if mod is None else value%mod
 return env

def direct(p,v,mod):
 r=lambda x:x%mod
 D=v['x']+v['Hfix']+v['height_slack'];c=D-1;B=v['radix_multiplier']*D;bm=B-1
 E=[v['edge_hat'+str(i)]-1 for i in range(p['n'])];J=sum(E);P=r(bm*J+1);Q=r(p['padding']*P);L=p['L'];m=p['m'];HH=[v['H'+str(i)] for i in range(4)];S=[sum(E[e] for e in g['edges']) for g in p['groups']]
 def word(xs):return sum(x*pow(Q,i,mod) for i,x in enumerate(xs))%mod
 Hphys=word([HH[g['source_coordinate']+j] for g in p['groups'] for j in [0,1]]);Hrange=word(HH);Mb=r(bm*word([s for s in S for _ in [0,1]]));bs=[v[e['side']+'_block_hat']-1 for e in p['extraction']];sw=[v['Zswitch'+str(i)+'_hat']-1 for i in range(2)]
 Zb=r(bs[0]+pow(Q,p['extraction'][0]['length'],mod)*bs[1]+pow(Q,L-2,mod)*word(sw));C=word(E);O=r(J*word([1]*m));O4=r(J*word([1]*4));T=pow(Q,L+m,mod);T2=pow(Q,L+m+4,mod)
 H=r(Hphys+pow(Q,L,mod)*C+T*Hrange+B*T2);M=r(Mb+pow(Q,L,mod)*O+T*(2*D-1)*O4+T2);Z=r(Zb+pow(Q,L,mod)*C+T*Hrange);q=r(32*B*T2);G=sum(HH)+sum(sw)+2+v['bound_global'];rs=[];ds=[];at=0
 for rec,block in zip(p['extraction'],bs):
  side=rec['side'];length=rec['length'];mag=rec['magnitude_shift'];total=v[side+'_sum_hat']-1;quot=v[side+'_sum_quot_hat']-1
  rs += [r(block+v[side+'_block_slack']-pow(Q,length,mod)),r(block-(Q-1)*quot-total),r(total+v[side+'_sum_slack']-(Q-1))]
  for j,prod in enumerate(rec['products']):
   pre=side+'_dot'+str(j)+'_';dot=v[pre+'hat']-1;low=v[pre+'low_hat']-1;high=v[pre+'high_hat']-1;pol=word(list(reversed(prod['coefficients'])))
   rs += [r(pol*block-low-pow(Q,length-1,mod)*(dot+Q*high)),r(low+v[pre+'low_slack']-pow(Q,length-1,mod)),r(dot+v[pre+'slack']-Q)]
   coeff=prod['coefficients'];center=sum((coeff[2*k]+coeff[2*k+1]-2*mag)*S[at+k] for k in range(length//2));ds.append(r(dot-mag*total-c*center))
  at+=length//2
 u=sw[0]-c*S[-1];vv=sw[1]-c*S[-1];ds[2]=r(ds[2]+v['R00_minus_one']*u+v['R10']*vv);ds[3]=r(ds[3]+v['R01']*u+v['R11_minus_one']*vv)
 init=[c+v['initial_X0'],c+v['initial_X1'],D,c];term=[v['F_even'],v['F_odd']]*2
 rs += [r(B*(HH[i]+ds[i])-HH[i]-term[i]*P+init[i]) for i in range(4)]
 rs += [r(J-E[0]-E[1]+P-B*(J-E[0])),r(bm*v['population_quotient']-E[0]-bm+v['x'])]
 # Independent closed formulas for the seven unchanged native factors.
 k=v['selection__eta']+v['selection__zeta'];Y=r((2*v['selection__odd_half']+1)*q);cc=r(k*Y+v['selection__eta']);f=v['selection__f'];ii=v['selection__i'];tau=v['selection__tau_gap'];aux=r(v['selection__o']*f-cc);F3=r(16*Z+8)
 X=r((v['selection__w']+(q-1)*F3)*q);a=r(Y*(X+1));Delta=r(a*a+4*a+3);ix=r(k-v['selection__h']*X*Y);packed=r((q-1)*(16*H+13+(q+1)*(16*M+10+(q-1)*F3)))
 factors=[r(tau*tau+4*X*Y*k*Y*(tau-k)),r((X+a*cc+v['selection__ga']*(4*a+3))**2-Delta*cc*cc),r(ii*ii*cc**4*(aux*aux-v['selection__y_aux']**2)+v['selection__y_aux']**2),r(ix-packed),r(aux-v['selection__j']*cc+2*ix),r(ii*ii*cc**4-Delta*(f*f-1)+1),r(G-P)]
 product=1
 for fac in factors:product=r(product*fac)
 return {'D':D,'B':B,'P':P,'Q':Q,'J':J,'H':H,'M':M,'Z':Z,'q':q,'global_sum':G},factors,rs,r(product*(1+sum(s*s for s in rs))-1)

def modular_checks(p):
 import random
 rng=random.Random(316201+p['n']);out=[]
 for mod in [1000000007,1000000009]:
  for seed in range(8):
   v={s:rng.randrange(-31,32) for s in p['free']}
   if seed<4:v.update(p['fixture_fixed_bindings'])
   env=evaluate(p,v,mod);ports,factors,rs,value=direct(p,v,mod)
   for s,z in ports.items():ck(env[p['ports'][s]]==z%mod,'mod port '+s)
   prod=1
   for fac in factors:prod=prod*fac%mod
   ck(env['eight_units']==prod,'native factors')
   for (l,r),z in zip(p['comparisons'],rs):ck((env[l]-env[r])%mod==z,'mod residual')
   ck(env[p['output']]==value,'mod full output');out.append({'modulus':mod,'seed':seed,'output':value})
 return out

def fixture(p,parent,x,idles,tiles=None,source_exact=False):
 mapping={a['tile_id']:i+1 for i,a in enumerate(parent['matrix_macros']) if i};seq=[0]*x+[1]+([2]*x if tiles is None else [mapping[z] for z in tiles])+[p['n']-1]*idles;bind=p['fixture_fixed_bindings'];state=[bind['initial_X0'],bind['initial_X1'],1,0];states=[];controller=0;R=[bind['R00_minus_one']+1,bind['R01'],bind['R10'],bind['R11_minus_one']+1]
 def act(s,a):return [s[0]*a[0]+s[1]*a[2],s[0]*a[1]+s[1]*a[3]]
 for e in seq:
  edge=parent['controller_edges'][e];ck(edge[1]==controller,'path');controller=edge[2];states.append(state[:])
  if e==1:state[2:]=act(state[2:],R)
  elif e!=p['n']-1:
   ma=parent['matrix_macros'][0 if e==0 else e-1];state[:2]=act(state[:2],ma['K']);state[2:]=act(state[2:],ma['G'])
 ck(controller==1 and state[:2]==state[2:],'endpoint')
 D=1
 while D<=max(x+bind['Hfix'],max(abs(z) for s in states+[state] for z in s)+1):D*=2
 B=bind['radix_multiplier']*D;c=D-1;t=len(seq);P=B**t;Q=p['padding']*P;shift=Q.bit_length()-1;ck(1<<shift==Q,'dyadic Q');E=[0]*p['n'];HH=[0]*4;ZZ=[0]*p['L'];pw=1
 for edge,s in zip(seq,states):
  E[edge]+=pw
  for j in range(4):HH[j]+=(s[j]+c)*pw
  for g,group in enumerate(p['groups']):
   if edge in group['edges']:
    ZZ[2*g]+=(s[group['source_coordinate']]+c)*pw;ZZ[2*g+1]+=(s[group['source_coordinate']+1]+c)*pw
  pw*=B
 def word(vals):return sum(z<<(shift*i) for i,z in enumerate(vals))
 v=dict(bind,x=x,height_slack=D-x-bind['Hfix'],F_even=state[0]+c,F_odd=state[1]+c,population_quotient=1+(E[0]-x)//(B-1),bound_global=P+1-sum(HH)-sum(ZZ[-2:])-2)
 v.update({'H'+str(i):z for i,z in enumerate(HH)});v.update({'edge_hat'+str(i):z+1 for i,z in enumerate(E)});v.update({'Zswitch'+str(i)+'_hat':z+1 for i,z in enumerate(ZZ[-2:])});at=0;dotchecks=[]
 for rec in p['extraction']:
  side=rec['side'];length=rec['length'];digits=ZZ[at:at+length];block=word(digits);power=1<<(shift*length);total=sum(digits);quot,remainder=divmod(block,Q-1);ck(total==remainder,'word sum extraction')
  v.update({side+'_block_hat':block+1,side+'_block_slack':power-block,side+'_sum_hat':total+1,side+'_sum_slack':Q-1-total,side+'_sum_quot_hat':quot+1})
  for j,prod in enumerate(rec['products']):
   co=prod['coefficients'];pol=word(list(reversed(co)));product=pol*block;high,rest=divmod(product,power);dot,low=divmod(rest,1<<(shift*(length-1)));expected=sum(a*z for a,z in zip(co,digits));ck(dot==expected,'carry-free middle extraction');pre=side+'_dot'+str(j)+'_'
   v.update({pre+'hat':dot+1,pre+'slack':Q-dot,pre+'low_hat':low+1,pre+'low_slack':(1<<(shift*(length-1)))-low,pre+'high_hat':high+1});dotchecks.append(dot==expected)
  at+=length
 native=set(p['free'])-set(v);ck(all(v[w]>0 for w in p['witnesses'] if w not in native),'positive outer')
 J=sum(E);S=[sum(E[e] for e in g['edges']) for g in p['groups']];L=p['L'];m=p['m'];Hp=word([HH[g['source_coordinate']+j] for g in p['groups'] for j in [0,1]]);Mb=(B-1)*word([s for s in S for _ in [0,1]]);Zb=word(ZZ);C=word(E);O=J*word([1]*m);O4=J*word([1]*4);Hr=word(HH);T=1<<(shift*(L+m));T2=1<<(shift*(L+m+4));H=Hp+(C<<(shift*L))+T*Hr+B*T2;M=Mb+(O<<(shift*L))+T*(2*D-1)*O4+T2;Z=Zb+(C<<(shift*L))+T*Hr;q=32*B*T2
 ck(H&M==Z,'joined AND');truth=[q-16*H-16*M+16*Z-15,16*(H-Z)+4,16*(M-Z)+2,16*Z+8];ck(min(truth)>0 and sum(truth)==q-1,'native truth fields')
 ds=[0]*4
 for j,g in enumerate(p['groups']):
  u=ZZ[2*j]-c*S[j];vv=ZZ[2*j+1]-c*S[j]
  if g['kind']=='SWITCH':a,bb,cc,d=[bind[z] for z in g['matrix']]
  else:a,bb,cc,d=g['matrix'];a-=1;d-=1
  z=g['source_coordinate'];ds[z]+=a*u+cc*vv;ds[z+1]+=bb*u+d*vv
 initials=[c+bind['initial_X0'],c+bind['initial_X1'],D,c];ends=[v['F_even'],v['F_odd']]*2
 ck(all(B*(HH[i]+ds[i])==HH[i]+ends[i]*P-initials[i] for i in range(4)),'history relations');ck(J-E[0]-E[1]+P==B*(J-E[0]),'flow');ck((B-1)*v['population_quotient']==E[0]+B-1-x,'population')
 if source_exact:
  env=evaluate(p,v,omit_native=True);ck(all(env[l]==env[r] for l,r in p['comparisons']),'all literal outer rows');ck([env[p['ports'][s]] for s in ['H','M','Z','q']]==[H,M,Z,q],'literal outer cuts')
 return {'x':x,'idles':idles,'duration':t,'D_bits':D.bit_length(),'B_bits':B.bit_length(),'Q_bits':Q.bit_length(),'q_bits':q.bit_length(),'max_coordinate_bits':max(abs(z).bit_length() for s in states+[state] for z in s),'four_middle_extractions':all(dotchecks),'all_outer_comparisons':True,'positive_outer_witnesses':True,'joined_AND':True,'positive_native_input_fields':True,'native_Pell_tuple_materialized':False,'exact_literal_outer_rows_evaluated':source_exact,'outer_fields_sha256':sha(json.dumps([hex(H),hex(M),hex(Z),hex(q)]).encode())}

def dense_degree(p):
 mod=1000000007;env={n:[v%mod] for n,v in p['fixture_fixed_bindings'].items()}
 for i,n in enumerate(p['free']):
  if n not in env:env[n]=[i+2,(i*i+3)%mod]
 for name,op,l,r in p['source']:
  a=env[l] if type(l)is str else [l%mod];b=env[r] if type(r)is str else [r%mod]
  if op=='*':
   c=[0]*(len(a)+len(b)-1)
   for i,u in enumerate(a):
    if u:
     for j,v in enumerate(b):
      if v:c[i+j]=(c[i+j]+u*v)%mod
  else:
   c=[0]*max(len(a),len(b))
   for i,u in enumerate(a):c[i]=u
   for i,v in enumerate(b):c[i]=(c[i]+v*(1 if op=='+' else -1))%mod
  while len(c)>1 and c[-1]==0:c.pop()
  env[name]=c
 out=env[p['output']];ck(len(out)-1==p['ledger']['proved_exact_degree'],'dense degree')
 return {'degree':len(out)-1,'modulus':mod,'leading_coefficient':out[-1],'all_coefficients_sha256':sha(json.dumps(out,separators=(',',':')).encode())}

def build(root):
 for name,pin in PINS.items():ck(sha((root/name).read_bytes())==pin,'pin '+name)
 parents=parse(root/'matrix193_atomic_context_packing.json');native=parse(root/'matrix193_marked_loader_packing.json')['native_source_contract']
 packets=[emit(p,native) for p in parents['packets']]
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'packets':packets,'modular_checks':[modular_checks(p) for p in packets],'diagnostic_dense_degree':dense_degree(packets[0]),'diagnostic_outer_fixtures':[fixture(packets[0],parents['packets'][0],x,i,source_exact=True) for x in range(5) for i in [0,2]],'actual_atomic_outer_fixture':fixture(packets[1],parents['packets'][1],0,0,parents['actual_atomic_outer_fixture']['tile_ids']),'scope':'Complete fixed-program packing with compressed selected outputs; arbitrary fixed ports and diagnostic not asserted universal; native witness extension is a proof obligation, not a materialized Pell tuple'}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();v=build(a.root)
 if a.output:a.output.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
 else:ck(exact(v,parse(a.expect)),'exact receipt replay')
 print(json.dumps([p['ledger'] for p in v['packets']]))
