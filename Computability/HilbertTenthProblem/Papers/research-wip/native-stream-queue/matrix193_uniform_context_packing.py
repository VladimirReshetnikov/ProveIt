#!/usr/bin/env python3
"""A fresh fixed-table arithmetic emitter; all predecessor inputs are inert JSON."""
import argparse, hashlib, json, random
from collections import Counter
from pathlib import Path

PINS = {
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

def emit(edges,m,native,name):
 n=len(edges);check(m>=8 and m&(m-1)==0 and n<=m,'controller width')
 switch=[e[0] for e in edges if e[3]=='R'];check(len(switch)==1,'unique switch')
 marks=[0];Eports=['edge_hat'+str(i) for i in range(n)]
 witnesses=['height_slack']+['H'+str(i) for i in range(4)]+['Zhat'+str(i) for i in range(10)]+['bound_global','F_even','F_odd','population_quotient']+Eports+native['independent_native_ports']
 b=DAG();D=b.add(b.add('x','Hfix'),'height_slack');c=b.sub(D,1);B=b.mul('radix_multiplier',D);bm=b.sub(B,1)
 E=[b.sub(p,1) for p in Eports];J=b.sum(E);P=b.add(b.mul(bm,J),1)
 powers={1:P};rep={1:1};width=1
 while width<m:
  powers[2*width]=b.mul(powers[width],powers[width]);rep[2*width]=b.mul(rep[width],b.add(powers[width],1));width*=2
 P2,P4,P8=powers[2],powers[4],powers[8];P10=b.mul(P8,P2)
 O=b.mul(J,rep[m]);O8=b.mul(J,rep[8]);C=b.poly(E,P)
 sels=[b.sum([E[e[0]] for e in edges if e[3]==l]) for l in range(1,9)]
 sels += [E[switch[0]],E[switch[0]]]
 Zs=[b.sub('Zhat'+str(i),1) for i in range(10)]
 Hb8=b.mul(b.add(P,1),b.poly(['H1','H0','H3','H2'],P2))
 Hb10=b.add(Hb8,b.mul(P8,b.add('H2',b.mul(P,'H3'))))
 Mb=b.mul(bm,b.poly(sels,P));Zb=b.poly(Zs,P)
 T=b.mul(powers[m],P10);T2=b.mul(T,P8);M8=b.mul(b.add(D,c),O8)
 Cshift=b.mul(P10,C);histshift=b.mul(T,Hb8)
 H=b.add(b.add(b.add(Hb10,Cshift),histshift),b.mul(B,T2))
 M=b.add(b.add(b.add(Mb,b.mul(P10,O)),b.mul(T,M8)),T2)
 Z=b.add(b.add(Zb,Cshift),histshift);q=b.mul(32,b.mul(B,T2))
 cut_values=[q,b.add(b.mul(16,H),13),b.add(b.mul(16,M),10),b.add(b.mul(16,Z),8),b.sum(['H'+str(i) for i in range(4)]+['Zhat'+str(i) for i in range(10)]+['bound_global']),P]
 cuts=dict(zip(native['cut_ports'],cut_values));stage={'packing':len(b.rows)}
 for nm,op,l,r in native['rows']:b.rows.append([nm,op,cuts.get(l,l),cuts.get(r,r)])
 stage['native']=len(b.rows)-stage['packing']
 deltas=[b.sub(b.sub(Zs[2*i],Zs[2*i+1]),b.mul(c,b.sub(sels[2*i],sels[2*i+1]))) for i in range(4)]
 cs=b.mul(c,E[switch[0]]);u=b.sub(Zs[8],cs);v=b.sub(Zs[9],cs)
 deltas[2]=b.add(deltas[2],b.add(b.mul('R00_minus_one',u),b.mul('R10',v)))
 deltas[3]=b.add(deltas[3],b.add(b.mul('R01',u),b.mul('R11_minus_one',v)))
 initial=[b.add(c,'initial_X0'),b.add(c,'initial_X1'),D,c]
 end=[b.mul('F_even',P),b.mul('F_odd',P)];comparisons=[]
 for i in range(4):comparisons.append([b.mul(B,b.add('H'+str(i),deltas[i])),b.sub(b.add('H'+str(i),end[i%2]),initial[i])])
 src=b.sum([b.mul(e[1],E[e[0]]) for e in edges]);dst=b.sum([b.mul(e[2],E[e[0]]) for e in edges])
 comparisons.append([b.add(src,P),b.mul(B,dst)])
 comparisons.append([b.mul(bm,'population_quotient'),b.sub(b.sub(b.add(Eports[0],bm),'x'),1)])
 stage['outer_producers']=len(b.rows)-sum(stage.values())
 squares=[]
 for l,r in comparisons:
  res=b.sub(l,r);squares.append(b.mul(res,res))
 output=b.sub(b.mul('eight_units',b.add(b.sum(squares),1)),1);stage['finalizer']=len(b.rows)-sum(stage.values())
 return {'name':name,'free':['x']+FIXED+witnesses,'fixed_numerals':FIXED,'ordinary_input':'x','witnesses':witnesses,'source':b.rows,'output':output,'native_cut_bindings':cuts,'outer_comparisons':comparisons,'stage_counts':stage,'n':n,'m':m,'controller_edges':edges,'marked_edge':0,'switch_edge':switch[0],'ports':dict(D=D,c0=c,B=B,bminus=bm,E=E,J=J,P=P,Hb8=Hb8,Hb10=Hb10,Mb=Mb,Zb=Zb,C=C,O=O,O8=O8,T=T,T2=T2,M8=M8,H=H,M=M,Z=Z,q=q,selectors=sels,selected=Zs,global_sum=cut_values[4])}

def audit(p):
 known=set(p['free']);by={};degree={v:0 if v in FIXED else 1 for v in known}
 for n,op,l,r in p['source']:
  check(n not in known and op in '+-*','valid row')
  check(all(type(v)is int or type(v)is str and v in known for v in (l,r)),'topology')
  dl=degree.get(l,0);dr=degree.get(r,0);degree[n]=dl+dr if op=='*' else max(dl,dr);by[n]=[l,r];known.add(n)
 live=set();todo=[p['output']]
 while todo:
  x=todo.pop()
  if type(x)is str and x not in live:live.add(x);todo.extend(by.get(x,[]))
 check(known<=live,'all ports/rows live')
 c=Counter(row[1] for row in p['source'])
 return {'total':len(p['source']),'M':c['*'],'A':c['+']+c['-'],'positive_witnesses':len(p['witnesses']),'naive_degree_upper':degree[p['output']],'proved_exact_degree':72*p['m']+1357,'all_live':True}

def evaluate(p,values,mod):
 env=dict(values)
 for n,op,l,r in p['source']:
  l=env[l] if type(l)is str else l;r=env[r] if type(r)is str else r
  env[n]=(l*r if op=='*' else l+r if op=='+' else l-r)%mod
 return env

def bindings(init,R,m):
 K=16
 while K<=1+max(abs(R[0])+abs(R[2]),abs(R[1])+abs(R[3])):K*=2
 return dict(zip(FIXED,[init[0],init[1],R[0]-1,R[2],R[1],R[3]-1,K,max(m,abs(init[0]),abs(init[1]))+1]))

def direct(p,v,mod):
 r=lambda x:x%mod
 D=v['x']+v['Hfix']+v['height_slack'];c=D-1;B=v['radix_multiplier']*D;bm=B-1
 E=[v['edge_hat'+str(i)]-1 for i in range(p['n'])];J=sum(E);P=r(bm*J+1);m=p['m']
 S=[sum(E[e[0]] for e in p['controller_edges'] if e[3]==l) for l in range(1,9)]+[E[p['switch_edge']]]*2
 ZZ=[v['Zhat'+str(i)]-1 for i in range(10)];HH=[v['H'+str(i)] for i in range(4)]
 def word(coeff):
  total=0;power=1
  for a in coeff:total=r(total+a*power);power=r(power*P)
  return total
 P8=pow(P,8,mod);P10=pow(P,10,mod);Rm=word([1]*m);R8=word([1]*8)
 Hb8=word([HH[i] for i in [1,1,0,0,3,3,2,2]]);Hb10=r(Hb8+P8*HH[2]+pow(P,9,mod)*HH[3])
 C=word(E);O=r(J*Rm);O8=r(J*R8);T=pow(P,m+10,mod);T2=pow(P,m+18,mod)
 Mb=r(bm*word(S));Zb=word(ZZ);M8=r((2*D-1)*O8)
 H=r(Hb10+P10*C+T*Hb8+B*T2);M=r(Mb+P10*O+T*M8+T2);Z=r(Zb+P10*C+T*Hb8);q=r(32*B*T2)
 global_sum=sum(HH)+sum(ZZ)+10+v['bound_global']
 values=dict(D=D,c0=c,B=B,bminus=bm,J=J,P=P,Hb8=Hb8,Hb10=Hb10,Mb=Mb,Zb=Zb,C=C,O=O,O8=O8,T=T,T2=T2,M8=M8,H=H,M=M,Z=Z,q=q,global_sum=global_sum)
 k=v['selection__eta']+v['selection__zeta'];Y=r((2*v['selection__odd_half']+1)*q);cc=r(k*Y+v['selection__eta']);f=v['selection__f'];ii=v['selection__i'];tau=v['selection__tau_gap'];auxroot=r(v['selection__o']*f-cc)
 F3=r(16*Z+8);X=r((v['selection__w']+(q-1)*F3)*q);a=r(Y*(X+1));Delta=r(a*a+4*a+3);index=r(k-v['selection__h']*X*Y)
 packed=r((q-1)*(16*H+13+(q+1)*(16*M+10+(q-1)*F3)))
 factors=[r(tau*tau+4*X*Y*k*Y*(tau-k)),r((X+a*cc+v['selection__ga']*(4*a+3))**2-Delta*cc*cc),r(ii*ii*cc**4*(auxroot**2-v['selection__y_aux']**2)+v['selection__y_aux']**2),r(index-packed),r(auxroot-v['selection__j']*cc+2*index),r(ii*ii*cc**4-Delta*(f*f-1)+1),r(global_sum-P)]
 ds=[ZZ[2*i]-ZZ[2*i+1]-c*(S[2*i]-S[2*i+1]) for i in range(4)]
 u=ZZ[8]-c*E[p['switch_edge']];vv=ZZ[9]-c*E[p['switch_edge']]
 ds[2]+=v['R00_minus_one']*u+v['R10']*vv;ds[3]+=v['R01']*u+v['R11_minus_one']*vv
 initial=[c+v['initial_X0'],c+v['initial_X1'],D,c];end=[v['F_even'],v['F_odd']]*2
 residuals=[r(B*(HH[i]+ds[i])-HH[i]-end[i]*P+initial[i]) for i in range(4)]
 residuals += [r(sum(e[1]*E[e[0]] for e in p['controller_edges'])+P-B*sum(e[2]*E[e[0]] for e in p['controller_edges'])),r(bm*v['population_quotient']-E[0]-bm+v['x'])]
 out=1
 for f0 in factors:out=r(out*f0)
 return values,factors,residuals,r(out*(1+sum(z*z for z in residuals))-1)

def modular_checks(p):
 rng=random.Random(19041004+p['n']);record=[]
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
   check(env[p['output']]==out,'whole source modular output')
   record.append({'modulus':modulus,'seed':seed,'output':out})
 return record

def diagnostic_fixture(p,x,idles):
 edges=p['controller_edges'];seq=[0]*x+[1]+[2,3,4]*x+[5]*idles;state=[2,1,1,0];states=[];code=0
 for eid in seq:
  e=edges[eid];check(e[1]==code,'fixture path');code=e[2];states.append(state[:]);label=e[3]
  if label=='R':state[2],state[3]=2*state[2]+state[3],state[2]+state[3]
  elif label:
   target=(label-1)//2;state[target]+=(1 if label%2 else -1)*state[target^1]
 check(code==1 and state[:2]==state[2:],'fixture endpoint')
 bind=p['fixture_fixed_bindings'];D=1
 while D<=max(x+bind['Hfix'],max(abs(z) for s in states+[state] for z in s)+1):D*=2
 B=bind['radix_multiplier']*D;c=D-1;t=len(seq);P=B**t
 E=[0]*p['n'];Hs=[0]*4;Zs=[0]*10;power=1
 for eid,s in zip(seq,states):
  E[eid]+=power;label=edges[eid][3]
  for i in range(4):check(0<s[i]+c<2*D,'fixture positivity/range');Hs[i]+=(s[i]+c)*power
  if label=='R':Zs[8]+=(s[2]+c)*power;Zs[9]+=(s[3]+c)*power
  elif label:Zs[label-1]+=(s[((label-1)//2)^1]+c)*power
  power*=B
 check((E[0]-x)%(B-1)==0,'fixture population')
 v=dict(bind,x=x,height_slack=D-x-bind['Hfix'],F_even=state[0]+c,F_odd=state[1]+c,population_quotient=1+(E[0]-x)//(B-1),bound_global=P+1-sum(Hs)-sum(Zs)-10)
 v.update({'H'+str(i):z for i,z in enumerate(Hs)});v.update({'Zhat'+str(i):z+1 for i,z in enumerate(Zs)});v.update({'edge_hat'+str(i):z+1 for i,z in enumerate(E)})
 native=set(p['free'])-set(v)
 check(all(v[name]>0 for name in p['witnesses'] if name not in native),'fixture positive outer witnesses')
 start=p['stage_counts']['packing'];end=start+p['stage_counts']['native'];rows=p['source'][:start]+p['source'][end:end+p['stage_counts']['outer_producers']]
 env=v.copy()
 for name,op,l,r in rows:
  l=env[l] if type(l)is str else l;r=env[r] if type(r)is str else r;env[name]=l*r if op=='*' else l+r if op=='+' else l-r
 check(all(env[l]==env[r] for l,r in p['outer_comparisons']),'fixture actual residuals')
 ports=p['ports'];H,M,Z,q=[env[ports[n]] for n in ['H','M','Z','q']]
 check(H&M==Z,'fixture exact joined AND')
 truth=[q-16*H-16*M+16*Z-15,16*(H-Z)+4,16*(M-Z)+2,16*Z+8]
 check(min(truth)>0 and sum(truth)==q-1,'fixture native fields')
 return {'x':x,'idles':idles,'duration':t,'D':D,'ordinary_input_preserved':True,'all_six_comparisons_zero':True,'joined_AND':True,'strictly_positive_native_fields':True,'native_Pell_tuple_materialized':False}

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

def build(root,factorroot):
 for name,pin in PINS.items():check(digest((root/name).read_bytes())==pin,'pin '+name)
 base=parse(root/'matrix193_marked_loader_packing.json');native=base['native_source_contract']
 check(digest((factorroot/'matrix193_unit_shear_controller.json').read_bytes())==PINS['matrix193_unit_shear_controller.json'],'actual factor receipt pin');factor=parse(factorroot/'matrix193_unit_shear_controller.json');real=factor['packets'][1];edges=real['controller']['edges'];m=real['statistics']['padded_m']
 diag=[[0,0,0,8,0],[1,0,1,'R',None],[2,1,2,2,1],[3,2,3,4,1],[4,3,1,1,1],[5,1,1,0,None]]
 packets=[emit(diag,8,native,'diagnostic'),emit(edges,m,native,'uniform_original_table')]
 for p in packets:p['ledger']=audit(p)
 context=factor['fixture_context'];bindingsets=[bindings([2,1],[2,1,1,1],8),bindings(context['original_initial_coordinates'],context['R'],m)]
 for p,v in zip(packets,bindingsets):p['fixture_fixed_bindings']=v
 return {'status':'PASS','pins':PINS,'factorization_receipt_sha256':digest((factorroot/'matrix193_unit_shear_controller.json').read_bytes()),'source_sha256':digest(Path(__file__).read_bytes()),'packets':packets,'modular_checks':[modular_checks(p) for p in packets],'diagnostic_outer_fixtures':[diagnostic_fixture(packets[0],x,idles) for x in range(5) for idles in [0,2]],'diagnostic_dense_degree':dense_degree(packets[0]),'scope':'Complete context-independent instruction grammar and fully paid uniform fixed-table source; valid program coefficient recipes inherit universality, arbitrary fixed ports do not'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--factor-root',type=Path);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();result=build(a.root,a.factor_root or a.root)
 if a.output:a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 else:check(exact(result,parse(a.expect)),'receipt replay')
 print(json.dumps([p['ledger'] for p in result['packets']]))
if __name__=='__main__':main()
