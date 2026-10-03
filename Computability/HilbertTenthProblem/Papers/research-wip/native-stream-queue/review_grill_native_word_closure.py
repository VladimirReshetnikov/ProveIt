#!/usr/bin/env python3
"""Independent bounded source and semantics review of fixed-arity Grill closure."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib,itertools,json,random,sys,types
from pathlib import Path
import sympy as sp

SOURCE_SHA256='80abbb7a293ba1051fc1d2559c7f8aac5a2f28947535573be49c8c49f5f3e7b7'

def need(x,msg):
 if not x:raise ValueError(msg)
def exact(a,b):
 if type(a) is not type(b):return False
 if type(a) is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a) in (tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def load(path):
 data=path.read_bytes();need(hashlib.sha256(data).hexdigest()==SOURCE_SHA256,'Changed reviewed source')
 m=types.ModuleType('_reviewed_native_grill');m.__file__=str(path);exec(compile(data,str(path),'exec'),m.__dict__);return m
def execute(rows,values):
 e=dict(values)
 for n,op,a,b in rows:
  need(n not in e and op in ('+','-','*'),'SSA');aa=e[a] if type(a) is str else a;bb=e[b] if type(b) is str else b
  e[n]=aa+bb if op=='+' else aa-bb if op=='-' else aa*bb
 return e
def val(e,x):return e[x] if type(x) is str else x

def outer(p,e):
 s=p['tiles'];m=p['phase_count'];gu=p['groups_U'];gv=p['groups_V'];g=len(gu)+len(gv)
 selectors=[e[f'Shat{i}']-1 for i in range(s)];products=[e[f'ZUhat{i}']-1 for i in range(len(gu))]+[e[f'ZVhat{i}']-1 for i in range(len(gv))]
 p0=3*e['x']+e['Z0'];uf=p0*e['Vfinal']+e['x'];D=uf+e['phase_initial']+e['height_slack'];B=p['K']*D;J=sum(selectors);P=(B-1)*J+1
 nextu=2*e['H_U']+sum(row[1]*a for row,a in zip(p['maps'],selectors))
 nextv=e['H_V']+sum(group['difference']*products[len(gu)+j] for j,group in enumerate(gv))+sum(row[3]*a for row,a in zip(p['maps'],selectors))
 Q=sum((i//2+1)*a for i,a in enumerate(selectors));Next=sum((((i//2-1)%m)+1)*a for i,a in enumerate(selectors))
 rr=[e['H_U']+e['H_V']+sum(products)+g+e['global_bound']-P,B*nextu+1-e['H_U']-P*uf,B*nextv+1-e['H_V']-P*e['Vfinal'],B*Next+e['phase_initial']-Q-P*m]
 return rr,dict(P0=p0,Ufinal=uf,D=D,B=B,J=J,P=P,Q=Q,Next=Next)

def ports(p,e):
 rr,a=outer(p,e);P=a['P'];B=a['B'];D=a['D'];J=a['J'];s=p['tiles'];g=p['selected_products'];gu=p['groups_U'];gv=p['groups_V']
 sel=[e[f'Shat{i}']-1 for i in range(s)];zs=[e[f'ZUhat{i}']-1 for i in range(len(gu))]+[e[f'ZVhat{i}']-1 for i in range(len(gv))]
 groups=[sum(sel[i] for i in group['tiles']) for group in gu+gv]
 pack=lambda row:sum(x*P**i for i,x in enumerate(row))
 Hb=pack([e['H_U']]*len(gu)+[e['H_V']]*len(gv));Mb=(B-1)*pack(groups);Zb=pack(zs)
 C=P**g*pack(sel)+P**(g+s)*(e['H_U']+P*e['H_V']);N=g+s+4
 H=Hb+C+P**(N-2)*B+P**N*a['P0'];M=Mb+P**g*J*sum(P**i for i in range(s))+P**(g+s)*(D-1)*J*(1+P)+P**(N-2)*(B-1)+P**N*(a['P0']-1);Z=Zb+C
 a.update(H=H,M=M,Z=Z,scale=P**(N+1));return rr,a

def symbolic_outer(p):
 e={n:sp.Symbol(n) for n in p['parameters']+p['auxiliaries']};rows={n:(op,a,b) for n,op,a,b in p['source']}
 memo=dict(e)
 def ev(x):
  if type(x) is int:return sp.Integer(x)
  if x not in memo:
   op,a,b=rows[x];aa=ev(a);bb=ev(b);memo[x]=aa+bb if op=='+' else aa-bb if op=='-' else aa*bb
  return memo[x]
 rr,face=outer(p,e)
 for (a,b),r in zip(p['comparisons'][:4],rr):need(sp.expand(ev(a)-ev(b)-r)==0,'Exact outer residual identity')
 for k,x in face.items():need(sp.expand(ev(p['interfaces'][k])-x)==0,'Exact outer interface identity '+k)

def semantics(program,max_t=6):
 count=Counter();valid=[];bad_phase=[];m=len(program);s=2*m
 for t in range(1,max_t+1):
  B=16;P=B**t
  for tiles in itertools.product(range(s),repeat=t):
   count['tile_words']+=1;phase=[i//2 for i in tiles];U=V=1
   for i in tiles:
    d=i%2;n=program[i//2];U=2*U+d;V=(2*4**n*V+2*(4**n-1)//3) if d else V
   heads=[i%2 for i in reversed(tiles)]
   need(U==2**t+sum(d*2**i for i,d in enumerate(heads)),'Reverse binary sentinel')
   G=''.join('0'+'10'*program[i//2] for i in reversed(tiles) if i%2)
   need(V==2**len(G)+sum(int(d)*2**i for i,d in enumerate(G)),'Reverse appendant sentinel')
   Q=sum((a+1)*B**j for j,a in enumerate(phase));Next=sum(((a-1)%m+1)*B**j for j,a in enumerate(phase));initial=phase[0]+1
   flow=B*Next+initial==Q+P*m
   chronological=phase[-1]==0 and all(phase[j+1]==(phase[j]-1)%m for j in range(t-1))
   need(flow==chronological,'Packed reverse chronology')
   for ell in range(1,t+2):
    p0=2**ell;x=U-p0*V
    if not 0<3*x<p0:continue
    z=p0-3*x;w=''.join(str((x>>j)&1) for j in range(ell));h=''.join(map(str,heads));need(h==w+G,'Sentinel implies exact word equality')
    if not flow:
     count['word_boundaries_rejected_by_phase']+=1
     if len(bad_phase)<4:bad_phase.append(dict(program=list(program),tiles=tiles,x=x,Z0=z,P0=p0))
     continue
    queue=w;halt=None
    for j,d in enumerate(heads):
     if not queue:halt=j;break
     need(int(queue[0])==d,'Actual FIFO head before halt');queue=queue[1:]+('0'+'10'*program[j%m] if d else '')
    if halt is None:need(not queue,'Closure must halt');halt=t
    count['positive_word_closures']+=1;count['posthalt_closures']+=halt<t
    valid.append(dict(program=program,tiles=tiles,x=x,Z0=z,P0=p0,Ufinal=U,Vfinal=V,halt=halt))
 return count,valid,bad_phase

def fixture(p,item):
 tiles=item['tiles'];U=V=1;hu=[];hv=[]
 for i in tiles:
  hu.append(U);hv.append(V);a,c,b,d=p['maps'][i];U,V=a*U+c,b*V+d
 initial=tiles[0]//2+1;D=1<<(U+initial).bit_length();B=p['K']*D;P=B**len(tiles);pack=lambda row:sum(v*B**i for i,v in enumerate(row))
 e={n:1 for n in p['parameters']+p['auxiliaries']};e.update(x=item['x'],Z0=item['Z0'],Vfinal=V,phase_initial=initial,height_slack=D-U-initial,H_U=pack(hu),H_V=pack(hv))
 for i in range(p['tiles']):e[f'Shat{i}']=pack([int(q==i) for q in tiles])+1
 hats=[]
 for tag,groups,hist in [('U',p['groups_U'],hu),('V',p['groups_V'],hv)]:
  for i,group in enumerate(groups):
   name=f'Z{tag}hat{i}';e[name]=pack([h if q in group['tiles'] else 0 for q,h in zip(tiles,hist)])+1;hats.append(e[name])
 e['global_bound']=P-e['H_U']-e['H_V']-sum(hats);need(min(e.values())>0,'Complete supplied-positive fixture')
 rr,a=ports(p,e);need(rr==[0]*4 and a['P']==P,'Complete outer word fixture')
 return e,a

def verify(path,root):
 s=load(path);c=Counter();rng=random.Random(219243);packets={};programs=((0,),(1,),(0,1,1),(2,0,1))
 # The original pinned AND64 is reused solely as a disclosed native residual oracle.
 with s.dependencies(root) as component:
  native_rows,native_pairs,_=component.parent.native.source('and64_prescribed')
 for program in programs:
  for unit in (False,True):
   p=s.build(program,unit_product=unit,root=root);packets[program,unit]=p;symbolic_outer(p);c['symbolic_outer_source_forms']+=1;c['symbolic_outer_residuals']+=4
   names=p['parameters']+p['auxiliaries'];known=set(names);live={p['output']};hist=Counter();degrees={n:1 for n in names}
   for n,op,a,b in p['polynomial_source']:
    need(n not in known and type(n) is str and all(type(v) is int or type(v) is str and v in known for v in (a,b)),'Exact full source closure');known.add(n);hist['M' if op=='*' else 'A']+=1
   for n,op,a,b in p['polynomial_source']:
    da=degrees[a] if type(a) is str else 0;db=degrees[b] if type(b) is str else 0;degrees[n]=da+db if op=='*' else max(da,db)
   need(degrees[p['output']]==p['polynomial_ledger']['degree_upper'] and p['exact_degree'] is None,'Honest complete degree upper bound');c['formal_degree_bounds']+=1
   need(len(p['auxiliaries'])==p['tiles']+p['selected_products']+(23 if unit else 29),'Fixed-arity witness formula')
   for n,op,a,b in reversed(p['polynomial_source']):need(n in live,'Dead gate');live.update(v for v in (a,b) if type(v) is str)
   need(set(names)<=live,'Unused supplied coordinate')
   need(len(p['polynomial_source'])==p['polynomial_ledger']['operations'] and all(hist[k]==p['polynomial_ledger'][k] for k in ('M','A')),'Full paid ledger');c['complete_ledgers']+=1
   if program==(0,1,1):need(hist==({'M':98,'A':121} if unit else {'M':104,'A':139}),'Default complete219/243 count')
  raw=packets[program,False];unit=packets[program,True]
  for j in range(24):
   values={n:rng.randrange(-3,4) if j>=12 else rng.randrange(1,5) for n in raw['parameters']+raw['auxiliaries']}
   rr,a=ports(raw,values);env=execute(raw['polynomial_source'],values)
   need(rr==[val(env,x)-val(env,y) for x,y in raw['comparisons'][:4]],'Manual outer source values')
   for k,v in a.items():need(val(env,raw['interfaces'][k])==v,'Manual joined port '+k)
   nv={n:values['and__'+n] for n in raw['native_auxiliaries']};nv.update(P=a['scale'],Hhat=a['H']+1,Mhat=a['M']+1,Zhat=a['Z']+1)
   ne=execute(native_rows,nv);nr=[val(ne,x)-val(ne,y) for x,y in native_pairs];allr=[val(env,x)-val(env,y) for x,y in raw['comparisons']]
   need(rr+nr==allr and env[raw['output']]==sum(z*z for z in allr),'Complete raw native/SOS identity');c['full_raw_source_cases']+=1;c['full_raw_residuals']+=len(allr)
   if j<12:need(a['D']>=7 and a['P0']<a['D'] and values['Vfinal']<a['D'] and min(a[k] for k in ('H','M','Z'))>=0 and a['scale']>=1,'Pretyping positivity')
   uv={n:rng.randrange(-3,4) if j>=12 else rng.randrange(1,5) for n in unit['parameters']+unit['auxiliaries']};ue=execute(unit['polynomial_source'],uv)
   restored={n:uv[n] for n in raw['parameters']+raw['auxiliaries'] if n in uv};restored.update({n:ue[r] for n,r in unit['projection_aliases'].items()});restored['and__tau']=ue['and__UM']*ue['and__ksn2']+Fraction(uv['and__tau_gap']-1,2)
   oe=execute(raw['polynomial_source'],restored);rmap={(x,y):val(oe,x)-val(oe,y) for x,y in raw['comparisons']}
   f=[1+rmap['and__L15','and__R15'],1+rmap['and__L17','and__P17']-rmap['and__ic22','and__R16']*oe['and__aux_square_gap'],1-4*rmap['and__L9','and__R9'],1-rmap['and__bs_q','and__q']]
   need(f==[ue[n] for n in unit['unit_factors']],'Complete unit factor correction')
   keep=[v for pair,v in rmap.items() if pair not in unit['removed_parent_comparisons']];product=1
   for v in f:product*=v
   need(keep==[val(ue,x)-val(ue,y) for x,y in unit['comparisons'][:-1]] and ue[unit['output']]==product*(1+sum(v*v for v in keep))-1,'Complete unit finalizer correction');c['full_unit_restoration_cases']+=1
   if j<12:need(min(restored.values())>0,'Positive computed fields and restored root')
  cc,valid,bad=semantics(program);c.update(cc)
  for item in valid:
   for isunit in (False,True):
    p=packets[program,isunit];e,a=fixture(p,item);env=execute(p['source'],e)
    need(all(val(env,x)==val(env,y) for x,y in p['comparisons'][:4]),'Actual emitted outer equations')
    need(a['H']&a['M']==a['Z'] and max(a['H'],a['M'],a['Z'])<a['scale'],'Complete nonoverlapping AND ports')
    need(a['P0']<a['D']<=a['B']<=a['P'],'Input power lane range');c['genuine_outer_native_port_fixtures']+=1
 # Existential padding differs from choosing the shortest allowed padding.
 program=(0,1,1);padding_cases=[]
 for p0 in (8,16,32):
  queue=''.join(str((2>>j)&1) for j in range(p0.bit_length()-1));seen={};heads=[];step=0
  while queue and (step%3,queue) not in seen:
   need(step<100,'Padding witness search bound');seen[step%3,queue]=step;d=int(queue[0]);heads.append(d)
   queue=queue[1:]+('0'+'10'*program[step%3] if d else '');step+=1
  if queue:
   need(p0 in (8,16) and step-seen[step%3,queue]==3,'Exact shorter-padding cycle')
   padding_cases.append(dict(P0=p0,Z0=p0-6,halt=False,prefix=seen[step%3,queue],period=3,cycle_queue=queue,cycle_phase=step%3))
  else:
   need(p0==32 and step==9 and heads==[0,1,0,0,0,0,1,0,0],'Longer padding actual halt')
   tiles=tuple(2*(i%3)+heads[i] for i in range(step-1,-1,-1));item=dict(tiles=tiles,x=2,Z0=26)
   for isunit in (False,True):
    p=packets[program,isunit];e,a=fixture(p,item);ee=execute(p['source'],e)
    need(a['Ufinal']==578 and e['Vfinal']==18 and all(val(ee,x)==val(ee,y) for x,y in p['comparisons'][:4]),'Actual nine-step boundary')
    need(a['H']&a['M']==a['Z'] and max(a['H'],a['M'],a['Z'])<a['scale'],'Actual nine-step native interfaces');c['longer_padding_native_port_fixtures']+=1
   padding_cases.append(dict(P0=32,Z0=26,halt=True,steps=9,heads=heads,Ufinal=578,Vfinal=18))
 c['padding_sensitive_semantic_cases']=3
 # Removing input power lane gives a false accept for the ones-conserving program(1).
 bad=dict(program=(1,),tiles=(0,0,1,0,0,0),x=2,Z0=1,P0=7,Ufinal=72,Vfinal=10)
 raw=packets[(1,),False];e,a=fixture(raw,bad);N=raw['region_exponents']['input_power'];withoutH=a['H']-a['P']**N*7;withoutM=a['M']-a['P']**N*6
 need(withoutH&withoutM==a['Z'],'All older native lanes accept the nondyadic counterexample')
 need((a['H']&a['M'])-a['Z']==6*a['P']**N,'Actual input lane rejects the false boundary')
 c['necessary_input_lane_counterexamples']=1
 # Exact type/canonical packet and assignment boundaries, with rebuilt authentication.
 example=packets[(0,1,1),True]
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):c['malformed_rejections']+=1;return
  raise ValueError('Malformed API call accepted')
 import copy
 for field in ('source','polynomial_source','comparisons','interfaces','polynomial_ledger','auxiliaries'):
  packet=copy.deepcopy(example);packet[field]=None;reject(lambda packet=packet:s.checked(packet,root=root))
 for badvalue in (1.0,True):
  packet=copy.deepcopy(example);n,op,a,b=packet['polynomial_source'][0];packet['polynomial_source'][0]=(n,op,badvalue,b);reject(lambda packet=packet:s.checked(packet,root=root))
 vals={n:1 for n in example['parameters']+example['auxiliaries']}
 for badvalue in (1.0,True,0,-1,Fraction(1,2)):
  badvals=dict(vals,x=badvalue);reject(lambda badvals=badvals:s.evaluate(example,badvals,root=root))
 before=s.build((0,1,1),root=root);after=s.build((0,1,1),root=root);after['source'].clear();need(exact(before,s.build((0,1,1),root=root)),'No mutable public cache');c['copy_checks']=1
 return dict(status='PASS_INDEPENDENT_FIXED_ARITY_GRILL_REVIEW',source_sha256=SOURCE_SHA256,helper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),padding_sensitive_cases=padding_cases,checks=dict(c),default_unit_ledger=example['polynomial_ledger'],default_raw_ledger=packets[(0,1,1),False]['polynomial_ledger'],necessary_input_lane_counterexample={'program':[1],'forward_heads':[0,0,0,1,0,0],'P0':7,'x':2,'Z0':1,'Ufinal':72,'Vfinal':10,'full_native_Pell_zero_materialized':False},scope='New wrapper and literal complete native composition; imported source-pinnedAND64 residual oracle and reviewed existence theorem disclosed. No new native-Pell classification or universality proof.')

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,default=Path(__file__).with_name('grill_tag_native_word_closure.py'));ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=json.loads(json.dumps(verify(a.source,a.root),sort_keys=True))
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Saved review receipt mismatch')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({k:r[k] for k in ('status','checks','default_unit_ledger','default_raw_ledger')},sort_keys=True))
