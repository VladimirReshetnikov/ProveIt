#!/usr/bin/env python3
"""Independent exact audit. Reads JSON and bytes; imports no project builders.
All checks use explicit exceptions and remain active under Python -O.
"""
from pathlib import Path
from collections import Counter
from math import comb, gcd
import copy, gzip, hashlib, json, random, sys
from sympy import ZZ
from sympy.polys.rings import ring
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent/'radicals'
BASE=['j','C','z','h','r','v','w','T','c','n','t','p2','p3']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
EXPECTED={'13':(13,1072,192),'14':(14,378,145),'15':(15,172,123),'15c':(15,170,134),'16':(16,98,138)}
class Failure(RuntimeError):pass
def need(ok,msg):
 if not ok:raise Failure(str(msg))
def sha(b):return hashlib.sha256(b).hexdigest()
def modeof(p):return p['name'].split('_')[0][7:]
def structure(p):
 mode=modeof(p);need(mode in EXPECTED,'mode');nv,deg,nop=EXPECTED[mode]
 extra={'13':[],'14':['f'],'15':['f','gamma'],'15c':['f','p1'],'16':['f','gamma','p1']}[mode]
 need(p['variables']==BASE+extra,'variable order');need(p['fixed_ports']==PORTS,'ports');need(p['inputs']==BASE+extra+PORTS,'inputs');need(p['variable_count']==nv,'dimension');need(p['exact_degree']==deg,'degree metadata');need(p['domain']=='unrestricted integers','domain')
 seen=set(p['inputs']);rows={}
 for row in p['nodes']:
  need(row['id'] not in seen,'duplicate node');need(row['op'] in ['add','sub','mul'],'op');need(len(row['args'])==2,'arity');need(all(type(a) is int or (isinstance(a,str) and a in seen) for a in row['args']),'topology');seen.add(row['id']);rows[row['id']]=row
 live=set();todo=[p['output']]
 while todo:
  x=todo.pop()
  if type(x) is int or x in live:continue
  need(x in seen,'output reference');live.add(x)
  if x in rows:todo.extend(rows[x]['args'])
 need(set(rows)|set(p['inputs'])==live,'liveness');need(len(rows)==nop==p['live_binary_operations'],'operations');need(dict(Counter(r['op'] for r in rows.values()))==p['operation_counts'],'operation counts')
 for name,ref in p['named_registers'].items():need(type(ref) is int or ref in live,('named ref',name))
 return rows

def recurrence_norms():
 R,*xs=ring('z,a,b,c,g,e',ZZ);z=xs[0];F=z;out={}
 for i,rad in enumerate(xs[1:]):
  ev=R.zero;od=R.zero
  for mon,coef in F.items():
   k=mon[0]
   for j in range(k+1):
    mm=list(mon);mm[0]-=j;mm[i+1]+=j//2;mm=tuple(mm);target=od if j%2 else ev;target[mm]=target.get(mm,0)+coef*comb(k,j)
  F=ev*ev-rad*od*od;out[i+1]=F
 return out
NORMS=recurrence_norms()

def local_checks(p):
 rows=structure(p);mode=modeof(p);names=list(p['inputs'])+list(p['named_registers']);R,*symbols=ring(','.join(names),ZZ);s=dict(zip(names,symbols));reg=p['named_registers'];cuts={};checks=[]
 def expand(ref,cache=None):
  if cache is None:cache={}
  if type(ref) is int:return R(ref)
  if ref in cuts:return cuts[ref]
  if ref in s and ref in p['inputs']:return s[ref]
  if ref in cache:return cache[ref]
  row=rows[ref];a,b=[expand(x,cache) for x in row['args']]
  val=a+b if row['op']=='add' else a-b if row['op']=='sub' else a*b;cache[ref]=val;return val
 # Own finite local specification. Every supplied register is checked, in order.
 spec={
 'J':lambda:6*s['j']+1,'q':lambda:s['beta']*s['J']+1,'q2':lambda:s['q']**2,'W':lambda:12*s['w']+4,
 'X':lambda:s['q']*s['W'],'Y':lambda:s['q']*s['v'],'E':lambda:s['X']*s['Y'],'a':lambda:s['E']+s['Y'],'H':lambda:4*s['a']+3,'Delta':lambda:s['a']**2+s['H'],
 'F':lambda:(s['K0']+s['W'])*s['C']-s['z']*(s['q']-1),'R':lambda:(s['q']*(s['q']-s['F'])-s['C'])*(s['q2']-1)+(s['MC']+s['q']*s['MF'])*s['J'],
 'k':lambda:s['R']+1+s['h']*s['E'],'eta':lambda:s['c']-s['Y']*s['k'],'Zeta':lambda:s['eta']*(s['k']-s['eta']),
 'u':lambda:s['E']*s['Y']*s['k'],'At':lambda:s['u']*(s['u']+s['k'])+1,'c2':lambda:s['c']**2,'Am':lambda:1+s['Delta']*s['c2'],'b0':lambda:s['X']+s['a']*s['c'],
 'dguard':lambda:s['cone_A']*s['F']*s['cone_B']*s['C']-(s['q']-s['cone_A']*s['F']-s['cone_B']*s['C'])**2,
 'Ag':lambda:s['dguard']*s['Zeta']-(s['t']**2-s['dguard']-s['Zeta']+1)**2-1-s['p2']**2-s['p3']*(s['p3']+1),'I':lambda:(2*s['r']+1)*s['c2'],
 'strong_core':lambda:s['Delta']*s['I']**2,'Af':lambda:1+s['strong_core'],'Q':lambda:s['Delta']*s['strong_core'] if mode=='13' else s['I']**2,
 'S':lambda:s['Q']-s['Delta']*(s['f']**2-1),'V':lambda:s['Af']*(s['c']*s['T']-s['R'])-s['c'] if mode=='13' else s['f']*s['c']*s['T']-s['f']**2*s['R']-s['c'],
 'delta':lambda:s['Q']-1,'Cy':lambda:s['Q']*s['V']**2-1,'M':lambda:2*s['q2'],'defect':lambda:s['v']-s['q2'],'U':lambda:s['M']*s['H'],
 'D':lambda:(s['b0']+s['H']*s['gamma'])**2-s['Am'],'G':lambda:s['Ag']-s['p1']**2,'t0':lambda:2*s['u']+s['k'],'ell':lambda:s['k']**2-4,
 'xnum':lambda:s['M']*s['n']+s['defect'],
 'jcenter':lambda:s['delta']*(s['xnum']**2+s['M']*(6*s['t0']+4*s['V'])*s['xnum']+9*s['M']**2*s['ell'])-4*s['M']**2*(s['V']**2-1),
 'hcenter':lambda:12*s['delta']*s['t0']*s['V']*s['M']**2,
 }
 if mode in ['13','14']:
  spec['norm_z']=lambda:s['U']*(s['n']+s['V'])+s['M']*s['b0']+s['H']*s['defect']
 elif mode=='15':spec['norm_z']=lambda:s['M']*(s['n']+s['V'])+s['defect']
 elif mode=='15c':spec['norm_z']=lambda:s['U']*(s['n']+3*s['t0']+2*s['V'])+2*s['M']*s['b0']+s['H']*s['defect']
 scale=s['U'] if mode in ['13','14','15c'] else s['M']
 if mode=='13':
  spec.update(rad_a=lambda:81*scale**2*s['Af'],rad_b=lambda:9*scale**2*s['At'],rad_c=lambda:s['M']**2*s['Am'],rad_g=lambda:729*scale**2*s['Ag'],rad_num=lambda:scale**2*s['Cy'])
 elif mode in ['14','15']:
  spec.update(rad_a=lambda:9*scale**2*s['At'],rad_b=lambda:81*scale**2*s['Ag'],rad_num=lambda:scale**2*s['Cy'])
  if mode=='14':spec['rad_c']=lambda:s['M']**2*s['Am']
 elif mode=='15c':spec.update(rad_a=lambda:36*scale**2*s['At'],rad_b=lambda:4*s['M']**2*s['Am'],rad_num=lambda:4*scale**2*s['Cy'])
 def norm_expected():
  if mode=='16':return s['jcenter']**2+2*s['hcenter']*s['jcenter']+576*s['delta']*s['M']**4*s['At']*(1-s['V']**2)+144*s['delta']**2*s['M']**4*s['ell']*s['V']**2
  m={'13':5,'14':4,'15':3,'15c':3}[mode];power=2**(m-1);keys=['norm_z','rad_a','rad_b']+(['rad_c'] if m>=4 else [])+(['rad_g'] if m==5 else [])+['rad_num'];ans=R.zero
  for mon,coef in NORMS[m].items():
   used=[mon[0]]+list(mon[1:m+1]);last=used[-1];term=R(coef)*s['delta']**(power-last)
   for key,expo in zip(keys,used):term*=s[key]**expo
   ans+=term
  return ans
 spec['norm']=norm_expected
 for name,ref in reg.items():
  need(name in spec,('unknown named register',name));got=expand(ref);expected=spec[name]();need(got==expected,('exact register mismatch',name));cuts[ref]=s[name];checks.append({'register':name,'terms':len(expected)})
 out=s['norm']
 if mode!='13':
  out=(1+out)*(1+s['S'])
  if 'gamma' in p['variables']:out*=1+s['D']
  if 'p1' in p['variables']:out*=1+4*s['G']
  out-=1
 need(expand(p['output'])==out,'exact finalizer');return checks

class UP:
 def __init__(self,v,p):self.p=p;self.a=[x%p for x in v];self.trim()
 def trim(self):
  while len(self.a)>1 and not self.a[-1]:self.a.pop()
 def cv(self,b):return b if isinstance(b,UP) else UP([b],self.p)
 def __add__(self,b):
  b=self.cv(b);a=self.a;c=b.a;return UP([(a[i] if i<len(a) else 0)+(c[i] if i<len(c) else 0) for i in range(max(len(a),len(c)))],self.p)
 __radd__=__add__
 def __neg__(self):return UP([-x for x in self.a],self.p)
 def __sub__(self,b):return self+-self.cv(b)
 def __rsub__(self,b):return self.cv(b)+-self
 def __mul__(self,b):
  b=self.cv(b);o=[0]*(len(self.a)+len(b.a)-1)
  for i,x in enumerate(self.a):
   if x:
    for j,y in enumerate(b.a):
     if y:o[i+j]+=x*y
  return UP(o,self.p)
 __rmul__=__mul__
def replay(p,env):
 vals=dict(env)
 for row in p['nodes']:
  a,b=[x if type(x) is int else vals[x] for x in row['args']];vals[row['id']]=a+b if row['op']=='add' else a-b if row['op']=='sub' else a*b
 return vals[p['output']],vals

def fixed():
 bind=json.loads((ROOT/'coefficients/BINDING.json').read_text());out={};receipts={}
 pins=json.loads((HERE/'SOURCE_BINDINGS.json').read_text());need(sha((ROOT/pins['source17']['path']).read_bytes())==pins['source17']['sha256'],'source17 binding');need(bind['tuple']=='mixed-parity-unrounded-1064921','tuple');need(bind['MF_convention']=='MF_native + beta, already shifted','MF convention')
 for name in PORTS:
  row=bind['payloads'][name];raw=gzip.decompress((ROOT/'coefficients'/row['file']).read_bytes());need(sha(raw)==row['raw_sha256'],('payload hash',name));need(len(raw)==row['raw_bytes'],('payload bytes',name));out[name]=int.from_bytes(raw,'little');need(out[name].bit_length()==row['bits'],('payload bits',name));need(sha(raw)==pins['payloads'][name]['raw_sha256'],('upstream payload mismatch',name));receipts[name]=sha(raw)
 need(out['beta']==2**1064921-1,'beta');need(out['cone_A']==2**1113 and out['cone_B']==2**666104,'cones');return out,receipts

def degree_bounds(p):
 ds={v:1 for v in p['variables']};ds.update({v:0 for v in PORTS})
 def deg(x):return 0 if type(x) is int else ds[x]
 for row in p['nodes']:
  a,b=map(deg,row['args']);ds[row['id']]=a+b if row['op']=='mul' else max(a,b)
 regs={k:deg(v) for k,v in p['named_registers'].items()};naive=ds[p['output']];mode=modeof(p)
 if mode=='13':
  root_degrees={'strong':regs['Af']//2,'tau':regs['At']//2,'main':regs['Am']//2,'guard':regs['Ag']//2};B=max(regs['U']+1,regs['M']+regs['b0'],regs['H']+regs['defect'],regs['U']+root_degrees['strong'],regs['U']+root_degrees['tau'],regs['M']+root_degrees['main'],regs['U']+root_degrees['guard']);pair=max(regs['delta']+2*B,regs['delta']+regs['U']+regs['V']+B,2*regs['U']+2*regs['V']);upper=16*pair;detail={'paired_auxiliary_shift_weight':B,'paired_factor_bound':pair,'sixteen_factor_norm_bound':upper}
 elif mode=='15c':
  x=max(regs['U']+1,regs['M']+regs['b0'],regs['H']+regs['defect'],regs['M']+regs['Am']//2);U=regs['U'];dd=regs['delta'];V=regs['V'];tt=regs['t0'];ell=2*regs['k'];j=max(dd+max(2*x,U+max(tt,V)+x,2*U+ell),2*U+2*V);h=dd+tt+V+2*U;two=max(j+max(j,h),dd+4*U+max(regs['At']+2*V,dd+ell+2*V));norm=2*two;upper=norm+regs['S']+regs['G'];detail={'centered_shift_weight':x,'j_bound':j,'h_bound':h,'two_root_bound':two,'main_conjugate_norm_bound':norm}
 else:upper=naive;detail={'naive_bound_is_sharp':True}
 need(upper==p['exact_degree'],('upper degree',mode,upper));return {'naive_upper':naive,'proved_upper':upper,'named_degree_bounds':regs,'cancellation':detail}

def exact_identities():
 R,U,V,d,B,x,M,t,A,k,Q,c,f,T,r,Delta,Rr=ring('U,V,d,B,x,M,t,A,k,Q,c,f,T,r,Delta,Rr',ZZ)
 need(d*(U*V+B)**2-U**2*((d+1)*V**2-1)==d*B**2+2*d*U*V*B-U**2*(V**2-1),'aux cancellation')
 # Identity after ell=t²-4A, Q=delta+1: no divisions remain.
 ell=t*t-4*A;Z=x+M*(3*t+2*V);an=36*M*M*A;bn=4*M*M*((d+1)*V*V-1)
 direct=(d*(Z*Z-an)-bn)**2-4*d*an*bn
 j=d*(x*x+M*(6*t+4*V)*x+9*M*M*ell)-4*M*M*(V*V-1);h=12*d*t*V*M*M
 centered=j*j+2*h*j+576*d*M**4*A*(1-V*V)+144*d*d*M**4*ell*V*V
 need(direct==centered,'centered exact identity')
 need((2*T-(2*U+k))**2+2*(2*T-(2*U+k))*(2*U+k)+k*k-4==4*(T*T-(U*(U+k)+1)),'source midpoint')
 need(V*V+(1-Q)*(T-V)*(T+V)-1==Q*V*V-(Q-1)*T*T-1,'source aux shear')
 # Denominator-cleared ordinary quotient identities, no unjustified division.
 VV=f*c*T-f*f*Rr-c;need(VV+c==f*(c*T-f*Rr),'ordinary quotient o');need(VV+Rr==c*(f*T-1)-(f*f-1)*Rr,'ordinary quotient j')
 return {'adjacent_pair_identity':True,'centered_two_root_identity':True,'source_midpoint_identity':True,'source_auxiliary_shear_identity':True,'ordinary_quotient_identities':True,'generic_norm_monomials':{str(m):len(v) for m,v in NORMS.items()}}

def finite_semantics():
 # Diagnostics only: the accompanying proof supplies the unbounded lemmas.
 import itertools
 count=0
 for aa,cc,rr,ff,gg in itertools.product(range(4),repeat=5):
  if aa%2:continue
  DD=aa*aa+4*aa+3;II=(2*rr+1)*cc*cc;S=II*II-DD*(ff*ff-1);D=gg*gg-DD*cc*cc-1;need(S%4!=2 and D%4!=2,'unit residues');count+=1
 for N,S,D,G in itertools.product(range(-4,5),repeat=4):
  if S==-2 or D==-2:continue
  need(((1+N)*(1+S)*(1+D)*(1+4*G)==1)==(N==S==D==G==0),'unit product')
 return {'residue_cases':count,'unit_product_bounded_diagnostic':True}

def negative_controls(packets):
 results=[]
 def reject(label,p):
  try:local_checks(p)
  except (Failure,KeyError):results.append(label);return
  raise Failure(('negative control escaped',label))
 p=copy.deepcopy(packets[0]);p['exact_degree']+=1;reject('wrong degree metadata',p)
 p=copy.deepcopy(packets[0]);p['nodes'][0]['args'][0]='missing';reject('dangling input',p)
 p=copy.deepcopy(packets[0]);p['nodes'].append({'id':'audit_dead','op':'add','args':['j',1]});reject('dead node',p)
 for name in ['H','V','Cy','Ag','norm_z']:
  p=copy.deepcopy(packets[0]);ref=p['named_registers'][name];row=next(x for x in p['nodes'] if x['id']==ref);row['op']='add' if row['op']=='sub' else 'sub';p['operation_counts']=dict(Counter(x['op'] for x in p['nodes']));reject('altered '+name,p)
 p=copy.deepcopy(packets[0]);ref=p['named_registers']['norm'];row=next(x for x in p['nodes'] if x['id']==ref);row['op']='add';p['operation_counts']=dict(Counter(x['op'] for x in p['nodes']));reject('altered norm sign',p)
 p=copy.deepcopy(packets[1]);row=p['nodes'][-1];row['op']='add';p['operation_counts']=dict(Counter(x['op'] for x in p['nodes']));reject('altered finalizer',p)
 return results

def main():
 fp,hashes=fixed();ids=exact_identities();packets=[json.loads((ROOT/('integer'+m+'_degree'+str(v[1])+'.json')).read_text()) for m,v in EXPECTED.items()];results=[]
 for p in packets:
  checks=local_checks(p);bounds=degree_bounds(p);certs=[]
  for prime in [65521,65519]:
   # Independent directions differ from the builder's checker.
   slopes={v:3+2*i+i*i for i,v in enumerate(p['variables'])};env={k:UP([v%prime],prime) for k,v in fp.items()};env.update({k:UP([0,v],prime) for k,v in slopes.items()});out,ev=replay(p,env);got=len(out.a)-1;need(got==p['exact_degree'],('degree lower',p['name'],got));nn=ev[p['named_registers']['norm']];certs.append({'prime':prime,'slopes':slopes,'fixed_residues':{k:v%prime for k,v in fp.items()},'degree':got,'leading_coefficient':out.a[-1],'norm_degree':len(nn.a)-1,'norm_leading_coefficient':nn.a[-1]})
  result={'name':p['name'],'packet_sha256':sha((ROOT/(p['name']+'.json')).read_bytes()),'dimension':len(p['variables']),'live_operations':len(p['nodes']),'exact_register_checks':checks,'degree':bounds,'actual_coefficient_lower_certificates':certs};results.append(result);print(p['name'],'PASS',flush=True)
 neg=negative_controls(packets);sem=finite_semantics();receipt={'status':'PASS','python_optimized':not __debug__,'scope':'Exact universal norm expansions, all literal register and finalizer identities, structural and operation checks, proved cancellation upper bounds and independent actual-coefficient lower certificates. No upstream code is imported or executed. Unbounded source correspondence is reviewed separately.','fixed_payload_hashes':hashes,'exact_identities':ids,'packets':results,'negative_controls_rejected':neg,'finite_diagnostics':sem};path=HERE/('AUDIT.optimized.json' if not __debug__ else 'AUDIT.normal.json');path.write_text(json.dumps(receipt,indent=2)+'\n');print(path,flush=True)
if __name__=='__main__':main()
