#!/usr/bin/env python3
"""Independent exact audit of the new coprime-quintic twelve-integer DAG.
Imports only the earlier independent audit's generic norm recurrence and
arithmetic helpers, never a builder or upstream executable source.
"""
from pathlib import Path
import sys,json,gzip,hashlib,copy
from collections import Counter
from sympy import ZZ
from sympy.polys.rings import ring
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent/'radicals12'
sys.path.insert(0,str(HERE.parent/'radicals_audit'))
from check_radicals import NORMS,UP,replay,need,Failure,sha
VARS=['j','C','z','h','r','v','w','T','c','n','t','s0'];PORTS=['beta','K0','MC','MF','cone_A','cone_B']
def structural(p):
 need(p['variables']==VARS,'variables');need(p['inputs']==VARS+PORTS,'inputs');need(p['fixed_ports']==PORTS,'ports');need(p['variable_count']==12,'dimension');need(p['exact_degree']==2048,'degree metadata');need(p['coefficient_binding']=='coefficients/BINDING.json','binding path');need(p['domain']=='unrestricted integers','domain');need(p['representation']=='division-free arithmetic DAG','representation')
 seen=set(p['inputs']);rows={}
 for n in p['nodes']:
  need(n['id'] not in seen,'duplicate id');need(n['op'] in ['add','sub','mul'],'operation');need(len(n['args'])==2,'arity');need(all(type(x) is int or x in seen for x in n['args']),'topology');seen.add(n['id']);rows[n['id']]=n
 live=set();todo=[p['output']]
 while todo:
  x=todo.pop()
  if type(x) is int or x in live:continue
  need(x in seen,'unknown output');live.add(x)
  if x in rows:todo+=rows[x]['args']
 need(live==set(rows)|set(p['inputs']),'liveness');need(len(rows)==233==p['live_binary_operations'],'operation count');need(p['operation_counts']==dict(Counter(n['op'] for n in p['nodes']))=={'mul':148,'add':53,'sub':32},'operation partition');return rows

def exact(p,check_structure=True):
 rows=structural(p) if check_structure else {n['id']:n for n in p['nodes']};names=p['inputs']+list(p['named_registers']);R,*vs=ring(','.join(names),ZZ);s=dict(zip(names,vs));cuts={};reg=p['named_registers'];results=[]
 def expand(x,cache=None):
  if cache is None:cache={}
  if type(x) is int:return R(x)
  if x in cuts:return cuts[x]
  if x in p['inputs']:return s[x]
  if x in cache:return cache[x]
  row=rows[x];a,b=[expand(v,cache) for v in row['args']];z=a+b if row['op']=='add' else a-b if row['op']=='sub' else a*b;cache[x]=z;return z
 spec={
 'J':lambda:6*s['j']+1,'q':lambda:s['beta']*s['J']+1,'W':lambda:12*s['w']+4,'X':lambda:s['q']*s['W'],'Y':lambda:s['q']*s['v'],'E':lambda:s['X']*s['Y'],'a':lambda:s['E']+s['Y'],'H':lambda:4*s['a']+3,'Delta':lambda:s['a']**2+s['H'],
 'F':lambda:(s['K0']+s['W'])*s['C']-s['z']*(s['q']-1),'R':lambda:(s['q']*(s['q']-s['F'])-s['C'])*(s['q']**2-1)+(s['MC']+s['q']*s['MF'])*s['J'],'k':lambda:s['R']+1+s['h']*s['E'],'eta':lambda:s['c']-s['Y']*s['k'],'Zeta':lambda:s['eta']*(s['k']-s['eta']),
 'det':lambda:s['cone_A']*s['F']*s['cone_B']*s['C']-(s['q']-s['cone_A']*s['F']-s['cone_B']*s['C'])**2,'P':lambda:s['det']*s['Zeta']-(s['t']**2-s['det']-s['Zeta']+1)**2,'s':lambda:3*s['s0'],'Dg':lambda:(3*s['P']-4)*s['s']**2+1,
 'I':lambda:s['s']*s['r']*s['c']**2,'Df':lambda:1+s['Delta']*s['I']**2,'Q':lambda:s['Delta']**2*s['I']**2,'delta':lambda:s['Q']-1,'V':lambda:s['Df']*(s['c']-s['R']+4*s['I']*s['T'])-s['c'],'Cy':lambda:s['Q']*s['V']**2-1,'Da':lambda:s['delta']*s['Cy'],
 'ell':lambda:s['E']*s['Y']*s['k'],'Dt':lambda:1+s['ell']*(s['ell']+s['k']),'Dm':lambda:1+s['Delta']*s['c']**2,'b0':lambda:s['X']+s['a']*s['c'],'M':lambda:2*s['q']**2,'L':lambda:s['M']*s['H'],'defect':lambda:s['v']-s['q']**2,'btilde':lambda:s['M']*s['b0']+s['H']*s['defect'],'u':lambda:s['L']*s['T']-s['btilde'],'Dtilde':lambda:s['M']**2*s['Dm'],'L5':lambda:s['L']**5,
 'A':lambda:s['u']**5+10*s['u']**3*s['Dtilde']+5*s['u']*s['Dtilde']**2+32*s['L']**2*(s['u']**3+3*s['u']*s['Dtilde'])+s['L']**3*(s['u']**2+s['Dtilde'])+31*s['L']**4*s['u']+31*s['L5'],
 'B':lambda:5*s['u']**4+10*s['u']**2*s['Dtilde']+s['Dtilde']**2+32*s['L']**2*(3*s['u']**2+s['Dtilde'])+2*s['L']**3*s['u']+31*s['L']**4,
 'S':lambda:s['I']*s['L5'],'Caux':lambda:(2*s['Q']-1)*s['V'],'norm_z':lambda:s['S']*(s['n']+s['Caux'])-s['A'],
 'rad_aux':lambda:4*s['S']**2*s['Da'],'rad_strong':lambda:36*s['S']**2*s['Df'],'rad_main':lambda:s['B']**2*s['Dtilde'],'rad_guard':lambda:2916*s['S']**2*s['Dg'],'rad_first':lambda:324*s['S']**2*s['Dt']}
 def norm():
  out=R.zero;keys=['norm_z','rad_aux','rad_strong','rad_main','rad_guard','rad_first']
  for mon,c in NORMS[5].items():
   term=R(c)
   for k,n in zip(keys,mon):term*=s[k]**n
   out+=term
  return out
 spec['norm']=norm
 for name,ref in reg.items():
  need(name in spec,('unknown register',name));got=expand(ref);want=spec[name]();need(got==want,('exact mismatch',name));cuts[ref]=s[name];results.append({'register':name,'expanded_terms':len(want)})
 need(expand(p['output'])==s['norm'],'output');return results

def algebra():
 R,u,L,D,x,d,I,S,B,A,V,Q,M,H,gamma,e,T,c,r,Rk,Delta,f=ring('u,L,D,x,d,I,S,B,A,V,Q,M,H,gamma,e,T,c,r,Rk,Delta,f',ZZ)
 # Independent coefficient extraction from the factored homogeneous quintic.
 phi=((u+x)**2+31*L**2)*((u+x)**3+L**2*(u+x)+L**3);ev=R.zero;od=R.zero;ix=R.gens.index(x);idD=R.gens.index(D)
 for mon,co in phi.items():
  mm=list(mon);power=mm[ix];mm[ix]=0;mm[idD]+=power//2;dest=od if power%2 else ev;mm=tuple(mm);dest[mm]=dest.get(mm,0)+co
 AA=u**5+10*u**3*D+5*u*D**2+32*L**2*(u**3+3*u*D)+L**3*(u**2+D)+31*L**4*u+31*L**5
 BB=5*u**4+10*u*u*D+D*D+32*L*L*(3*u*u+D)+2*L**3*u+31*L**4
 need(ev==AA and od==BB,'quintic split');positive=5*u**4+10*u*u*D+D*D+32*L*L*D+95*L*L*u*u+L*L*(u+L)**2+30*L**4;need(BB==positive,'B positivity decomposition')
 need(((2*Q-1)*V)**2-4*(Q-1)*(Q*V*V-1)==V*V+4*Q-4,'auxiliary centered cancellation')
 need((S*(2*Q-1)*V+B)**2-4*S*S*(Q-1)*(Q*V*V-1)==B*B+2*S*(2*Q-1)*V*B+S*S*(V*V+4*Q-4),'paired norm identity')
 # Strong and auxiliary quotient restoration, normalized I=s*r*c².
 ss=d;II=ss*r*c*c;ff2=1+Delta*II*II;VV=ff2*(c-Rk+4*II*T)-c;jj=Delta*ss*ss*r*r*c**3*(c-Rk)+4*ss*r*c*ff2*T;need(VV+Rk==c*jj,'quotient j');need(VV+c==ff2*(c-Rk+4*II*T),'quotient o')
 # Specialization S=0 of the universal norm, checked exactly.
 zero=R.zero;vals=[-A,zero,zero,B*B*D,zero,zero];out=R.zero
 for mon,co in NORMS[5].items():
  term=R(co)
  for v,n in zip(vals,mon):
   if n:term*=v**n
  out+=term
 need(out==(A*A-B*B*D)**16,'I zero specialization')
 return {'quintic_factor_reduction':True,'positive_B_decomposition':True,'centered_auxiliary_pair_identity':True,'I_zero_norm_identity':True,'normalized_quotient_identities':True,'generic_F5_terms':len(NORMS[5])}

def degree(p):
 ds={x:1 for x in VARS};ds.update({x:0 for x in PORTS})
 def get(x):return 0 if type(x) is int else ds[x]
 for row in p['nodes']:
  a,b=map(get,row['args']);ds[row['id']]=a+b if row['op']=='mul' else max(a,b)
 de={k:get(v) for k,v in p['named_registers'].items()};B=max(de['S']+1,de['A'],de['rad_main']//2,de['rad_strong']//2,de['rad_first']//2,de['rad_guard']//2);parts=[2*B,de['S']+de['Caux']+B,2*de['S']+max(2*de['V'],de['Q'])];need(B==49 and parts==[98,128,110],'paired degree bounds');need(16*max(parts)==2048,'upper');need(de['rad_guard']//2==49 and max(de['rad_main']//2,de['rad_strong']//2,de['rad_first']//2,de['S']+1,de['A'])<49,'unique highest paired radical');return {'naive_DAG_upper':get(p['output']),'named_upper_bounds':de,'Bother_bound':B,'paired_term_bounds':parts,'proved_upper':2048,'leading_form':'108^16 * S_top^32 * Caux_top^16 * Dg_top^8'}

def payloads():
 binding=json.loads((ROOT/'coefficients/BINDING.json').read_text());pins=json.loads((HERE.parent/'radicals_audit/SOURCE_BINDINGS.json').read_text());out={};receipt={}
 for n in PORTS:
  row=binding['payloads'][n];raw=gzip.decompress((ROOT/'coefficients'/row['file']).read_bytes());need(sha(raw)==row['raw_sha256']==pins['payloads'][n]['raw_sha256'],('coefficient binding',n));out[n]=int.from_bytes(raw,'little');need(out[n].bit_length()==row['bits'] and len(raw)==row['raw_bytes'],('coefficient length',n));receipt[n]=sha(raw)
 need(out['beta']==2**1064921-1 and out['cone_A']==2**1113 and out['cone_B']==2**666104,'explicit coefficients');return out,receipt

def controls(p):
 reports=[]
 for name in ['s','Dg','I','V','M','btilde','A','B','Caux','norm_z','rad_guard','norm']:
  bad=copy.deepcopy(p);ref=bad['named_registers'][name];row=next(x for x in bad['nodes'] if x['id']==ref);row['op']='add' if row['op']=='sub' else 'sub'
  try:exact(bad,check_structure=False)
  except Failure:reports.append('altered '+name);continue
  raise Failure(('negative control accepted',name))
 return reports

def selected_leading_monomial():
 def mul(*terms):
  out={}
  for term in terms:
   for k,v in term.items():out[k]=out.get(k,0)+v
  return out
 def pw(term,n):return {k:v*n for k,v in term.items()}
 q={'2':1,'3':1,'beta':1,'j':1};a=mul({'2':2,'3':1,'w':1,'v':1},pw(q,2));ii={'3':1,'s0':1,'r':1,'c':2};ll=mul({'2':3},pw(q,2),a);ss=mul(ii,pw(ll,5));ca=mul({'2':3,'T':1},pw(a,6),pw(ii,5));dg=mul({'3':3,'s0':2},pw(mul(q,{'v':1,'h':1},a),4));out=mul({'2':32,'3':48},pw(ss,32),pw(ca,16),pw(dg,8));want={'2':2064,'3':1400,'beta':928,'j':928,'w':288,'v':320,'h':32,'s0':128,'r':112,'c':224,'T':16};need(out==want,'selected monomial');need(sum(v for k,v in out.items() if k not in ['2','3','beta'])==2048,'selected degree');return {'coefficient':'2^2064 * 3^1400 * beta^928','monomial':{k:v for k,v in out.items() if k not in ['2','3','beta']},'uniqueness':'h^32 forces all k_top factors to h*a_top; T^16 forces all (4I_top*T-R_top) factors to 4I_top*T.'}

def elementary_diagnostics():
 from math import gcd
 def pell(A,n,mod=None):
  x,y=1,0
  for _ in range(n):
   x,y=A*x+(A*A-1)*y,x+A*y
   if mod:x%=mod;y%=mod
  return x,y
 for A in [2,4,6,8,10]:
  for n in range(1,33):
   f,I=pell(A,n);need(gcd(n,I*I)!=0 and I%gcd(n,I*I)==0,'valuation diagnostic')
 f,I=pell(2,2);bad=pell(2,8,f*f);good=pell(2,8*f,f*f);need(bad!=(1,0),'missing period counterexample');need(good==(1,0),'correct period diagnostic')
 for t in range(4):
  for z in range(4):
   P=-(t*t-z+1)**2;need(P%4 in [0,3],'P residue diagnostic')
 need((5*2**4+10*2**2+1)%3==1,'B local unit diagnostic')
 return {'valuation_gcd_cases':160,'incorrect_4n_period_counterexample':{'A':2,'n':2,'f':f,'I':I,'modulus':f*f,'coordinates_at_4n':bad,'coordinates_at_4nf':good},'P_mod4_excludes_1':True,'B_mod3_unit':True,'scope':'Finite diagnostics, not substitutes for the unbounded proof.'}

def source_bindings():
 pins=json.loads((ROOT/'SOURCE_PINS.json').read_text());need(pins['source_archive_sha256']=='f44b903de17a70316787ff57562a3d8fe3bdec12791e266318cedb49e7125f72','late source archive');need(pins['source_repository_snapshot']=='04a1d79222d55cabe4ba52897863fc33baa8c268','late source snapshot')
 for row in pins['files']:
  path=ROOT/row['path'];need(path.resolve().is_relative_to(ROOT.resolve()),'source path scope');need(sha(path.read_bytes())==row['sha256'],('source hash',row['path']))
 need(sha((ROOT/'inherited/INTERPOLATION12.md').read_bytes())=='fc6254eb1c892f7777ddd9f65207ba343586fe2fa1f373b3d4a7e61482e87da7','interpolation proof pin');return {'source_archive_sha256':pins['source_archive_sha256'],'repository_snapshot':pins['source_repository_snapshot'],'copied_source_files_checked':len(pins['files'])}

def main():
 p=json.loads((ROOT/'integer12_degree2048.json').read_text());checks=exact(p);identities=algebra();bounds=degree(p);fp,hashes=payloads();certs=[]
 for prime in [65521,65519]:
  slopes={v:5+3*i+i*i for i,v in enumerate(VARS)};env={k:UP([v%prime],prime) for k,v in fp.items()};env.update({k:UP([0,v],prime) for k,v in slopes.items()});poly,vals=replay(p,env);need(len(poly.a)-1==2048,'degree lower');S=vals[p['named_registers']['S']];Ca=vals[p['named_registers']['Caux']];Dg=vals[p['named_registers']['Dg']];want=pow(108,16,prime)*pow(S.a[-1],32,prime)*pow(Ca.a[-1],16,prime)*pow(Dg.a[-1],8,prime)%prime;need(poly.a[-1]==want!=0,'leading polynomial');certs.append({'prime':prime,'slopes':slopes,'fixed_port_residues':{k:v%prime for k,v in fp.items()},'exact_degree':2048,'leading_coefficient':poly.a[-1],'derived_leading_coefficient':want});print('degree certificate',prime,'PASS',flush=True)
 neg=controls(p);result={'status':'PASS','python_optimized':not __debug__,'scope':'Independent exact universal arithmetic and degree audit; unbounded arithmetic and inherited calibration reviewed in AUDIT_REVIEW.md. No builder or upstream code executed.','packet_sha256':sha((ROOT/'integer12_degree2048.json').read_bytes()),'variables':12,'live_binary_operations':233,'operation_counts':p['operation_counts'],'payload_raw_sha256':hashes,'exact_local_checks':checks,'universal_identities':identities,'degree_bounds':bounds,'degree_certificates':certs,'negative_controls_rejected':neg,'selected_leading_monomial':selected_leading_monomial(),'elementary_diagnostics':elementary_diagnostics(),'source_bindings':source_bindings()};dest=HERE/('AUDIT.optimized.json' if not __debug__ else 'AUDIT.normal.json');dest.write_text(json.dumps(result,indent=2)+'\n');print(dest,flush=True)
if __name__=='__main__':main()
