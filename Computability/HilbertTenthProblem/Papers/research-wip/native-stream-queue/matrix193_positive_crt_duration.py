#!/usr/bin/env python3
"""Paid positive fixed-duration refinement of the centered CRT interface."""
import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

PINS={
 'matrix193_centered_crt_selector.py':'091ea1a9fae724f7dd9cab551e6938b0524677766b39f0311d9e324f8837cd28',
 'matrix193_centered_crt_selector.json':'51e304b13fbeea6d1b69a35ee8fbd3f359dfe050e2ceee177890b8b3d07d1d78',
 'matrix193_centered_crt_selector.md':'5360a8ecd24ab88eb0e7867ca98179eebfcded3a11fd427fb3923ba535106046',
 'matrix193_gamma1_recode.md':'6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742',
 'matrix193_context_absorption.md':'d7492809ba00a011c8280172bb016f96f3f6c240de6a823ed717d82bda5e4f4b',
}
COLS=['K0','K1','K2','G0','G1','G2']
CONSTS=['L','m_bias','T_squared']+['center_'+c for c in COLS]
DIRECT_POSITIVE=['bound_z_0']+['q_'+c for c in COLS]+['bound_'+c+'_'+str(j) for c in COLS for j in range(3)]
def need(ok,msg):
 if not ok:raise ValueError(msg)

def sha(b):return hashlib.sha256(b).hexdigest()

def exact(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def read_json(path):
 def pairs(items):
  out={}
  for k,v in items:need(k not in out,'duplicate key');out[k]=v
  return out
 def bad(v):raise ValueError('noninteger JSON number '+v)
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)

# Exact sparse polynomial ring; monomials are sorted tuples of variable names.
def pc(n):return {():n} if n else {}
def pv(s):return {(s,):1}
def add(a,b,sign=1):
 out=a.copy()
 for k,v in b.items():
  out[k]=out.get(k,0)+sign*v
  if not out[k]:del out[k]
 return out

def mul(a,b):
 out={}
 for x,v in a.items():
  for y,w in b.items():
   k=tuple(sorted(x+y));out[k]=out.get(k,0)+v*w
 return {k:v for k,v in out.items() if v}

def sq(a):return mul(a,a)
def psum(xs):
 out={}
 for x in xs:out=add(out,x)
 return out

def phash(p):
 h=hashlib.sha256()
 for k,v in sorted(p.items()):h.update(json.dumps([k,hex(v)],separators=(',',':')).encode()+b'\n')
 return h.hexdigest()

def pdegree(p,ports):return max((sum(x in ports for x in k) for k in p),default=-1)

class Build:
 def __init__(self):self.rows=[]
 def op(self,op,a,b):
  out='r'+str(len(self.rows));self.rows.append([out,op,a,b]);return out
 def add(self,a,b):return self.op('+',a,b)
 def sub(self,a,b):return self.op('-',a,b)
 def mul(self,a,b):return self.op('*',a,b)
 def sos(self,args):
  terms=[self.mul(a,a) for a in args];out=terms[0]
  for a in terms[1:]:out=self.add(out,a)
  return out

def audit_packet(packet,constants):
 ports=packet['ports'];seen=set(ports)|set(constants);by={};M=0;degrees={p:1 for p in ports}|{p:0 for p in constants}
 def known(x):return type(x) is int or (type(x) is str and x in seen)
 def deg(x):return 0 if type(x) is int else degrees[x]
 for row in packet['instructions']:
  need(type(row) is list and len(row)==4,'row')
  out,op,a,b=row;need(type(out) is str and out not in seen and op in ['+','-','*'] and known(a) and known(b),'closure')
  degrees[out]=deg(a)+deg(b) if op=='*' else max(deg(a),deg(b));M+=op=='*';seen.add(out);by[out]=row
 need(packet['output'] in by,'output')
 live=set();stack=[packet['output']]
 while stack:
  v=stack.pop()
  if v in live:continue
  live.add(v)
  if v in by:
   stack.extend(a for a in by[v][2:] if type(a) is str)
 need(set(by)<=live and set(ports)<=live and set(constants)<=live,'liveness')
 ledger={'M':M,'A':len(by)-M,'total':len(by)}
 return ledger,degrees[packet['output']]

def evaluate(packet,constants,ports,modulus=None):
 env=constants|ports
 def val(x):return x if type(x) is int else env[x]
 for out,op,a,b in packet['instructions']:
  A=val(a);B=val(b);v=A*B if op=='*' else A+B if op=='+' else A-B
  env[out]=v if modulus is None else v%modulus
 return env

def direct_numeric(mode,countdown,constants,ports):
 e=constants|ports;z=e['z'];m=e['L']*z+e['m_bias']
 triples=lambda prefix:sum(e[prefix+'_'+str(i)]**2 for i in range(3))
 rs=[z*z+e['bound_z_0']**2-5928325];co={}
 for c in COLS:
  rem=e['center_'+c]-m*e['q_'+c];a=e['a_'+c] if mode=='supplied' else rem;co[c]=a
  if mode=='supplied':rs.append(rem-a)
  rs.append(a*a+triples('bound_'+c)-e['T_squared'])
 for f,u,v,p,q in [('K','x0','x1','next_x0','next_x1'),('G','y0','y1','next_y0','next_y1')]:
  rs.extend([2*e[p]-co[f+'0']*e[u]-co[f+'2']*e[v],co[f+'0']*e[q]-co[f+'1']*e[p]-2*e[v]])
 U=sum(r*r for r in rs)
 if not countdown:return U
 load=(e['next_x0']-e['x0'])**2+(e['next_x1']-e['x1'])**2+(e['next_y0']-52891*e['y0']-94920*e['y1'])**2+(e['next_y1']+29036*e['y0']+52109*e['y1'])**2+(e['next_n']-e['n']+1)**2
 return load*(U+e['n']**2+e['next_n']**2)

def local_shape(parent):
 p=parent['variants']['computed_countdown']
 out={k:p[k] for k in ['ports','instructions','output','residual_wires','sync_output','sync_rows','m_wire','coefficient_wires']}
 out['domain']='Signed state and selector z; circle root, six CRT quotients and eighteen sphere roots are positive integers without changing state zero-projection.'
 out['ledger'],out['degree_upper']=audit_packet(out,CONSTS)
 need(out['ledger']=={'M':64,'A':69,'total':133} and out['degree_upper']==10,'local count')
 need(out['instructions']==parent['variants']['computed_countdown']['instructions'],'exact parent local rows')
 return out

def interpret(packet,values):
 env=values.copy()
 def value(v):return pc(v) if type(v) is int else env[v]
 for out,op,a,b in packet['instructions']:
  A=value(a);B=value(b);env[out]=mul(A,B) if op=='*' else add(A,B,1 if op=='+' else -1)
 return env

def full_numeral_pullback(local,oldconstants,newconstants,M):
 # Independent formal constant ports: shifting the six centers is an all-value pullback.
 ports={p:pv(p) for p in local['ports']};formal={c:pv(c) for c in CONSTS}
 original=interpret(local,ports|formal)[local['output']]
 shift={c:(add(pv(c),pv('CRT_product')) if c.startswith('center_') else pv(c)) for c in CONSTS}
 shifted=interpret(local,ports|shift)[local['output']]
 # Fresh polynomial substitution of the already expanded original, independent of DAG evaluation.
 mapped={}
 for monomial,coefficient in original.items():
  term=pc(coefficient)
  for name in monomial:term=mul(term,shift.get(name,pv(name)))
  mapped=add(mapped,term)
 need(mapped==shifted,'whole fixed-numeral pullback')
 for name in CONSTS:need(newconstants[name]==oldconstants[name]+(M if name.startswith('center_') else 0),'fixed numeral shift')
 return {'formal_template_terms':len(original),'formal_template_sha256':phash(original),'shifted_formal_terms':len(shifted),'shifted_sha256':phash(shifted),'scope':'Complete all-value substitution center_c -> center_c + CRT_product relative to the newly recompiled unshifted T/L/CRT frame. It is not a pullback of the numerical constants of the old parent. Source instructions and variable ports are unchanged.'}

def positive_history(h,local,parent,constants):
 b=Build();inverse={};positive_ports=[];direct_ports=[];signed_ports=[]
 local_aux=[p for p in local['ports'] if p not in ['x0','x1','y0','y1','next_x0','next_x1','next_y0','next_y1','n','next_n']]
 step_supplied=['next_x0','next_x1','next_y0','next_y1','next_n']+local_aux
 need(len(step_supplied)==31 and set(DIRECT_POSITIVE)<=set(local_aux),'step interface')
 for step in range(h):
  for name in step_supplied:
   key='s'+str(step)+'_'+name;pos='positive_'+key;positive_ports.append(pos)
   if name in DIRECT_POSITIVE:inverse[key]=pos;direct_ports.append(pos)
   else:inverse[key]=b.sub(pos,'offset');signed_ports.append(pos)
 initial=parent['initial_state'];state={'x0':initial['X'][0],'x1':initial['X'][1],'y0':initial['Y'][0],'y1':initial['Y'][1],'n':'ordinary_x'};outs=[];step_maps=[]
 for step in range(h):
  rename=state.copy();rename.update({p:inverse['s'+str(step)+'_'+p] for p in step_supplied});step_maps.append(rename.copy())
  for out,op,a,c in local['instructions']:rename[out]=b.op(op,rename.get(a,a),rename.get(c,c))
  outs.append(rename[local['output']]);state={p:rename['next_'+p] for p in ['x0','x1','y0','y1','n']}
 rename=state.copy();endpoint=parent['endpoint']
 for out,op,a,c in endpoint['instructions']:rename[out]=b.op(op,rename.get(a,a),rename.get(c,c))
 total=rename[endpoint['output']]
 for out in outs:total=b.add(total,out)
 packet={'duration':h,'domain':'ordinary_x natural, all listed witness ports positive integers','witness_ports':['offset']+positive_ports,'ports':['ordinary_x','offset']+positive_ports,'direct_positive_ports':direct_ports,'offset_reconstructed_ports':signed_ports,'instructions':b.rows,'output':total,'state_reconstruction_rows':6*h,'local_instances':h,'endpoint_rows':7,'final_joins':h}
 packet['ledger'],packet['degree_upper']=audit_packet(packet,CONSTS)
 need(len(direct_ports)==25*h and len(signed_ports)==6*h,'positive roles')
 need(packet['ledger']['total']==140*h+7 and len(packet['witness_ports'])==31*h+1 and packet['degree_upper']<=10,'positive ledger')
 for seed in range(8):
  ports={p:1+(j+seed)%7 for j,p in enumerate(positive_ports)}|{'offset':3+seed,'ordinary_x':seed}
  for prime in (1000000007,1000000009):
   env=evaluate(packet,constants,ports,prime);direct=0;reduced={k:v%prime for k,v in constants.items()}
   for mapping in step_maps:
    localports={p:(v if type(v) is int else env[v]) for p,v in mapping.items()}
    direct+=direct_numeric('computed',True,reduced,localports)
   final={p:(v if type(v) is int else env[v]) for p,v in state.items()}
   direct+=(final['x0']-final['y0'])**2+(final['x1']-final['y1'])**2+final['n']**2
   need(env[total]==direct%prime,'full positive history modular composition')
 packet['complete_source_modular_composition_checks']=16
 return packet


def prime(n):
 return type(n) is int and n>=2 and all(n%d for d in range(2,math.isqrt(n)+1))

def compile_positive_frame(parent):
 table=parent['transition_table'];labels=parent['selector_labels'];recipe=parent['fixed_numeral_recipe']
 need(len(table)==len(labels)==96 and math.isqrt(5928325)**2!=5928325,'nonsquare selector')
 entries=sorted({abs(2*row[f][j]) for row in table for f in ['K','G'] for j in range(3)});nonzero=[A for A in entries if A]
 value=3;period=6;p=7;constraints=[]
 for A in nonzero:
  while not prime(p) or A%p==0:p+=4
  modulus=p*p;residue=(A+p)%modulus
  value+=((residue-value)*pow(period,-1,modulus)%modulus)*period;period*=modulus;value%=period
  constraints.append({'absolute_doubled_entry':A,'prime':p,'modulus':modulus,'T_residue':residue});p+=4
 bound=max(entries);T=value+max(0,(bound+1-value+period-1)//period)*period
 need(T>bound and T%6==3,'positive odd T divisible3')
 for rec in constraints:
  A=rec['absolute_doubled_entry'];p=rec['prime'];gap=T*T-A*A
  need(prime(p) and p%4==3 and p!=3 and (2*A)%p!=0,'prime hypotheses')
  need(T%(p*p)==rec['T_residue'] and gap%p==0 and gap%(p*p)!=0 and gap%8 in (1,5),'exact valuation and Legendre hypothesis')
 need(len({r['prime'] for r in constraints})==len(constraints),'distinct T primes')
 support=recipe['difference_primes'];L0=math.prod(support);zs=[r['label'] for r in labels]
 need(all(prime(p) for p in support),'difference primes')
 for i,z in enumerate(zs):
  for w in zs[:i]:
   rem=z-w
   for p in support:
    while rem%p==0:rem//=p
   need(rem==1,'complete difference prime support')
 L=L0*max(1,(2*T+1+L0-1)//L0);moduli=[1+(z+2435)*L for z in zs];M=math.prod(moduli)
 need(all(m>2*T for m in moduli) and all(math.gcd(m,n)==1 for i,m in enumerate(moduli) for n in moduli[:i]),'new moduli')
 partial=[M//m for m in moduli];inverses=[pow(p,-1,m) for p,m in zip(partial,moduli)]
 unshifted={'L':L,'m_bias':2435*L+1,'T_squared':T*T};constants=unshifted.copy();qchecks=0
 for c in COLS:
  vals=[2*row[c[0]][int(c[1])] for row in table]
  C=sum((A+T)*part*inv for A,part,inv in zip(vals,partial,inverses))%M
  unshifted['center_'+c]=C-T;constants['center_'+c]=C+M-T
  for A,m in zip(vals,moduli):
   residue=A+T;need(0<residue<2*T<m and C%m==residue,'recompiled canonical CRT')
   oldq,r=divmod(C-residue,m);q,r2=divmod(constants['center_'+c]-A,m)
   need(r==r2==0 and oldq>=0 and M//m>=2 and q==oldq+M//m>0,'positive quotient');qchecks+=1
 for i,(row,label) in enumerate(zip(table,labels)):
  need(label['table_index']==i and label['tile_id']==row['tile_id'] and label['circle_witness']>0,'positive label')
  need(label['label']**2+label['circle_witness']**2==5928325,'circle identity')
  for family in ['K','G']:
   a,b,c,d=row[family];need(a*d-b*c==1 and a%5==1,'inherited group pivot')
 metadata={'T_recipe':'Assign successive distinct primes p=3 mod4 starting7, skipping composite primes and divisors of the absolute doubled entry. CRT T=3 mod6 and T=abs(A)+p modp^2; lift the least residue by its full period until T>max abs(A).','T_constraints':constraints,'T_hex':hex(T),'T_bits':T.bit_length(),'T_period_hex':hex(period),'T_period_bits':period.bit_length(),'zero_entry_branch_used':0 in entries,'L_recipe':'L0*max(1,ceil((2T+1)/L0)) with the pinned circle difference-prime radical L0.','L0_bits':L0.bit_length(),'L_bits':L.bit_length(),'moduli_hex':[hex(m) for m in moduli],'M_hex':hex(M),'M_bits':M.bit_length(),'column_recipe':'Recompile least nonnegative C_c with residue T+2entry at the new moduli, then bind center_c=C_c+M-T.','positive_quotient_checks':qchecks,'valuation_checks':len(constraints),'fixed_numerals':{k:{'hex':hex(v),'bit_length':abs(v).bit_length(),'sha256_hex':sha(hex(v).encode())} for k,v in constants.items()},'maximum_fixed_numeral_bits':max(abs(v).bit_length() for v in constants.values())}
 return unshifted,constants,M,metadata

def bounded_checks(local,constants):
 # Small sphere components demonstrate both branches, not the huge actual T.
 fixtures=[{'A':0,'T':3,'roots':[2,2,1]}, {'A':2,'T':9,'prime':7,'roots':[2,3,8]}, {'A':-4,'T':15,'prime':11,'roots':[3,10,10]}]
 for f in fixtures:
  A=f['A'];T=f['T'];roots=f['roots'];gap=T*T-A*A
  need(T>abs(A) and T%6==3 and all(x>0 for x in roots) and sum(x*x for x in roots)==gap,'small positive sphere')
  if A:
   p=f['prime'];need(prime(p) and p%4==3 and gap%p==0 and gap%(p*p)!=0,'small valuation')
 source_checks=loads=0
 for seed in range(12):
  ports={p:((seed+3)*(i+7)%23)-11 for i,p in enumerate(local['ports'])}
  for q in (1000000007,1000000009):
   reduced={k:v%q for k,v in constants.items()}
   need(evaluate(local,constants,ports,q)[local['output']]==direct_numeric('computed',True,reduced,ports)%q,'full modular local formula');source_checks+=1
 for seed in range(4):
  ports={p:(j+seed)%7-3 for j,p in enumerate(local['ports'])};ports.update({p:1+seed for p in DIRECT_POSITIVE})
  ports.update({'x0':2,'x1':-1,'next_x0':2,'next_x1':-1,'y0':-3,'y1':4,'next_y0':-3*52891+4*94920,'next_y1':3*29036-4*52109,'n':seed,'next_n':seed-1})
  need((ports['next_x0']-ports['x0'])**2+(ports['next_x1']-ports['x1'])**2+(ports['next_y0']-52891*ports['y0']-94920*ports['y1'])**2+(ports['next_y1']+29036*ports['y0']+52109*ports['y1'])**2+(ports['next_n']-ports['n']+1)**2==0,'exact LOAD factor')
  for q in (1000000007,1000000009):need(evaluate(local,constants,ports,q)[local['output']]==0,'modular full LOAD source');loads+=1
 return {'small_positive_sphere_fixtures':fixtures,'complete_modular_source_formula_checks':source_checks,'complete_modular_LOAD_zeros':loads,'exact_LOAD_factor_fixtures':4,'scope':'Small sphere examples are component checks, not the actual recompiled large-T tile witnesses. Actual large-T triple existence follows from the proved valuation/Legendre argument. No full large-T tile zero tuple is materialized.'}

def make(root):
 for name,pin in PINS.items():need(sha((root/name).read_bytes())==pin,'pin '+name)
 parent=read_json(root/'matrix193_centered_crt_selector.json');need(parent['source_sha256']==PINS['matrix193_centered_crt_selector.py'],'parent source identity')
 unshifted,constants,M,recipe=compile_positive_frame(parent);local=local_shape(parent)
 pullback=full_numeral_pullback(local,unshifted,constants,M)
 need(pullback['formal_template_sha256']==parent['variants']['computed_countdown']['formal_identity']['sha256'],'parent full formal grammar')
 env={p:{} for p in local['ports']}|{k:pv(k) for k in CONSTS};env['z']=pv('t');env['q_K0']=pv('t');env['n']=pv('t')
 line=interpret(local,env)[local['output']];degree=pdegree(line,{'t'})
 leading={tuple(v for v in mon if v!='t'):a for mon,a in line.items() if mon.count('t')==10}
 need(degree==10 and leading=={('L','L','L','L'):1} and constants['L']>0,'uniform nonzero degree leader')
 local['degree_certificate']={'degree':10,'line':'all state and root ports zero; z=q_K0=n=t; all other quotients zero; constants remain formal','formal_leading_coefficient':'L^4','polynomial_sha256':phash(line)}
 checks=bounded_checks(local,constants);positive={str(h):positive_history(h,local,parent,constants) for h in [1,2]}
 return {'schema':'matrix193-positive-crt-duration-v1','status':'PASS_COMPLETE_POSITIVE_FIXED_DURATION_INTERFACE','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'predecessor_code_executed':False,'fixed_numeral_recipe':recipe,'direct_positive_auxiliary_names':DIRECT_POSITIVE,'local_packet':local,'full_fixed_numeral_pullback':pullback,'finite_checks':checks,'positive_fixed_duration_sources':positive,'initial_state':parent['initial_state'],'endpoint':parent['endpoint'],'uniform_fixed_context_recipe':{'scope':'All inherited fixed contexts in Hprime subset Gamma1(5), preserving96 actions, nonzero pivots and the same nonsquare circle. Recompile T by the valuation recipe, enlarge L, and shift each new CRT value by the new full product. Numeric arrays remain the selected fixture.','local_operations':133,'positive_fixed_duration_operations':'140h+7','positive_witnesses':'31h+1','degree_upper':10,'signed_reconstructions_per_step':6,'direct_positive_auxiliaries_per_step':25},'scope':'Paid positive fixed-duration integer certificate; no fixed-arity unbounded packing and no real exactness claim. Its projected integer history relation equals the parent relation after reselecting sphere roots and node-dependent quotients. No unrestricted numerical quotient-coordinate pullback or auxiliary-fiber bijection is claimed.'}

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,required=True)
 g=p.add_mutually_exclusive_group(required=True);g.add_argument('--expect',type=Path);g.add_argument('--output',type=Path);a=p.parse_args();r=make(a.root)
 if a.output:
  with a.output.open('x') as f:json.dump(r,f,indent=2,sort_keys=True);f.write('\n')
 else:need(exact(r,read_json(a.expect)),'exact receipt')
 print('PASS: positive CRT duration140h+7; complete147/287 arrays,25 direct positive auxiliaries and6h paid reconstructions')

if __name__=='__main__':main()
