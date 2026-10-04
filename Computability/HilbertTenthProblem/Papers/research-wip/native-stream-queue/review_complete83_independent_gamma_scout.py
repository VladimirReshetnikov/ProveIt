#!/usr/bin/env python3
"""Independent bounded source and input-fiber review; no historical Python imports."""
import argparse
import hashlib
import json
from fractions import Fraction
from math import gcd, lcm
from pathlib import Path

AUTHOR = {
 '.py':'b67ee981d5475a745094924d6ec3cbe72dfb38e3d28d9bd2c144ff0c2a59dc18',
 '.json':'ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20',
 '.md':'bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41'}
STEM='complete83_independent_gamma_scout'

def need(ok,msg):
 if not ok: raise ValueError(msg)
def sha(raw): return hashlib.sha256(raw).hexdigest()
def exact(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def unique(pairs):
 out={}
 for k,v in pairs:
  need(k not in out,'duplicate JSON key');out[k]=v
 return out
def reject(x):raise ValueError('nonfinite JSON '+x)
def read(path):return json.loads(path.read_text(),object_pairs_hook=unique,parse_constant=reject)
def run(rows,assignment):
 env=dict(assignment)
 for n,op,a,b in rows:
  x=env[a] if type(a) is str else a;y=env[b] if type(b) is str else b
  env[n]=x*y if op=='*' else x+y if op=='+' else x-y
 return env

def add(a,b,sign=1):
 r=[0]*max(len(a),len(b))
 for i,v in enumerate(a):r[i]+=v
 for i,v in enumerate(b):r[i]+=sign*v
 while len(r)>1 and r[-1]==0:r.pop()
 return r
def mul(a,b):
 r=[0]*(len(a)+len(b)-1)
 for i,v in enumerate(a):
  for j,w in enumerate(b):r[i+j]+=v*w
 while len(r)>1 and r[-1]==0:r.pop()
 return r
def polynomial_run(rows,assignment):
 env=dict(assignment)
 for n,op,a,b in rows:
  x=env[a] if type(a) is str else [a];y=env[b] if type(b) is str else [b]
  env[n]=mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
 return env

def pell(A,n,modulus=None):
 D=A*A-1;out=(1,0);base=(A,1)
 def product(a,b):
  x=a[0]*b[0]+D*a[1]*b[1];y=a[0]*b[1]+a[1]*b[0]
  return (x,y) if modulus is None else (x%modulus,y%modulus)
 while n:
  if n&1:out=product(out,base)
  base=product(base,base);n//=2
 return out

def fiber_checks():
 records=[];components=[];indices=comparisons=0
 for a in [6,12,18]:
  A=a+2;Delta=A*A-1;H=4*a+3
  powers=[];z=1
  while not powers or z!=1:
   need(z not in powers,'return before initial residue');powers.append(z);z=2*z%H
  O=len(powers);g=gcd(2*Delta,O);period=lcm(2*Delta,O)
  us=[1,3,5,7];observed={u:set() for u in us}
  for v in range(period):
   chi,psi=pell(A,v,Delta*H);residue=(chi-a*psi)%H
   need(residue==pow(2,v,H),'binary Pell power congruence')
   for u in us:
    if psi%Delta==u:observed[u].add(residue)
  for u in us:
   predicted={W for j,W in enumerate(powers) if (j-u)%g==0 or (j-A*u)%g==0}
   need(predicted==observed[u],'full period projection')
   for W in range(H):
    need((W in observed[u])==(W in predicted),'all H residues');comparisons+=1
   need(all(W%3==2 for j,W in enumerate(powers) if (j-u)%g==0),'odd branch residue')
   need(all(W%3==1 for j,W in enumerate(powers) if (j-A*u)%g==0),'even branch residue')
  for v in [5,8,11,20]:
   chi,psi=pell(A,v);u=psi%Delta
   if u%2==0:u+=Delta
   for shift in [0,1]:
    W=pow(2,v,H)-shift*H
    dn,dr=divmod(psi-u,Delta);rn,rr=divmod(chi-a*psi-W,H)
    need(dr==rr==0 and min(u,dn,rn)>0,'strict positive input component')
    need(chi==W+a*(u+dn*Delta)+rn*H and chi*chi-Delta*psi*psi==1,'input norm')
    components.append({'a':a,'v':v,'u':u,'W':W,'delta':str(dn),'rho':str(rn)})
  records.append({'a':a,'Delta':Delta,'H':H,'order':O,'g':g,'period':period})
  indices+=period
 return {'periods':records,'binary_Pell_indices':indices,'residue_comparisons':comparisons,
         'positive_input_components':components,'scope':'Component evidence only, not complete compiler zeros.'}

def verify(root,author_root):
 for ext,pin in AUTHOR.items():need(sha((author_root/(STEM+ext)).read_bytes())==pin,'author pin '+ext)
 saved=read(author_root/(STEM+'.json'));packet=saved['packet']
 need(saved['source_sha256']==AUTHOR['.py'],'author self-source')
 for name,pin in saved['pins'].items():need(sha((root/name).read_bytes())==pin,'dependency '+name)
 need(len(saved['pins'])==12,'twelve dependency files')
 parent=read(root/'complete84_scaled_strong_output.json')['packet'];old=parent['source']
 need([r for r in old if r[0]=='gamma_sum']==[['gamma_sum','+','rho','sigma']],'old linear producer')
 need([r for r in old if 'gamma_sum' in r[2:]]==[['gam','*','gamma_sum','a4m5']],'sole consumer')
 rows=[([n,o,'sigma',b] if n=='gam' else [n,o,a,b]) for n,o,a,b in old if n!='gamma_sum']
 need(rows==packet['source'],'independent complete source reconstruction')
 for k in ['free','witnesses','fixed_numerals','ordinary_input','output','factors']:
  need(exact(packet[k],parent[k]),'retained interface '+k)
 known=set(packet['free']);deps={};M=0
 for n,o,a,b in rows:
  need(n not in known and o in ['+','-','*'],'fresh legal producer')
  need(all(type(t) is int or type(t) is str and t in known for t in [a,b]),'closure')
  known.add(n);deps[n]=[t for t in [a,b] if type(t) is str];M+=o=='*'
 live=set();pending=[packet['output']]
 while pending:
  n=pending.pop()
  if n not in live:live.add(n);pending.extend(deps.get(n,[]))
 need(live==known and len(rows)==83 and M==47 and len(packet['witnesses'])==18,'full paid interface')
 # Exact exceptional linear cut; all remaining definitions are byte-identical.
 need(add([0,1],add([0,0,1],[0,1],-1))==[0,0,1],'rho+(gamma-rho)=gamma')
 finalnames={'norm_pair','norm_triple','norm_four','norm_product','all_units','seven_units','polynomial'}
 tail=[r for r in rows if r[0] in finalnames]
 need(len(tail)==7 and sum(r[1]=='*' for r in tail)==6,'six products and subtraction')
 # Complete numeric pullbacks supplement the structural induction above.
 factor_names=packet['factors'];equalities=0
 for case in range(32):
  env={n:Fraction(((case+5)*(j+7)%29)-14,(j%3+1) if case>=16 else 1) for j,n in enumerate(packet['free'])}
  back=dict(env);back['sigma']-=env['rho']
  ce,pe=run(rows,env),run(old,back)
  for n,_,_,_ in rows:need(ce[n]==pe[n],'whole signed/rational pullback');equalities+=1
  # Rebuild finalizer directly, rather than following only its row names.
  product=1
  for f in factor_names:product*=ce[f]
  need(ce[packet['output']]==product-ce['A'],'full finalizer product')
 noninput=[f for f in factor_names if f!='norm_input'];fiber_equalities=0
 for case in range(12):
  env={n:(j+3)*(case+2)%17-8 for j,n in enumerate(packet['free'])};shift=case-5
  new=dict(env);new['x']+=shift;new['alpha']-=env['twice_cell_bits']*shift
  new['rho']+=case+1;new['delta']-=case+2
  a,b=run(rows,env),run(rows,new)
  for n in noninput+['marked_rhs','W','r_lhs']:
   need(a[n]==b[n],'same noninput fiber');fiber_equalities+=1
 diagnostics=[]
 for case,constants in enumerate([(15,7,10,5,6,19),(31,9,50,25,10,37)]):
  env={n:[(j+case)%4+1,(2*j+case)%7+1] for j,n in enumerate(packet['free'])}
  for n,v in zip(packet['fixed_numerals'],constants):env[n]=[v]
  back=dict(env);back['sigma']=add(env['sigma'],env['rho'],-1)
  ce,pe=polynomial_run(rows,env),polynomial_run(old,back)
  need(ce[packet['output']]==pe[parent['output']],'full exact integer coefficient pullback')
  d=[len(ce[f])-1 for f in factor_names]
  need(d==[22,18,32,60,7,2,46] and len(ce[packet['output']])-1==187,'degree attainment')
  diagnostics.append({'numerals':dict(zip(packet['fixed_numerals'],constants)),
                      'factor_degrees':d,'output_degree':187,
                      'full_coefficients_sha256':sha(json.dumps(ce[packet['output']]).encode()),
                      'valid_compiler_fixture':False})
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'author_pins':dict(AUTHOR),
         'dependency_pins':dict(saved['pins']),'packet':packet,
         'source_checks':{'gates':83,'M':47,'A':36,'witnesses':18,'free_ports':25,
                          'signed_cases':16,'rational_cases':16,'retained_row_equalities':equalities,
                          'fiber_cases':12,'fiber_equalities':fiber_equalities,'finalizer_rows':tail},
         'exact_integer_line_diagnostics':diagnostics,'input_fiber_checks':fiber_checks(),
         'uniform_degree_proof':'Invertible linear pullback of the pinned degree187 parent, with independently derived factor leaders in the note.',
         'language_status':'UNRESOLVED; full same-input inverse failure does not establish a false input.',
         'full_compiler_zeros_materialized':False,'predecessor_Python_executed':False}

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,required=True)
 p.add_argument('--author-root',type=Path)
 modes=p.add_mutually_exclusive_group(required=True);modes.add_argument('--expect',type=Path);modes.add_argument('--output',type=Path)
 a=p.parse_args();r=verify(a.root.resolve(),(a.author_root or a.root).resolve())
 if a.expect:need(exact(r,read(a.expect)),'type-exact expected receipt')
 else:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':'PASS','source_checks':r['source_checks'],'period_indices':r['input_fiber_checks']['binary_Pell_indices']},sort_keys=True))
if __name__=='__main__':main()
