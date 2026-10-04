"""Independent signed-T source/factor/census and recurrence checks; no old code."""
import argparse,hashlib,json
from pathlib import Path
AUTHOR={
'complete84_signed_quotient_absorption.py':'cc5ed27ffcffefbd76b85ea36efa05637e06a0eb7fa221c6d9e31af9ea4f9d5f',
'complete84_signed_quotient_absorption.json':'c9522c55adb3e602c2d355cb98d4e313c5e258a66e93bf0bbca52d56fddd9a00',
'complete84_signed_quotient_absorption.md':'79800010986c07674fb681a93e02f624ee7bc6e5d39b99a1e77daf5021fa77c9'}
SOURCE='complete84_scaled_strong_output.json'
SOURCE_SHA='8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf'
def ck(x,s):
 if not x:raise ValueError(s)
def sha(x):return hashlib.sha256(x).hexdigest()
def enc(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def pairs(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate key');d[k]=v
  return d
 def bad(x):raise ValueError('noninteger '+x)
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def const(x):return {():x} if x else {}
def var(x):return {(x,):1}
def add(a,b,s=1):
 d=dict(a)
 for m,v in b.items():d[m]=d.get(m,0)+s*v
 return {m:v for m,v in d.items() if v}
def mul(a,b):
 d={}
 for m,v in a.items():
  for n,w in b.items():
   k=tuple(sorted(m+n));d[k]=d.get(k,0)+v*w
 return {m:v for m,v in d.items() if v}
def power(p,n):
 r=const(1)
 for _ in range(n):r=mul(r,p)
 return r
def plist(p):return [[list(m),v] for m,v in sorted(p.items())]
def build(root,author):
 for n,h in AUTHOR.items():ck(sha((author/n).read_bytes())==h,'author pin '+n)
 rec=read(author/'complete84_signed_quotient_absorption.json')
 ck(rec['source_sha256']==AUTHOR['complete84_signed_quotient_absorption.py'],'helper binding')
 for n,h in rec['pins'].items():ck(sha((root/n).read_bytes())==h,'inert pin '+n)
 ck(len(rec['pins'])==22 and rec['pins'][SOURCE]==SOURCE_SHA,'exact dependency scope')
 p=read(root/SOURCE)['packet'];rows=p['source'];free=p['free'];d={};dep={n:{n} for n in free}
 for row in rows:
  ck(type(row)is list and len(row)==4,'row shape');n,o,a,b=row
  ck(type(n)is str and n not in dep and o in ['+','-','*'],'source SSA/operator')
  ck(all(type(v)is int or type(v)is str and v in dep for v in [a,b]),'source topology')
  d[n]=row;dep[n]=set().union(*[set() if type(v)is int else dep[v] for v in [a,b]])
 ck(rows==rec['authenticated_parent_source'] and free==rec['authenticated_free_ports'],'entire actual84 source')
 ck(len(rows)==84 and sum(r[1]=='*' for r in rows)==47 and len(free)==25,'literal ledger')
 old=[n for n in d if not dep[n]&{'i','f','auxiliary_quotient','y_aux'}]
 new=[n for n in d if not dep[n]&{'auxiliary_quotient','y_aux'}]
 oldfree=[n for n in free if n not in ['i','f','auxiliary_quotient','y_aux']]
 newfree=[n for n in free if n not in ['auxiliary_quotient','y_aux']]
 ck((len(old),len(new),len(oldfree),len(newfree))==(64,70,21,23),'independent dependency census')
 for k,v in [('old_computed',old),('new_computed',new),('old_free',oldfree),('new_free',newfree)]:ck(rec['census'][k]==v,'census '+k)
 ba=rec['bound_audit'];boundrows=ba['old_computed']+ba['added_computed']
 ck([r['name'] for r in ba['old_computed']]==old and {r['name'] for r in boundrows}==set(new),'all70 bound records')
 ck(all(r['literal_producer']==d[r['name']] for r in boundrows),'every producer bound binding')
 ck({r['name'] for r in ba['old_supplied']+ba['added_supplied']}==set(newfree),'all23 supplied bounds')
 ck(set(new)-set(old)=={'L16','auxiliary_R_f2','aux_coefficient_root','R16','scaled_f_square','norm_strong'},'six additional producers')
 ck([r for r in rows if 'auxiliary_quotient' in r[2:]]==[['auxiliary_Tf','*','auxiliary_quotient','f']],'sole T consumer')
 # Eight actual exterior cuts suffice: five factors, Delta,c,R. Every other
 # actual ancestor is expanded, including the paired/triple products and c².
 factors=['norm_first','norm_main','norm_input','norm_index','norm_transport']
 cuts=set(factors+['A','R10a','r_lhs']);ck(cuts<=set(old),'only legitimate exterior cuts')
 memo={n:var(n) for n in cuts};visited=set()
 def at(n):
  if type(n)is int:return const(n)
  if n not in memo:
   if n in free:memo[n]=var(n)
   else:
    visited.add(n);_,o,a,b=d[n];a,b=at(a),at(b);memo[n]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
  return memo[n]
 F=at(p['output']);Delta,c,R,i,f,T,y=[var(n) for n in ['A','R10a','r_lhs','i','f','auxiliary_quotient','y_aux']]
 S=mul(mul(Delta,i),power(c,2));V=add(mul(c,add(mul(T,f),const(1),-1)),mul(R,power(f,2)),-1)
 Ns=add(power(f,2),mul(mul(Delta,power(i,2)),power(c,4)),-1)
 Na=add(mul(power(S,2),add(power(V,2),power(y,2),-1)),power(y,2));P5=const(1)
 for n in factors:P5=mul(P5,var(n))
 norm=add(mul(mul(P5,Na),Ns),const(1),-1)
 ck(F==mul(Delta,norm) and len(F)==17,'full source normalization')
 ck(at('norm_strong')==mul(Delta,Ns) and at('norm_aux')==Na and at('aux_u_rhs')==V,'actual factors')
 o=add(mul(c,T),mul(R,f),-1)
 j=add(add(mul(T,f),mul(mul(mul(R,Delta),power(i,2)),power(c,3)),-1),const(1),-1)
 ck(add(V,c)==mul(f,o),'f congruence')
 ck(add(add(V,R),mul(c,j),-1)==mul(R,add(const(1),Ns,-1)),'c congruence with exact strong correction')
 # Formal identities, independently in the polynomial ring Z[A0].
 A=var('A0');z=add(const(1),power(A,2),-1)
 chi=[const(1),A];psi=[{},const(1)]
 for n in range(2,28):
  chi.append(add(mul(mul(const(2),A),chi[-1]),chi[-2],-1))
  psi.append(add(mul(mul(const(2),A),psi[-1]),psi[-2],-1))
 cs=rec['finite_evidence']['C_coefficients'];ck(len(cs)==14,'14 odd polynomials');formal=[]
 for v,coeff in enumerate(cs):
  def compose(base):
   out={}
   for k in reversed(coeff):out=add(mul(out,base),const(k))
   return out
  n=2*v+1
  ck(compose(z)==mul(const((-1)**v),psi[n]),'formal negative-Delta identity')
  ck(mul(A,compose(power(A,2)))==chi[n],'formal chi quotient identity')
  ck(coeff[0]==(-1)**v*n,'zero evaluation')
  formal.append(dict(index=n,psi_terms=plist(psi[n]),chi_terms=plist(chi[n])))
 # Separate recurrence evaluation of every saved signed step-down case.
 successful=[]
 for a in range(2,9):
  xs=[1,a]
  for n in range(2,137):xs.append(2*a*xs[-1]-xs[-2])
  for m in range(3,18):
   f0=xs[m]
   for p0 in range(1,(m+1)//2):
    if 2*p0>=m:continue
    for ell in range(4*m):
     if (xs[2*ell]-xs[2*p0])%f0==0:
      ck(ell%m in [p0%m,(-p0)%m],'independent signed step-down residue')
      successful.append([a,m,p0,ell])
 ck(successful==rec['finite_evidence']['signed_step_down_checks'] and len(successful)==1792,'all saved step-down cases')
 for t,L,bound in rec['finite_evidence']['cutoff_checks']:
  ck(bound==3*t+(L-1).bit_length()+3,'exact integer cutoff')
  for f0 in [2,3,5,11]:ck(f0**(bound-3)>=L*f0**(3*t),'strict-growth threshold')
 return dict(status='PASS_INDEPENDENT_SIGNED_QUOTIENT_ABSORPTION',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR,inert_pins=rec['pins'],
  full_source_sha256=sha(enc(rows)),literal_rows=84,computed_exterior=new,supplied_exterior=newfree,
  old_computed_exterior=old,old_supplied_exterior=oldfree,eight_actual_cuts=sorted(cuts),expanded_ancestors=sorted(visited),
  source_normalization_coefficients=plist(F),source_normalization_terms=len(F),formal_odd_identities=formal,signed_step_down_cases=len(successful),
  cutoff_cases=len(rec['finite_evidence']['cutoff_checks']),scope=dict(only_T_signed=True,full_signed_compiler_transfer=False,
   R_mod_four_not_assumed=True,canonical_input_index_not_assumed=True,predecessor_execution=False,new_full_zero_fixture=False))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=ap.parse_args();r=build(a.root,a.author_root or a.root)
 if a.output:
  with a.output.open('x') as f:f.write(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(enc(r)==enc(read(a.expect)),'exact independent receipt')
 print(r['status'],'84 rows,93 ports,formal odd identities and signed rank components')
if __name__=='__main__':main()
