#!/usr/bin/env python3
"""Actual auxiliary cut and an unbounded-exponent separated-model bound."""
import argparse,hashlib,json,random
from collections import Counter
from pathlib import Path
PINS={'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737','complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf','complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade'}
def ck(v,s):
 if not v:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def parse(path):
 def pairs(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate key');d[k]=v
  return d
 def bad(x):raise ValueError('nonfinite JSON')
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_constant=bad)
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def polyadd(a,b,sgn=1):
 d=dict(a)
 for k,v in b.items():
  d[k]=d.get(k,0)+sgn*v
  if not d[k]:del d[k]
 return d
def polymul(a,b):
 d={}
 for x,u in a.items():
  for y,v in b.items():
   z=tuple(a+b for a,b in zip(x,y));d[z]=d.get(z,0)+u*v
 return {k:v for k,v in d.items() if v}
def build(root):
 for name,pin in PINS.items():ck(sha((root/name).read_bytes())==pin,'pin '+name)
 old=parse(root/'complete84_scaled_strong_output.json')['packet'];rows=old['source'];by={r[0]:r for r in rows};free=old['free']
 expected={'c2':['*','R10a','R10a'],'Ac2':['*','A','c2'],'L16':['*','f','f'],'auxiliary_Tf':['*','auxiliary_quotient','f'],'auxiliary_Tf_minus_one':['-','auxiliary_Tf',1],'auxiliary_c_Tf':['*','R10a','auxiliary_Tf_minus_one'],'auxiliary_R_f2':['*','r_lhs','L16'],'aux_u_rhs':['-','auxiliary_c_Tf','auxiliary_R_f2'],'aux_coefficient_root':['*','i','Ac2'],'R16':['*','aux_coefficient_root','aux_coefficient_root'],'scaled_f_square':['*','A','L16'],'norm_strong':['-','scaled_f_square','R16']}
 for name,definition in expected.items():ck(by[name][1:]==definition,'literal producer '+name)
 cut=list(expected)[2:];ck(len(cut)==10,'ten paid producers')
 consumers={name:[] for name in cut}
 for nm,op,a,b in rows:
  for x in (a,b):
   if x in consumers:consumers[x].append(nm)
 external={k:[n for n in vs if n not in cut] for k,vs in consumers.items()}
 ck({k for k,v in external.items() if v}=={'aux_u_rhs','R16','norm_strong'},'exact three output interface')
 ct=Counter(by[n][1] for n in cut);ck(ct['*']==7 and ct['+']+ct['-']==3,'ten-gate cut')
 # Exponent proof certificates in order Delta,c,i,f,T,R.
 unit=(0,0,0,0,0,0);base=[tuple(int(i==j) for i in range(6)) for j in range(6)];leaves=[unit]+base+[(0,2,0,0,0,0),(1,2,0,0,0,0)]
 targets=[(0,1,0,1,1,0),(0,0,0,2,0,1),(2,4,2,0,0,0)];scaled_first=(1,0,0,2,0,0)
 divides=lambda a,b:all(x<=y for x,y in zip(a,b))
 for t in targets:
  ck(t not in leaves and all(tuple(x+y for x,y in zip(a,b))!=t for a in leaves for b in leaves),'at least two products '+str(t))
 gcds=[tuple(min(a,b) for a,b in zip(targets[i],targets[j])) for i in range(3) for j in range(i+1,3)]
 ck(all(g in leaves and sum(g)<=1 for g in gcds),'common divisors already supplied')
 ck(scaled_first not in leaves and all(not divides(scaled_first,t) for t in targets),'new mixed Delta/f cone')
 ck(all(t[0]==0 for t in targets[:2]+[base[1]]) and min(scaled_first[0],targets[2][0])>=1,'disjoint additive output supports')
 # An exact same-polynomial separated attaining source: cTf-c-Rf².
 changed=[]
 for r in rows:
  if r[0]=='auxiliary_Tf_minus_one':changed.append(['auxiliary_cTf_flat','*','R10a','auxiliary_Tf'])
  elif r[0]=='auxiliary_c_Tf':changed.append(['auxiliary_c_Tf','-','auxiliary_cTf_flat','R10a'])
  else:changed.append(r[:])
 newby={r[0]:r for r in changed};ck(consumers['auxiliary_Tf_minus_one']==['auxiliary_c_Tf'],'private changed intermediate')
 # Actual local coefficient identities, including the dependency Ac2=Delta*c².
 ps={name:{base[i]:1} for i,name in enumerate(['A','R10a','i','f','auxiliary_quotient','r_lhs'])};ps['c2']={(0,2,0,0,0,0):1};ps['Ac2']={(1,2,0,0,0,0):1}
 def local(rr):
  env=dict(ps)
  for nm,op,a,b in rr:
   if nm not in cut and nm!='auxiliary_cTf_flat':continue
   aa=env[a] if type(a)is str else {unit:a};bb=env[b] if type(b)is str else {unit:b}
   env[nm]=polymul(aa,bb) if op=='*' else polyadd(aa,bb,1 if op=='+' else -1)
  return env
 before=local(rows);after=local(changed)
 for nm in ['auxiliary_c_Tf','aux_u_rhs','R16','norm_strong']:ck(before[nm]==after[nm],'exact local coefficient identity')
 ck(before['aux_u_rhs']=={targets[0]:1,base[1]:-1,targets[1]:-1},'three quotient monomials')
 ck(before['R16']=={targets[2]:1} and before['norm_strong']=={scaled_first:1,targets[2]:-1},'joint norm monomials')
 # Every unchanged row agrees after the proved equal intermediate is cut.
 def interpret(rr,intern):
  env={x:('free',x) for x in free}
  for nm,op,a,b in rr:
   if nm=='auxiliary_c_Tf':env[nm]=('proved_cut',nm);continue
   aa=env[a] if type(a)is str else ('constant',a);bb=env[b] if type(b)is str else ('constant',b);key=(op,aa,bb)
   if key not in intern:intern[key]=len(intern)
   env[nm]=intern[key]
  return env
 inter={};eo=interpret(rows,inter);en=interpret(changed,inter)
 for name in by:
  if name!='auxiliary_Tf_minus_one':ck(eo[name]==en[name],'retained whole graph '+name)
 known=set(free);lookup={};count=Counter()
 for nm,op,a,b in changed:
  ck(nm not in known and all(type(x)is int or x in known for x in (a,b)),'closed alternate');known.add(nm);lookup[nm]=(a,b);count[op]+=1
 live=set();todo=[old['output']]
 while todo:
  x=todo.pop()
  if type(x)is str and x not in live:live.add(x);todo.extend(lookup.get(x,()))
 ck(live==known and len(changed)==84 and count['*']==47,'84 live whole source')
 # Supplementary full signed evaluations, not native zero tuples.
 rng=random.Random(841003);cases=[]
 def ev(rr,values):
  d=dict(values)
  for n,op,a,b in rr:
   aa=d[a] if type(a)is str else a;bb=d[b] if type(b)is str else b;d[n]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
  return d[old['output']]
 for j in range(16):
  values={x:rng.randrange(-4,5) for x in free};a=ev(rows,values);b=ev(changed,values);ck(a==b,'whole signed evaluation');cases.append({'values':values,'output_sha256':sha(str(a).encode())})
 packet=dict(old,source=changed,full_polynomial_identity='F_flat=F84 on all supplied values',ledger={'M':47,'A':37,'total':84,'all_rows_live':True,'all_ports_live':True})
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'parent_pins':PINS,'parent_packet':old,'separated_attaining_packet':packet,'cut_rows':cut,'cut_consumers':consumers,'cut_external_consumers':external,'cut_ledger':{'M':7,'A':3,'total':10},'monomial_certificate':{'variable_order':['Delta','c','i','f','T','R'],'paid_exponents':[list(v) for v in leaves],'unchanged_required_monomials':[list(v) for v in targets],'pairwise_gcds':[list(v) for v in gcds],'scaled_strong_first_base':list(scaled_first),'all_nonnegative_multiplier_exponents_allowed':True,'proof_uses_variable_support_and_divisor_ancestry':True},'coefficient_identities':{name:[[list(k),v] for k,v in sorted(before[name].items())] for name in ['aux_u_rhs','R16','norm_strong']},'full_signed_checks':cases,'scope':'At least7 nonconstant multiplications and3 additions for separated monomial production/additive outputs; no lower bound for general mixed arithmetic or coordinate charts.'}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--expect',type=Path);g.add_argument('--output',type=Path);args=ap.parse_args();d=build(args.root)
 if args.output:args.output.write_text(json.dumps(d,sort_keys=True,indent=2)+'\n')
 else:ck(exact(d,parse(args.expect)),'exact receipt replay')
 print(json.dumps({'cut':d['cut_ledger'],'full':d['separated_attaining_packet']['ledger']}))
if __name__=='__main__':main()
