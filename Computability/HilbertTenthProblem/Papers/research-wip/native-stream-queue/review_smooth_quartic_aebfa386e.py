#!/usr/bin/env python3
"""Portable pinned review of the smooth-quartic incoming archive."""
import argparse
from collections import Counter
from contextlib import contextmanager
from fractions import Fraction
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

ARCHIVE_SHA='52cea74ad86e678a10963c2d8db4cb5874fc8aece9691c2dcfea45bfb00f9551'
MEMBERS={'smooth_diophantine/Makefile': '3661f3471f353e8f0099d5ce41f70cf609dc01dfab5192ce8c9210637ee8bf95', 'smooth_diophantine/README.md': 'ba1054f176e1bbca85fe1f753f9bc49603ad62413332cf0a9aeb00d41b99c847', 'smooth_diophantine/RESEARCH_STATUS.md': '07d0d313b0a646ba7e7b092b0d8d463ff7029160924dd2b1eb76f43f0b0c7c64', 'smooth_diophantine/SHA256SUMS': '82d9e8c361d23650e7796222ac078373afce93034372675e4ea5811fbbe25d49', 'smooth_diophantine/SOURCE_AUDIT.md': '01144a63fe1bf70653ba81583943f83d755b57273efc687c25c84debcfa8d98a', 'smooth_diophantine/article.pdf': '5499f4741a17bd913fda1325e04f90b3db3a7a6827b4c4547d81304cfbb8b4dc', 'smooth_diophantine/article.tex': '2ad776fa10af8d8bd446e77273888b9806564cf1e32e6c31475f526de164be89', 'smooth_diophantine/code/counter_frontend.py': '6e230beb1bec97ab96de7d25be7d2184b74a51b5e170130f7a97f13729d79b03', 'smooth_diophantine/code/smooth_compiler.py': '5bec75dfb639762b070feed1612e5a784a63c691db1cb884768271d5e7b29ff8', 'smooth_diophantine/code/verify.py': '97f294e54be9ba9720ea303e196b8ef2cb18ec8985685415512aa2daac9fcb16', 'smooth_diophantine/examples/countdown_T3.json': '9f3f47db6b9827fa8f5c971a61f5c308f1c0b14af07efefb5e7ac5190dd1fe25', 'smooth_diophantine/examples/inconsistent.json': '5b47d3a079279a2ee09667acda3ce09ba636425c252c4dc0b7d60bcc94dad54b', 'smooth_diophantine/requirements.txt': '25f9f1fb1988b230147a1d3092d34e09c069eb7a6c6d6df46b3973b9f2d36efc', 'smooth_diophantine/verification/document_qa.json': '957127c62c5499a69bff1f69bda83274cb3c2a0e6c790cd8043d7cb6168ffd91', 'smooth_diophantine/verification/results.json': '86422a9d976eb6529e8693591140130f898b03085cde40d5a075df2c05d5708a', 'smooth_diophantine/verification/run.log': 'e08dba7209b74bfdc538525354850d9ab982d97e577a2d10c93939253da5728d'}

def need(ok,message):
 if not ok:raise ValueError(message)
def exact(a,b):
 if type(a) is not type(b):return False
 if type(a) is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a) in (list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def sparse(export,values):
 need(len(values)==len(export['variables']),'Independent evaluator dimension')
 total=0
 for term in export['terms']:
  value=term['coefficient']
  for x,e in zip(values,term['exponents']):value*=x**e
  total+=value
 return total

@contextmanager
def modules(root):
 before=dict(sys.modules);oldpath=list(sys.path);code=root/'code';names=('smooth_compiler','counter_frontend')
 try:
  for name in names:sys.modules.pop(name,None)
  sys.path.insert(0,str(code));out=[]
  for name in names:
   spec=importlib.util.spec_from_file_location(name,code/(name+'.py'));m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);out.append(m)
  yield out
 finally:
  sys.path[:]=oldpath
  for name in names:
   sys.modules.pop(name,None)
   if name in before:sys.modules[name]=before[name]

def original_run(root,original):
 run=subprocess.run([sys.executable,str(root/'code/verify.py')],cwd=root,capture_output=True,text=True,timeout=300)
 need(run.returncode==0,'Original author verification failed: '+run.stderr[-2000:])
 result=json.loads((root/'verification/results.json').read_text());saved=json.loads(original['smooth_diophantine/verification/results.json'])
 runtime={k:result.pop(k) for k in ('python','sympy')};expected_runtime={k:saved.pop(k) for k in ('python','sympy')}
 need(exact(result,saved),'Author result differs outside explicit runtime version fields')
 exports=[]
 for rel in ('examples/countdown_T3.json','examples/inconsistent.json'):
  data=(root/rel).read_bytes();need(data==original['smooth_diophantine/'+rel],'Author export changed: '+rel)
  exports.append(dict(path=rel,sha256=hashlib.sha256(data).hexdigest()))
 return dict(status='PASS',total_checks=result['total_checks'],normalized_fields=['python','sympy'],exports_byte_identical=exports)

def focused(root):
 import sympy as sp
 counts=Counter();fixtures=[]
 with modules(root) as (m,c):
  x,y=sp.symbols('x y');sources=[((x,y),(x*y-2,x+y-3)),((x,y),(x*x+y*y-1,)),((),(sp.Integer(1),)),((),())]
  for vv,rr in sources:
   cert=m.compile_smooth(m.QuadraticSystem(vv,rr));exp=cert.export();n=len(vv)
   need(len(cert.variables)==n+5 and exp['degree']==4,'Wrong complete interface/degree');counts['interfaces']+=1
   A,B=cert.jacobian_coefficients()
   need(sp.expand(A*cert.F+sum(b*sp.diff(cert.F,v) for b,v in zip(B,cert.variables)))==1,'Actual integral Jacobian certificate');counts['symbolic_jacobian_identities']+=1
   char2=sp.Poly(sp.diff(cert.F,cert.z[0])-1,*cert.variables)
   need(all(int(a)%2==0 for a in char2.coeffs()),'Characteristic-two unit derivative');counts['characteristic_two_identities']+=1
   point,meta=m.dyadic_point(cert);rational=[Fraction(str(v)) for v in point]
   need(sparse(exp,rational)==0 and all(v>=0 and v.denominator&(v.denominator-1)==0 for v in rational),'Dyadic point failed independent sparse evaluation');counts['dyadic_points']+=1
   a0,b0,c0=[sp.Integer(0)]*3
   for coordinates in product(range(-2,3),repeat=n):
    for t,u in product(range(-1,2),repeat=2):
     for z in product(range(-1,2),repeat=3):
      values=coordinates+(t,u)+z;actual=sparse(exp,values)==0
      expected=t==u and t in (-1,1) and z==(0,0,0) and all(f.subs(dict(zip(vv,(t*a for a in coordinates))))==0 for f in rr)
      need(actual==expected,'Integer fibre census mismatch');counts['integer_fibre_tuples']+=1
      if all(a>=0 for a in values):
       expected_nat=t==u==1 and z==(0,0,0) and all(f.subs(dict(zip(vv,coordinates)))==0 for f in rr)
       need(actual==expected_nat,'Natural fibre census mismatch');counts['natural_fibre_tuples']+=1
   for const in (0,1,3,5,13,100):
    residues=m.two_adic_residues(const,12);last=0
    for k,r in enumerate(residues,1):
     need(r['modulus']==2**k and (const+2*r['z']**2-r['z'])%2**k==0 and (k==1 or r['z']%2**(k-1)==last),'Incompatible exact 2-adic root');last=r['z'];counts['two_adic_residues']+=1
   fixtures.append(dict(source_variables=n,source_residuals=list(map(str,rr)),degree=exp['degree'],monomials=exp['monomial_count'],dyadic=list(map(str,point))))
  programs=[]
  for target in range(2):programs.append(c.Program(1,(c.Instruction('inc',0,target),c.Instruction('halt'))))
  for positive,zero in product(range(2),repeat=2):programs.append(c.Program(1,(c.Instruction('dec',0,positive,zero),c.Instruction('halt'))))
  for program in programs:
   for initial,T in product(range(4),range(5)):
    state,register=0,initial;hist=[(state,(register,))]
    for _ in range(T):
     ins=program.instructions[state]
     if ins.op=='inc':register+=1;state=ins.next
     elif ins.op=='dec':
      if register:register-=1;state=ins.next
      else:state=ins.zero
     hist.append((state,(register,)))
    compiled=c.compile_counter(program,(initial,),T)
    need(compiled.history==tuple(hist),'Independent operational interpreter differs')
    value=compiled.system.evaluate(compiled.point)
    need(all(v==0 for v in value[:-1]) and (value[-1]==0)==(state==1),'Bounded row/endpoint semantics differ')
    E=len(program.edges);p=sum(e.guard=='positive' for e in program.edges);g=sum(e.guard!='any' for e in program.edges)
    need(len(compiled.system.variables)==3*(T+1)+(E+p)*T and len(compiled.system.residuals)==4+T*(6+g),'Bounded paid witness/residual formula')
    counts['independent_counter_runs']+=1
  bad=[lambda:m.QuadraticSystem((x,),(x**3,)),lambda:m.QuadraticSystem((x,),(sp.Rational(1,2)*x,)),lambda:m.QuadraticSystem((x,),(x+y,)),lambda:m.QuadraticSystem((x,x),(x,)),lambda:m.QuadraticSystem((x,),(1.0*x,)),lambda:c.compile_counter(c.countdown(),(-1,),2),lambda:c.compile_counter(c.countdown(),(1,),True),lambda:c.compile_counter(c.countdown(),(True,),2)]
  for fn in bad:
   try:fn()
   except (TypeError,ValueError):counts['malformed_inputs_rejected']+=1
   else:raise ValueError('Bad interface accepted')
  # Independent finite replays of the proof's primitive ternary obstructions.
  for a,b,c0 in product(range(16),repeat=3):need((a*a+3*b*b+2*c0*c0)%16!=10,'Ternary obstruction mod16');counts['ternary_mod16_cases']+=1
  for a,b,c0 in product(range(8),repeat=3):
   if any(v%2 for v in (a,b,c0)):need((a*a+3*b*b+2*c0*c0)%8!=0,'Primitive ternary obstruction mod8');counts['primitive_mod8_cases']+=1
 return dict(counts=dict(counts),fixtures=fixtures)

def verify(archive):
 archive=Path(archive);need(hashlib.sha256(archive.read_bytes()).hexdigest()==ARCHIVE_SHA,'Archive pin mismatch')
 with tempfile.TemporaryDirectory(prefix='smooth-quartic-review-') as folder:
  base=Path(folder);original={}
  with zipfile.ZipFile(archive) as z:
   entries=z.infolist();need(len(entries)==len({e.filename for e in entries}),'Duplicate archive entries')
   for entry in entries:
    p=Path(entry.filename);need(not p.is_absolute() and '..' not in p.parts and '\\' not in entry.filename and (entry.external_attr>>16)&0o170000!=0o120000,'Unsafe archive entry')
    if entry.is_dir():continue
    data=z.read(entry);need(MEMBERS.get(entry.filename)==hashlib.sha256(data).hexdigest(),'Archive member mismatch');original[entry.filename]=data;target=base/p;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
  need(set(original)==set(MEMBERS),'Incomplete archive inventory')
  root=base/'smooth_diophantine';author=original_run(root,original);checks=focused(root)
 return dict(status='PASS_SMOOTH_QUARTIC_REVIEW',archive_sha256=ARCHIVE_SHA,member_sha256=MEMBERS,author_replay=author,independent=checks,scope='Complete article/source proofread, original 21128-check replay and byte-identical exports; independent bounded fixtures and symbolic identities, no universal source operation improvement or novelty priority certification.')

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--archive',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();out=verify(a.archive)
 if a.output:a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'Saved review differs')
 print(json.dumps(out,indent=2,sort_keys=True))
