#!/usr/bin/env python3
"""Producer-independent exact audit of the 23-integer degree-12 system.

Uses only the Python standard library. It parses inert upstream residuals
and independently reconstructs every surviving arithmetic row in compact
form. It does not import the producer, its polynomial class, or its circuit.
"""
import ast, collections, gzip, hashlib, json, sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else HERE
SYMS=['J','F','alpha','f','h','r','v_scale','tau','eta','y','gamma','o','j','E','c','a','I','u','Z','pair_root','pair_pos1','pair_pos2','pair_pos3','beta','K0','MC','MF','cone_A','cone_B']
NV=23; NS=len(SYMS); ZERO=(0,)*NS

def require(x,msg):
 if not x:raise RuntimeError(msg)

def add(p,q):
 out=dict(p)
 for k,v in q.items():
  out[k]=out.get(k,0)+v
  if not out[k]:del out[k]
 return out

def neg(p):return {k:-v for k,v in p.items()}
def mul(p,q):
 out=collections.defaultdict(int)
 for a,x in p.items():
  for b,y in q.items():out[tuple(i+j for i,j in zip(a,b))]+=x*y
 return {k:v for k,v in out.items() if v}
def power(p,n):
 require(type(n)==int and n>=0,'fixed nonnegative exponent')
 ans={ZERO:1}
 while n:
  if n&1:ans=mul(ans,p)
  n//=2
  if n:p=mul(p,p)
 return ans

VARS={s:{tuple(int(i==j) for i in range(NS)):1} for j,s in enumerate(SYMS)}

def parse(s,env=None):
 env=VARS if env is None else env
 def walk(n):
  if isinstance(n,ast.Constant):
   require(type(n.value)==int,'integer constant')
   return {ZERO:n.value} if n.value else {}
  if isinstance(n,ast.Name):return env[n.id]
  if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return neg(walk(n.operand))
  if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.UAdd):return walk(n.operand)
  if isinstance(n,ast.BinOp):
   if isinstance(n.op,ast.Add):return add(walk(n.left),walk(n.right))
   if isinstance(n.op,ast.Sub):return add(walk(n.left),neg(walk(n.right)))
   if isinstance(n.op,ast.Mult):return mul(walk(n.left),walk(n.right))
   if isinstance(n.op,ast.Pow):
    require(isinstance(n.right,ast.Constant),'literal exponent')
    return power(walk(n.left),n.right.value)
  raise ValueError(ast.dump(n))
 return walk(ast.parse(s,mode='eval').body)

def normed(p):
 if not p:return ()
 sign=1 if next(v for k,v in sorted(p.items()))>0 else -1
 return tuple(sorted((k,sign*v) for k,v in p.items()))

def degree(p):return max((sum(k[:NV]) for k in p),default=-1)

def add_aliases(env,seq):
 for name,s in seq:env[name]=parse(s,env)
 return env

def main():
 env=add_aliases(dict(VARS),[
  ('q','beta*J+1'),('C','q-F-alpha'),('s','2*v_scale+1'),
  ('X','4*q*u**2'),('H','4*a+3'),('Delta','a*a+4*a+3'),
  ('V','f*o-c'),('k','1-V+j*c+h*E'),('zeta','k-eta'),
  ('D','X+a*c+gamma*H'),
  ('R','((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J'),
  ('Ug','cone_A*F'),('Vg','cone_B*C'),
  ('G','Ug*Vg-(q-Ug-Vg)**2'),('Bsign','eta*zeta'),
  ('GP','G*Bsign-(pair_root**2-G-Bsign+1)**2-1-pair_pos1**2-pair_pos2**2-pair_pos3*(pair_pos3+1)')])
 formulas=[
  'a-E-s*q**3',
  'E-X*(a-E)',
  'c-eta-k*(a-E)',
  'tau**2+(2*tau-k)*E*(c-eta)-1',
  'D**2-Delta*c**2-1',
  'j*c-V-R',
  '(K0*q+X)*C-q*F-Z*(q-1)',
  'I-(2*r+1)*c**2',
  'I**2-Delta*(f**2-1)',
  'y**2-I**2*(y**2-V**2)-1',
  'GP']
 ours=[parse(s,env) for s in formulas]
 # Restore all eliminated arithmetic coordinates of signed40 exactly.
 restored=dict(env)
 add_aliases(restored,[('L','q*q-1'),('N','q**3'),('P','k+E*(c-eta)'),('C2','c*c'),('F2','f*f'),('g','y*y-V*V'),('Baux','I*I')])
 restored['tau']=parse('tau+E*(c-eta)',env)
 old=json.loads((ROOT/'upstream/signed40_sextic.json').read_text())
 old_arith=old['residuals'][:-3]
 image=[parse(s,restored) for s in old_arith]
 live_image=[p for p in image if p]
 require(len(live_image)==10,'exactly 10 nonzero arithmetic residual images')
 require(collections.Counter(map(normed,live_image))==collections.Counter(map(normed,ours[:-1])), 'all arithmetic source images match compact equations up to sign')
 require(sum(not p for p in image)==12,'all 12 eliminated defining equations are literal zero')
 candidate=json.loads((ROOT/'degree12_23.json').read_text())
 require(len(candidate['variables'])==23 and len(set(candidate['variables']))==23,'exactly 23 distinct integer unknowns')
 require(set(candidate['variables'])==set(SYMS[:NV]),'exact variable set')
 require(candidate['domain']=='unrestricted integers','unrestricted integer domain')
 producer=[parse(s) for s in candidate['residuals']]
 require(collections.Counter(map(normed,producer))==collections.Counter(map(normed,ours)), 'all 11 final residuals match independently derived formulas')
 deg=[degree(p) for p in ours]
 require(max(deg)==6 and len(deg)==11,'11 residuals degree at most six')
 require({SYMS[i] for p in ours for k in p for i in range(NV) if k[i]}==set(SYMS[:NV]),'all listed variables live')
 full={}
 for p in ours:full=add(full,mul(p,p))
 require(degree(full)==12,'exact final symbolic degree12')
 target=[0]*NS
 for name,exponent in [('eta',4),('j',4),('c',4)]:target[SYMS.index(name)]=exponent
 require(full.get(tuple(target))==1,'exact coefficient +1 at eta^4*j^4*c^4')
 require(not any(k[:NV]==tuple(target[:NV]) and any(k[NV:]) for k in full),'no port-dependent term at degree witness')
 # Check exact fixed powers and all bundled unsigned coefficient bytes.
 binding=json.loads((ROOT/'coefficients/BINDING.json').read_text())
 vals={}
 for name,rec in binding['payloads'].items():
  raw=gzip.decompress((ROOT/'coefficients'/rec['file']).read_bytes())
  require(hashlib.sha256(raw).hexdigest()==rec['raw_sha256'],'coefficient bytes '+name)
  vals[name]=int.from_bytes(raw,'little')
 require(vals['beta']==2**1064921-1,'native beta')
 require(vals['cone_A']==2**1113,'determinant scale A')
 require(vals['cone_B']==2**666104,'determinant scale B')
 require(0<vals['MC']<vals['beta']<vals['MF']<2*vals['beta'],'authentic mask interval')
 result={'status':'PASS','variables':23,'residuals':11,'exact_degree':12,'compact_residual_degrees':deg,'source_arithmetic_rows':len(old_arith),'eliminated_rows_identically_zero':12,'surviving_rows_exact':10,'full_expansion_terms':len(full),'degree_certificate':{'monomial':{'eta':4,'j':4,'c':4},'coefficient':1},'checks':['no producer imports','complete exact source restoration','all final residuals exactly matched','full symbolic SOS expansion','literal fixed-power checks','all fixed payload hashes'],'boundary':'Universal sign/cone/Pell arguments are mathematical proof obligations, not established by finite symbolic checks.'}
 (HERE/'INTEGER23_INDEPENDENT_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))

if __name__=='__main__':main()
