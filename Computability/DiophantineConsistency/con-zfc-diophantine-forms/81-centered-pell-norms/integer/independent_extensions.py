#!/usr/bin/env python3
"""Producer-independent exact audits of the 24-integer degree-10 and 22-integer degree-14 systems.

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


def symbols(names):
 global SYMS,NV,NS,ZERO,VARS
 SYMS=names+['beta','K0','MC','MF','cone_A','cone_B'];NV=len(names);NS=len(SYMS);ZERO=(0,)*NS
 VARS={s:{tuple(int(i==j) for i in range(NS)):1} for j,s in enumerate(SYMS)}


def environment(keep_zeta):
 env=add_aliases(dict(VARS),[
  ('q','beta*J+1'),('C','q-F-alpha'),('s','2*v_scale+1'),
  ('X','4*q*u**2'),('H','4*a+3'),('Delta','a*a+4*a+3'),
  ('V','f*o-c'),('Y','a-E'),('b','a*c+gamma*H'),('D','X+b'),
  ('R','((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J'),
  ('Ug','cone_A*F'),('Vg','cone_B*C'),('G','Ug*Vg-(q-Ug-Vg)**2')])
 if keep_zeta:env['k']=parse('eta+zeta',env)
 else:add_aliases(env,[('k','1-V+j*c+h*E'),('zeta','k-eta')])
 add_aliases(env,[('Bsign','eta*zeta'),('GP','G*Bsign-(pair_root**2-G-Bsign+1)**2-1-pair_pos1**2-pair_pos2**2-pair_pos3*(pair_pos3+1)')])
 if 'I' not in VARS:env['I']=parse('(2*r+1)*c*c',env)
 return env


def source_images(env):
 restored=dict(env)
 restored['y']=parse('f*o+y',env)
 add_aliases(restored,[('L','q*q-1'),('N','q**3'),('P','k+E*(c-eta)'),('C2','c*c'),('F2','f*f'),('g','y*y-V*V'),('Baux','I*I')])
 restored['tau']=parse('tau+E*(c-eta)',env)
 old=json.loads((ROOT/'upstream/signed40_sextic.json').read_text())
 require(len(old['residuals'])==25,'exact signed40 source size')
 return [parse(s,restored) for s in old['residuals'][:-3]]


def replace_unique(rows, old, new):
 matches=[i for i,p in enumerate(rows) if p==old or p==neg(old)]
 require(len(matches)==1,'unique row to transform')
 out=list(rows);out[matches[0]]=new
 return out


def check_packet(name, expected, expected_degree, witness, leading):
 packet=json.loads((ROOT/(name+'.json')).read_text())
 require(packet['domain']=='unrestricted integers','unrestricted integer domain')
 require(len(packet['variables'])==NV and len(set(packet['variables']))==NV,'distinct exact variable count')
 require(set(packet['variables'])==set(SYMS[:NV]),'complete variable list')
 actual=[parse(s) for s in packet['residuals']]
 require(collections.Counter(map(normed,actual))==collections.Counter(map(normed,expected)),'complete residual formula match')
 require({SYMS[i] for p in expected for k in p for i in range(NV) if k[i]}==set(SYMS[:NV]),'all unknowns live')
 full={}
 for p in expected:full=add(full,mul(p,p))
 require(degree(full)==expected_degree,'exact polynomial degree')
 head={k:v for k,v in full.items() if sum(k[:NV])==expected_degree}
 require(head==parse(leading),'complete leading homogeneous form')
 target=[0]*NS
 for v,n in witness['powers'].items():target[SYMS.index(v)]=n
 require(full.get(tuple(target))==witness['coefficient'],'exact coefficient witness')
 require(not any(k[:NV]==tuple(target[:NV]) and any(k[NV:]) for k in full),'no fixed-port-dependent contribution to witness')
 circuit=json.loads((ROOT/(name+'_circuit.json')).read_text())
 values=[]
 for index,node in enumerate(circuit['nodes']):
  op=node['op']
  if op=='symbol':values.append(VARS[node['name']])
  elif op=='const':values.append({ZERO:node['value']} if node['value'] else {})
  else:
   require(op in ['add','sub','mul'] and len(node['args'])==2,'ordinary binary circuit gate')
   left,right=node['args'];require(0<=left<index and 0<=right<index,'topological circuit')
   values.append(add(values[left],values[right]) if op=='add' else add(values[left],neg(values[right])) if op=='sub' else mul(values[left],values[right]))
 require(values[circuit['output']]==full,'complete circuit equals the independently expanded SOS')
 require(collections.Counter(map(normed,[values[i] for i in circuit['residual_outputs']]))==collections.Counter(map(normed,expected)),'all circuit residual outputs correct')
 live=set();todo=[circuit['output']]
 while todo:
  index=todo.pop()
  if index in live:continue
  live.add(index);todo.extend(circuit['nodes'][index].get('args',[]))
 counts=dict(collections.Counter(circuit['nodes'][i]['op'] for i in live if circuit['nodes'][i]['op'] in ['add','sub','mul']))
 require(counts==circuit['binary_operation_counts'] and sum(counts.values())==circuit['total_binary_operations'],'exact live arithmetic operation counts')
 return {'name':name,'variables':NV,'residuals':len(expected),'exact_degree':degree(full),'compact_residual_degrees':[degree(p) for p in expected],'expanded_symbolic_port_terms':len(full),'leading_form':leading,'degree_witness':witness,'live_binary_operations':sum(counts.values()),'operation_counts':counts,'full_circuit_polynomial_identity':True}


def check24():
 symbols(['J','F','alpha','f','h','r','v_scale','tau','eta','zeta','y','gamma','o','j','E','c','a','I','u','Z','pair_root','pair_pos1','pair_pos2','pair_pos3'])
 env=environment(True)
 add_aliases(env,[('Nmain','D**2-Delta*c*c-1'),
                  ('Mmain','X*E+2*E*b+Y*(b*b-Delta*c*c-1)'),
                  ('transfer','E-X*Y')])
 require(env['Mmain']==parse('Y*Nmain+(X+2*b)*transfer',env),'localization row identity')
 require(parse('b*b-Delta*c*c',env)==parse('H*(2*a*c*gamma+H*gamma*gamma-c*c)',env),'main norm leading cancellation')
 require(parse('(f*o+y)**2-V**2',env)==parse('(y+c)*(2*f*o+y-c)',env),'auxiliary centered difference of squares')
 forms=[
  'a-E-s*q**3','E-X*Y','c-eta-k*Y',
  'tau**2+(2*tau-k)*E*(c-eta)-1','Mmain','k-R-1-h*E',
  '(K0*q+X)*C-q*F-Z*(q-1)','V-c*j+k-h*E-1',
  'I-(2*r+1)*c*c','I*I-Delta*(f*f-1)',
  '(f*o+y)**2-I*I*(y+c)*(2*f*o+y-c)-1','GP']
 ours=[parse(s,env) for s in forms]
 image=source_images(env)
 require(sum(not p for p in image)==11,'24: eleven eliminated source rows')
 live=replace_unique([p for p in image if p],env['Nmain'],env['Mmain'])
 require(collections.Counter(map(normed,live))==collections.Counter(map(normed,ours[:-1])),'24: all eleven remaining source rows after localization')
 result=check_packet('degree10_24',ours,10,{'powers':{'I':4,'f':2,'o':2,'y':2},'coefficient':4},'64*a**4*gamma**2*(c+2*gamma)**2*(a-E)**2+4*I**4*f**2*o**2*(c+y)**2')
 result['semantic_side_condition']='Y=(2*v_scale+1)*(beta*J+1)^3 is nonzero on common zeros; beta=2^1064921-1>1 and all coordinates integral.'
 return result


def check22():
 symbols(['J','F','alpha','f','h','r','v_scale','tau','eta','y','gamma','o','j','E','c','a','u','Z','pair_root','pair_pos1','pair_pos2','pair_pos3'])
 env=environment(False)
 add_aliases(env,[('strong','I*I-Delta*(f*f-1)'),
                  ('difference','(f*o+y)**2-V*V'),
                  ('oldaux','(f*o+y)**2-I*I*difference-1'),
                  ('newaux','(f*o+y)**2-Delta*(f*f-1)*(y+c)*(2*f*o+y-c)-1')])
 require(env['difference']==parse('(y+c)*(2*f*o+y-c)',env),'22: centered difference identity')
 require(env['newaux']==parse('oldaux+strong*difference',env),'22: elementary row operation')
 forms=['a-E-s*q**3','E-X*Y','c-eta-k*Y',
  'tau**2+(2*tau-k)*E*(c-eta)-1','D*D-Delta*c*c-1',
  'j*c-V-R','(K0*q+X)*C-q*F-Z*(q-1)',
  'strong','newaux','GP']
 ours=[parse(s,env) for s in forms]
 image=source_images(env)
 require(sum(not p for p in image)==13,'22: thirteen eliminated source rows')
 live=replace_unique([p for p in image if p],env['oldaux'],env['newaux'])
 require(collections.Counter(map(normed,live))==collections.Counter(map(normed,ours[:-1])),'22: all nine remaining source rows after elementary operation')
 result=check_packet('degree14_22',ours,14,{'powers':{'a':4,'f':6,'o':2,'y':2},'coefficient':4},'4*a**4*f**6*o**2*(c+y)**2')
 result['semantic_side_condition']='None beyond the inherited source equivalence: the auxiliary operation is invertible, the y change is an integer shear, and I is eliminated by a monic equation.'
 return result


def check_fixed():
 vals={}
 binding=json.loads((ROOT/'coefficients/BINDING.json').read_text())
 for name,rec in binding['payloads'].items():
  raw=gzip.decompress((ROOT/'coefficients'/rec['file']).read_bytes())
  require(hashlib.sha256(raw).hexdigest()==rec['raw_sha256'],'fixed coefficient hash '+name)
  vals[name]=int.from_bytes(raw,'little')
 require(vals['beta']==2**1064921-1 and vals['beta']>1,'nonzero affine q on integer inputs')
 require(vals['cone_A']==2**1113 and vals['cone_B']==2**666104,'literal determinant weights')
 pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
 r=[r for r in pins['files'] if r['local']=='upstream/signed40_sextic.json']
 require(len(r)==1,'unique source40 pin')
 raw=(ROOT/r[0]['local']).read_bytes()
 require(hashlib.sha256(raw).hexdigest()==r[0]['sha256'],'upstream source40 pinned bytes')


def main():
 check_fixed()
 results=[check24(),check22()]
 out={'status':'PASS','independent_of_producer':True,'results':results,'checks':['complete exact residual lists','full source40 arithmetic restoration','all new row identities','variable count and liveness','full symbolic SOS expansions','complete leading forms','fixed-port-independent degree witnesses','complete circuit identities and live operation counts','source pin and all fixed integer hashes'],'boundary':'Algebraic verification is exact. The nonzero-Y argument and inherited sign, canonical cone, Pell and compiler proofs are mathematical dependencies stated separately.'}
 (HERE/'INTEGER_EXTENSIONS_INDEPENDENT_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,indent=2))

if __name__=='__main__':main()
