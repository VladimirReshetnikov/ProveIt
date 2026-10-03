#!/usr/bin/env python3
"""Independent cancellation-aware degree and leading coefficient certificate.
Reads frozen raw source/JSON only; executes no producer or upstream source.
"""
from array import array
from pathlib import Path
import argparse, hashlib, json, mmap, resource, struct, time

HERE = Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-dir',required=True,type=Path,help='Directory containing the three original pinned arithmetic files')
parser.add_argument('--output',type=Path,required=True,help='Explicit certificate output path outside the release')
args=parser.parse_args()
# Portable packaging adaptation: no replay result may overwrite delivered evidence.
args.output=args.output.expanduser().resolve()
_release=Path(__file__).resolve().parents[2]
if args.output == _release or _release in args.output.parents:
 raise ValueError('Output must be outside the complete release')
SOURCE=args.source_dir
PINS = {
 'universal.dag': 'a07c1ba41e3a18fafd05c19b8ac39211b0475e30ed8a08ddf43c45a9f5f440f2',
 'universal.json': '41e6f754df8f60448e1207ef36e6161729b52004fac719a580d6ec643d039d49',
 'native_unit_kernel.json': '2d88343037c08fe8b073f67dca531ee73309c0735c1d98a23c20b9ddb1eb08ae'}
ROW = struct.Struct('<Bqq'); BASE = 1 << 50
MAX_NODES=4_000_000; MAX_INPUTS=800_000; MAX_TERMS=256
MAX_RSS=512*1024**2; MAX_SECONDS=180
resource.setrlimit(resource.RLIMIT_AS,(MAX_RSS,MAX_RSS))
resource.setrlimit(resource.RLIMIT_CPU,(MAX_SECONDS,MAX_SECONDS))
start=time.monotonic()

def need(ok,msg):
 if not ok: raise ValueError(msg)
def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()

# Exact sparse polynomial identity in four independent indeterminates u,a,c,gamma.
# Neither positivity nor any residual equality enters this calculation.
z=(0,0,0,0)
one={z:1}
def padd(x,y,sgn=1):
 r=x.copy()
 for k,v in y.items():r[k]=r.get(k,0)+sgn*v
 r={k:v for k,v in r.items() if v}
 need(len(r)<=MAX_TERMS,'symbolic term limit')
 return r
def pmul(x,y):
 need(len(x)*len(y)<=MAX_TERMS**2,'symbolic product limit')
 r={}
 for k,v in x.items():
  for l,w in y.items():
   e=tuple(a+b for a,b in zip(k,l));r[e]=r.get(e,0)+v*w
 r={k:v for k,v in r.items() if v}
 need(len(r)<=MAX_TERMS,'symbolic term limit')
 return r
def smul(n,x):return {k:n*v for k,v in x.items() if n*v}
def prod(*xs):
 r=one
 for x in xs:r=pmul(r,x)
 return r
u,a,c,ga=({tuple(int(i==j) for i in range(4)):1} for j in range(4))
d=padd(smul(4,a),smul(3,one));t=padd(padd(u,prod(a,c)),prod(ga,d))
lhs=padd(prod(t,t),prod(padd(prod(a,a),d),c,c),-1)
terms=[prod(u,u),smul(2,prod(u,a,c)),smul(2,prod(u,ga,d)),smul(2,prod(a,c,ga,d)),prod(ga,ga,d,d),smul(-1,prod(d,c,c))]
rhs={}
for p in terms:rhs=padd(rhs,p)
need(lhs==rhs,'norm identity failed')
identity={'indeterminates':['u','a','c','gamma'],'left_monomials':len(lhs),'right_monomials':len(rhs),'exact_dictionary_equality':True,
 'expanded_terms':[{'powers':list(k),'coefficient':v} for k,v in sorted(lhs.items())]}

for name,pin in PINS.items():need(digest(SOURCE/name)==pin,'source pin '+name)
m=json.loads((SOURCE/'universal.json').read_text());kernel=json.loads((SOURCE/'native_unit_kernel.json').read_text())
need(m['input_base']==BASE and m['magic_hex']==b'CDAGv1\0\0'.hex(),'source format')
need(m['input_count']<=MAX_INPUTS,'input limit')
N=m['ledger']['operations'];need(N<=MAX_NODES,'node limit')
need(N==3_600_546 and m['input_count']==797_141,'frozen size')
next_input=0;names={};roles={}
for r in m['inputs']:
 need(r['start']==next_input and r['count']>0,'partition gap')
 need(r['name'] not in names,'duplicate coordinate family')
 names[r['name']]=BASE+r['start'];next_input+=r['count'];roles[r['role']]=roles.get(r['role'],0)+r['count']
need(next_input==m['input_count'] and roles=={'external':6,'witness':797135},'partition census')
need([r['name'] for r in m['inputs'] if r['role']=='external']==['x','a_e','p_e','s_e','C_e','L_e'],'external names')
consts=m['constants'];small={int(r[1]): -i-1 for i,r in enumerate(consts) if r[0]=='int'}
ports={'H':3600206,'M':3600215,'Z':3600216,'scale':3600218}
registers={'@'+k:v for k,v in ports.items()}
registers.update({k:names['native.'+k] for k in kernel['auxiliaries']})

def constant_residues(mod):
 values=[]
 for i,r in enumerate(consts):
  op=r[0]
  if op=='int':need(len(r)==2,'integer arity');v=int(r[1])%mod
  elif op in ('pow2','geom4'):
   need(len(r)==2 and type(r[1]) is int and r[1]>=0,'exponent shape')
   if op=='pow2':v=pow(2,r[1],mod)
   else:
    # Integer division is valid since 4^n mod (3*mod) is 1 modulo 3.
    w=pow(4,r[1],3*mod);need((w-1)%3==0,'geom remainder');v=((w-1)//3)%mod
  else:
   need(op in ('add','sub','mul') and len(r)==3,'constant operation')
   need(all(type(h) is int and -i<=h<0 for h in r[1:]),'nonconstant or forward recipe')
   x,y=(values[-h-1] for h in r[1:]);v=(x+y if op=='add' else x-y if op=='sub' else x*y)%mod
  values.append(v)
 return values

with (SOURCE/'universal.dag').open('rb') as file,mmap.mmap(file.fileno(),0,access=mmap.ACCESS_READ) as mm:
 need(mm[:8]==b'CDAGv1\0\0' and len(mm)==8+17*N,'raw format')
 need(len(kernel['source'])==67,'kernel size')
 def kh(v):return small[v] if type(v) is int else registers[v]
 for i,(name,op,x,y) in enumerate(kernel['source'],3600219):
  expected=({'+' :0,'-':1,'*':2}[op],kh(x),kh(y))
  need(ROW.unpack_from(mm,8+17*i)==expected,'kernel mismatch '+name)
  need(name not in registers,'duplicate kernel name');registers[name]=i
 need([registers[k] for k in kernel['unit_factors']]==m['extra']['unit_factors'],'factor refs')
 need(registers[kernel['unit']]==m['extra']['native_unit'],'unit ref')
 override=registers['and__R15'];need(override==3600240,'norm ref')
 U=registers['and__wn2'];A=registers['and__R12'];C=registers['and__R10a'];G=registers['and__ga'];D=registers['and__a4m5']
 trials=[]
 for modulus in [17,1_000_000_007]:
  cv=constant_residues(modulus);degree=array('I');lead=array('I')
  def at(h):
   if h<0:need(-h<=len(cv),'constant ref');return (0,cv[-h-1])
   if h>=BASE:need(h-BASE<m['input_count'],'input ref');return (1,1)
   need(h<len(degree),'gate forward ref');return degree[h],lead[h]
  def add(x,y,sgn=1):
   d=max(x[0],y[0]);return d,((x[1] if x[0]==d else 0)+sgn*(y[1] if y[0]==d else 0))%modulus
  def mul(x,y):return x[0]+y[0],x[1]*y[1]%modulus
  def many(*xs):
   r=(0,1)
   for x in xs:r=mul(r,x)
   return r
  rewrite_terms=None
  for i in range(N):
   op,x,y=ROW.unpack_from(mm,8+17*i);need(op in (0,1,2),'invalid opcode')
   xv,yv=at(x),at(y)
   if op==2:dv,v=mul(xv,yv)
   else:dv,v=add(xv,yv,1 if op==0 else -1)
   if i==override:
    u,a,c,g,d=(at(h) for h in [U,A,C,G,D])
    rt=[many(u,u),many((0,2),u,a,c),many((0,2),u,g,d),many((0,2),a,c,g,d),many(g,g,d,d),many((0,modulus-1),d,c,c)]
    rewrite_terms=[{'degree_bound':dd,'leading_value':vv} for dd,vv in rt]
    dv,v=(0,0)
    for value in rt:dv,v=add((dv,v),value)
   degree.append(dv);lead.append(v)
   if i%100000==0:need(time.monotonic()-start<MAX_SECONDS,'wall time limit')
  def record(h):return {'ref':h,'degree_bound':degree[h] if h<BASE else 1,'leading_value':lead[h] if h<BASE else 1}
  residuals=[]
  for j,(x,y) in enumerate(m['extra']['residual_pairs']):
   dd,vv=add(at(x),at(y),-1);residuals.append({'index':j,'degree_bound':dd,'leading_value':vv})
  output=record(m['output']);need(output['degree_bound']==69_339_973,'unexpected output degree')
  need(output['leading_value']!=0,'leading coefficient vanished')
  closed_coefficient=(-pow(2,148,modulus)*pow(pow(2,551891,modulus)*794976 % modulus,23_113_311,modulus)) % modulus
  need(output['leading_value']==closed_coefficient,'closed leading coefficient mismatch')
  trials.append({'modulus':modulus,'input_specialization':'Every one of the 797141 coordinates equals t',
   'closed_form_leading_coefficient':closed_coefficient,'output':output,'unit':record(m['extra']['native_unit']),'unit_factors':[record(h) for h in m['extra']['unit_factors']],
   'positive_finalizer':record(m['extra']['finalizer_positive']),
   'native_ports':{k:record(v) for k,v in ports.items()},'native_kernel':{k:record(v) for k,v in registers.items() if not k.startswith('@')},
   'norm_rewrite_terms':rewrite_terms,'residuals':residuals,'exact_degree_certified':True})
  print(json.dumps({'modulus':modulus,'output':output,'unit':trials[-1]['unit'],'unit_factors':trials[-1]['unit_factors'],'positive_finalizer':trials[-1]['positive_finalizer']}),flush=True)
result={'status':'PASS','total_degree':69_339_973,'previous_syntactic_upper_bound':71_731_007,'decrease':2_391_034,
 'scope':'The SAME frozen integer polynomial; all six external parameters and all 797135 witnesses have degree one.',
 'identity':identity,'frozen_kernel_all_67_rows_match':True,'source_pins':PINS,'trials':trials,
 'resources':{'max_nodes':MAX_NODES,'max_inputs':MAX_INPUTS,'max_symbolic_terms':MAX_TERMS,'memory_limit_bytes':MAX_RSS,'cpu_limit_seconds':MAX_SECONDS,'wall_seconds':time.monotonic()-start,'max_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024},
 'checker_sha256':digest(Path(__file__))}
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','total_degree':result['total_degree'],'resources':result['resources']}))
