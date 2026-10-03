#!/usr/bin/env python3
"""Independent runtime, exact-domain, snapshot, and polynomial-cost audit.
No assert statements: identical contracts under python -O.
"""
import argparse,copy,hashlib,itertools,json,sys,time
from fractions import Fraction
from pathlib import Path
BUNDLE=Path(__file__).resolve().parents[2]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--certificate-root',default=str(BUNDLE/'primitive-certificates'))
parser.add_argument('--literal-source',default=str(BUNDLE/'source/source.json'))
parser.add_argument('--output',default=str(Path(__file__).resolve().parent))
args=parser.parse_args()
ROOT=Path(args.certificate_root).resolve()
SOURCE_PATH=Path(args.literal_source).resolve()
sys.path.insert(0,str(ROOT));import certificate as c
OUT=Path(args.output).resolve();OUT.mkdir(parents=True,exist_ok=True)
CODE_BEFORE=hashlib.sha256((ROOT/'certificate.py').read_bytes()).hexdigest()
checks=0;rejects=0

def ck(v,msg):
 global checks;checks+=1
 if not v:raise RuntimeError(msg)

def rejects_call(fn,msg):
 global rejects
 try:fn()
 except (ValueError,TypeError,AttributeError,IndexError): rejects+=1;return
 raise RuntimeError('did not reject: '+msg)

def source(rows,controls=('S','T','H'),start='S',halt='H'):
 return dict(schema='reversible-two-counter-v1',controls=list(controls),start=start,halt=halt,class_cut=0,branches=[dict(name=str(i),source=s,target=t,side=2*k-1,delta=d,guard=g) for i,(s,t,k,d,g) in enumerate(rows)])
TRUE={'op':'true'}
def atom(op,k):return dict(op=op,counter=k,value=0)
def edges(kind,s,t):
 if kind=='A':return [(s,t,0,0,TRUE)]
 if kind.startswith('I'):return [(s,t,int(kind[1]),1,TRUE)]
 if kind.startswith('D'):
  k=int(kind[1]);return [(s,t,k,-1,atom('gt',k))]
 k=int(kind[1]);return [(s,t,1-k,0,atom('eq',k)),(s,t,1-k,0,atom('gt',k))]

def run(src,H,initial):
 q=src['start'];v=tuple(initial);trace=[]
 for _ in range(H):
  candidates=[]
  for i,b in enumerate(src['branches']):
   g=b['guard'];op=g['op']
   enabled=op=='true' or (op=='eq' and v[g['counter']]==0) or (op=='gt' and v[g['counter']]>0)
   if q==b['source'] and enabled:candidates.append((i,b))
  ck(len(candidates)<=1,'independent interpreter detected nondeterminism')
  if not candidates:return None
  i,b=candidates[0];old=v;new=list(v);new[(b['side']+1)//2]+=b['delta'];v=tuple(new);q=b['target'];trace.append((i,b,old,v))
 return trace if q==src['halt'] else None

def expected_witness(cert,trace):
 w=[0]*cert.nvars;theta=0
 g=cert.machine.geometry()
 for t,(i,b,old,new) in enumerate(trace):
  w[t*cert.width+i]=1
  for k in (0,1):
   off=int(b['delta']==0 and b['guard']['op']=='gt' and b['guard']['counter']==k)
   w[t*cert.width+cert.B+k]=new[k]-off
   w[t*cert.width+cert.B+2+k]=off
  theta+=1 if b['delta']==0 else 3+2*(g['Z']+old[(b['side']+1)//2])+b['delta']-4*g['S']
 if cert.clock:w[-1]=theta
 return tuple(w)

def direct_value(cert,w):
 # Independent arithmetic equations, without iter_raw_terms, polynomial, row or evaluation.
 m=cert.machine;B=cert.B;W=B+4;v=cert.initial_counters;q=m.codes[cert.initial_state];r=[];theta=0
 for t in range(cert.H):
  e=w[t*W:t*W+B];z=w[t*W+B:t*W+B+2];off=w[t*W+B+2:t*W+B+4]
  r += [sum(e)-1,sum(e[i]*m.codes[b.source] for i,b in enumerate(m.branches))-q]
  new=[z[k]+off[k] for k in (0,1)]
  r += [new[k]-v[k]-sum(e[i]*b.delta for i,b in enumerate(m.branches) if b.counter==k) for k in (0,1)]
  r += [off[k]-sum(e[i] for i,b in enumerate(m.branches) if b.kind=='P' and b.tested==k) for k in (0,1)]
  r += [e[i]*z[b.tested] for i,b in enumerate(m.branches) if b.kind=='Z']
  if cert.real:r.append(sum(x*x for x in e)-1)
  geo=m.geometry()
  theta+=sum(e[i]*(1 if b.delta==0 else 3+2*(geo['Z']+v[b.counter])+b.delta-4*geo['S']) for i,b in enumerate(m.branches))
  v=new;q=sum(e[i]*m.codes[b.target] for i,b in enumerate(m.branches))
 r.append(q-m.codes[m.halt])
 if cert.clock:r.append(w[-1]-theta)
 return sum(x*x for x in r)

def check_ledger(cert):
 ledger=cert.ledger();rows=[cert.row(i) for i in range(cert.nrows)]
 lengths=[len(p) for _,p in rows]
 ck(sum(lengths)==ledger['collected_residual_monomials'],'collected ledger mismatch')
 ck(sum(x*x for x in lengths)==ledger['expanded_ordered_product_occurrences'],'ordered ledger mismatch')
 ck(sum(len(tuple(cert.iter_raw_terms(i))) for i in range(cert.nrows))==ledger['raw_residual_term_slots'],'raw ledger mismatch')
 ck(sum(x>0 for x in lengths)==ledger['nonzero_residuals'],'nonzero rows ledger mismatch')
 ck(all(abs(a)<=ledger['residual_coefficient_height_bound'] for _,p in rows for a,mon in p),'residual coefficient bound')
 exp=cert.expanded()
 ck(all(len(mon)<=4 for a,mon in exp),'quartic bound')
 ck(all(abs(a)<=ledger['expanded_coefficient_height_bound'] for a,mon in exp),'expanded coefficient bound')

start=time.time();cases=0
kinds=['A','I0','I1','D0','D1','T0','T1']
for first,second in itertools.product(kinds,repeat=2):
 s=source(edges(first,'S','T')+edges(second,'T','H'))
 m=c.load_machine(s)
 for initial in itertools.product(range(3),repeat=2):
  for H in range(4):
   trace=run(s,H,initial)
   for clock,real in itertools.product((False,True),repeat=2):
    cert=c.Certificate(m,H,'S',initial,clock=clock,nonnegative_real=real);w=cert.witness()
    ck((w is None)==(trace is None),'halting equivalence')
    if trace is not None:
     expected=expected_witness(cert,trace);ck(w==expected,'whole witness reconstruction');ck(cert.evaluate(w)==direct_value(cert,w)==0,'independent residual mismatch')
     for j in range(len(w)):
      bad=list(w);bad[j]+=1;ck(cert.evaluate(bad)>0,'individual coordinate freedom')
     led=cert.ledger();ck(all(x<=led['witness_coordinate_height_bound'] for x in w),'witness height bound')
    cases+=1
  for H in (0,1,2,3):
   for clock,real in itertools.product((False,True),repeat=2):
    if initial in [(0,0),(1,2)]:check_ledger(c.Certificate(m,H,'S',initial,clock=clock,nonnegative_real=real))
# Exhaust all bounded natural witness coordinates for every tested-counter/side choice.
exhaustive=0
for tested,side in itertools.product((0,1),repeat=2):
 s=source([('S','H',side,0,atom('eq',tested)),('S','H',side,0,atom('gt',tested))])
 m=c.load_machine(s)
 for n in range(3):
  initial=[1,1];initial[tested]=n;cert=c.Certificate(m,1,'S',initial);truth=cert.witness();zeros=[]
  for w in itertools.product(range(3),repeat=cert.nvars):
   v=cert.evaluate(w);ck(v==direct_value(cert,w),'exhaustive residual mismatch')
   if v==0:zeros.append(w)
   exhaustive+=1
  ck(zeros==[truth],'entire bounded natural fiber nonunique')
# Real norm is necessary: midpoint of branch source codes spoofs state in the unpaid real core.
s=source([('A','H',0,0,TRUE),('B','H',0,0,TRUE),('C','H',0,0,TRUE)],controls=('A','B','C','H'),start='B')
m=c.load_machine(s);paid=c.Certificate(m,1,'B',(0,0),nonnegative_real=True)
fractional=(Fraction(1,2),0,Fraction(1,2),0,0,0,0)
ck(direct_value(c.Certificate(m,1,'B',(0,0)),fractional)==0,'expected unpaid fractional pathology absent')
ck(paid.evaluate(fractional)==Fraction(1,4),'real norm failed fractional rejection')
ck(paid.evaluate(paid.witness())==0,'paid real witness failed')
# Zero horizon, including immediate halt and clock=0, with no branches.
s=source([],controls=('H',),start='H');m=c.load_machine(s)
for clock,real in itertools.product((False,True),repeat=2):
 cert=c.Certificate(m,0,'H',(7,11),clock=clock,nonnegative_real=real)
 ck(cert.witness()==((0,) if clock else ()),'zero horizon witness');check_ledger(cert)
# Snapshot and reinitialization resistance.
s=source(edges('T1','S','H'));m=c.load_machine(s);cert=c.Certificate(m,1,'S',(0,2));expected=cert.witness();b=m.branches[0]
s['controls'][0]='evil';s['branches'][0]['guard']['counter']=0;s['branches'].clear()
ck(cert.witness()==expected,'source alias mutated certificate')
rejects_call(lambda:b.__init__('x','S','H',0,0,TRUE),'Branch reinit')
rejects_call(lambda:m.__init__(['S','H'],[],'S','H'),'Machine reinit')
rejects_call(lambda:cert.__init__(m,0,'S',(0,0)),'Certificate reinit')
rejects_call(lambda:setattr(b,'kind','A'),'Branch setattr')
rejects_call(lambda:m.codes.__setitem__('S',99),'code map mutation')
rejects_call(lambda:m.outgoing.__setitem__('S',()),'outgoing map mutation')
ck(cert.witness()==expected,'reinit damaged snapshot')
# Exact numeric and schema boundaries; normal/-O identical.
for bad in (True,False,0.0,1.0,Fraction(1,1),-1,None,'1'):
 rejects_call(lambda bad=bad:c.Certificate(m,bad,'S',(0,0)),'bad horizon')
 rejects_call(lambda bad=bad:c.Certificate(m,1,'S',(bad,0)),'bad input counter')
 rejects_call(lambda bad=bad:m.transition('S',(bad,0)),'bad transition counter')
 rejects_call(lambda bad=bad:m.duration(0,(bad,0)),'bad duration counter')
 rejects_call(lambda bad=bad:b.enabled((bad,0)),'bad enabled counter')
 rejects_call(lambda bad=bad:cert.selector(bad,0),'bad selector layer')
 rejects_call(lambda bad=bad:cert.selector(0,bad),'bad selector row')
 rejects_call(lambda bad=bad:cert.row(bad),'bad residual index')
 rejects_call(lambda bad=bad:cert.name(bad),'bad variable index')
 rejects_call(lambda bad=bad:cert.materialize(max_variables=bad),'bad variable bound')
 rejects_call(lambda bad=bad:cert.expanded(max_ordered_products=bad),'bad expansion bound')
for bad in (0,1,0.0,None,'true',Fraction(1,1)):
 rejects_call(lambda bad=bad:b.mask(bad),'bad image flag')
for bad in (None,TRUE,object(),True):
 rejects_call(lambda bad=bad:m.kappa(bad),'unvalidated branch kappa')
for bad in ([],[0],[0,0,0],object()):
 rejects_call(lambda bad=bad:b.enabled(bad),'malformed enabled counters')
for bad in (True,0.0,Fraction(1,1),-1):
 w=list(expected);w[0]=bad;rejects_call(lambda w=w:cert.evaluate(w),'bad natural witness type')
for bad in (True,0.0,-1):
 w=list(paid.witness());w[0]=bad;rejects_call(lambda w=w:paid.evaluate(w),'bad real witness type/domain')
for guard in ({'op':'true','extra':1},{'op':'gt','counter':True,'value':0},{'op':'eq','counter':0,'value':False},{'op':'not','arg':TRUE},{'op':'gt','counter':0,'value':1},lambda x:True):
 rejects_call(lambda guard=guard:c.Branch('x','S','H',0,0,guard),'bad primitive guard')
for rows in ([('S','H',0,-1,TRUE)],[('S','H',0,1,atom('gt',0))],[('S','H',0,-1,atom('gt',1))],[('H','S',0,0,TRUE)],[('S','H',0,0,TRUE),('S','T',0,0,TRUE)]):
 rejects_call(lambda rows=rows:c.load_machine(source(rows)),'bad action/source')
rejects_call(lambda:json.loads('{"a":1,"a":2}',object_pairs_hook=c.nodup),'duplicate JSON key')
# Polynomials can be evaluated separately after ordinary expansion.
small=c.Certificate(c.load_machine(source(edges('T0','S','H'))),1,'S',(1,2),clock=True,nonnegative_real=True)
for w in (small.witness(),tuple([0]*small.nvars),tuple([2]*small.nvars)):
 exp=small.expanded();v=0
 for a,mon in exp:
  for j in mon:a*=w[j]
  v+=a
 ck(v==small.evaluate(w),'expanded polynomial evaluation mismatch')
# Pinned literal source is inspected, never materialized as a horizon-one polynomial.
path=SOURCE_PATH;large,sha=c.read_machine(path,require_reversible=True)
ck(sha=='38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a','source pin')
for H in (0,1,2,10**30):
 cert=c.Certificate(large,H,large.start,(1,0),clock=True);led=cert.ledger()
 ck(led['variables']==141565*H+1,'literal vars');ck(led['squared_residual_slots']==23435*H+2,'literal rows')
 ck(led['raw_residual_term_slots']==(839918*H-66065 if H else 2),'literal raw terms')
 if H:
  for method in (cert.witness,cert.materialize,cert.expanded):rejects_call(method,'literal materialization default bound')
 if H in (0,1,2): (OUT/f'literal-ledger-H{H}.json').write_text(json.dumps(led,indent=2)+'\n')
CODE_AFTER=hashlib.sha256((ROOT/'certificate.py').read_bytes()).hexdigest()
ck(CODE_BEFORE==CODE_AFTER,'producer source changed during audit run')
receipt=dict(status='passed',checks=checks,expected_rejections=rejects,primitive_program_flag_cases=cases,exhaustive_bounded_fiber_assignments=exhaustive,python_optimized=not __debug__,seconds=round(time.time()-start,3),source_sha256=sha,certificate_sha256=hashlib.sha256((ROOT/'certificate.py').read_bytes()).hexdigest(),auditor_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Independent residual evaluator and interpreter; exact small expansion/count parity; h=0, blocked/padded run, cross-side guards, snapshot/reinit, exact-domain contracts, paid real norm and lazy literal large-H ledger')
name='optimized' if not __debug__ else 'normal';(OUT/f'audit-{name}-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
