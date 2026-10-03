import collections, hashlib, itertools, json, random, sys, time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
import argparse
_parser_args=argparse.ArgumentParser(description=__doc__)
_parser_args.add_argument('--output-dir',type=Path,default=ROOT)
OUT=_parser_args.parse_args().output_dir.resolve();OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT))
from compiler import Emitter, Certificate, _parser, natural_pairs
from circuit import Circuit, const, var, sub, ev
F=json.loads((ROOT/'fixtures.json').read_text())
report={'file_hashes':{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in ('compiler.py','circuit.py','audit-design.md','fixtures.json')},'checks':collections.Counter()}
def require(b,why):
 if not b:raise RuntimeError(why)
def literal(m,X,block):
 lo,hi=(0,m.E_count) if block=='E' else (m.E_count,m.factors)
 out={}
 for ID in range(lo,hi):
  g=m.gate_at(ID)
  for ell,shape in enumerate(g.shapes):
   for first in X:
    u=first-shape[0]
    if all(u+d in X for d in shape) and sum(abs(x-u)<=g.L for x in X)==len(shape):
     if g.guard is not None and not _parser._guard_sparse(g.guard,X,u):continue
     require((ID,u) not in out,('literal duplicate',ID,u))
     out[ID,u]=ell
 return out
for (name,n),cases in itertools.groupby(sorted(F['cases'],key=lambda v:(v['source'],v['mass'])),key=lambda v:(v['source'],v['mass'])):
 cases=list(cases);m=_parser.compile_lazy_source(F['sources'][name]['data'])
 for block in ('E','P'):
  c=Circuit([f'x{i}{s}' for i in range(n) for s in '+-']);X=[sub(var(2*i),var(2*i+1)) for i in range(n)]
  raw=Emitter(c,m).raw(X,block)
  require(c.ledger()['max_residual_degree']<=2,'degree')
  for case in cases:
   xs=case['input'];v=c.evaluate(natural_pairs(xs));actual={}
   for slot in raw:
    if ev(slot['raw'],v):
     ID,u=ev(slot['ID'],v),ev(slot['u'],v);key=(ID,u)
     require(key not in actual,('duplicate slot',case['id'],block,key))
     actual[key]=slot['label'];g=m.gate_at(ID);arity=ev(slot['arity'],v)
     old=tuple(ev(p,v) for p in slot['old']);new=tuple(ev(p,v) for p in slot['new'])
     require(set(old[:arity])=={u+d for d in g.shapes[slot['label']]},('old descriptor',case['id'],slot))
     require(set(new[:arity])=={u+d for d in g.shapes[1-slot['label']]},('new descriptor',case['id'],slot))
     require((arity==3 or (old[2]==0 and new[2]==0)),('pair padding',case['id']))
     report['checks']['live_descriptor_shapes']+=1
   expected={(i,u):ell for i,u,ell in case['blocks'][block]['raw']}
   require(actual==expected==literal(m,xs,block),('raw mismatch',case['id'],block,actual,expected))
   report['checks']['raw_snapshots']+=1
 report['checks']['source_mass_groups']+=1
 print('raw completed',name,n,flush=True)
# Sorting with equal anchors, false rows, negative values, padded widths and permutations.
rng=random.Random(20261003)
for width in range(1,18):
 c=Circuit([f'r{i}{f}' for i in range(width) for f in ('b','p','m')]);e=Emitter(c,None)
 raw=[{'raw':var(3*i),'u':sub(var(3*i+1),var(3*i+2))} for i in range(width)]
 rows=e.sort_keys(raw)
 for repeat in range(25):
  original=[(rng.randrange(2),rng.randrange(-3,4),i) for i in range(width)]
  inputs=[]
  for b,u,i in original:inputs.extend([b]+natural_pairs([u]))
  vals=c.evaluate(inputs);actual=[tuple(ev(p,vals) for p in row) for row in rows]
  keys=[(-b,u) for b,u,i in actual]
  require(keys==sorted(keys),('sort order',width,original,actual))
  require(collections.Counter(actual)==collections.Counter(original+[(0,0,-1)]*(len(rows)-width)),('sort conservation',width))
  report['checks']['sorting_cases']+=1
# Each comparator and signed lift has a unique natural solution, including strict split at -1/0.
for d in range(-9,10):
 c=Circuit([]);b=c.ge(const(d),const(0));z=c.integer(const(d));val=c.evaluate([])
 require((val[0],val[1])==(int(d>=0), d if d>=0 else -d-1),'ge witness')
 solutions=[(b,s) for b in range(3) for s in range(12) if b*(b-1)==0 and d-(2*b-1)*s+1-b==0]
 require(solutions==[(val[0],val[1])],('ge uniqueness',d,solutions))
 solutions=[(p,m) for p in range(12) for m in range(12) if p-m==d and p*m==0]
 require(solutions==[(max(d,0),max(-d,0))],('signed uniqueness',d))
 report['checks']['primitive_domain_cases']+=1
# Canonical input acceptance and rejection do not rely on a promise.
for n in (0,1,2):
 cert=Certificate(F['sources']['empty']['data'],n,0)
 xs=list(range(-n,0));v=cert.witness(xs,xs)
 require(cert.circuit.score(v)==0,'T0 acceptance')
 if n:
  bad=list(v);bad[0]+=1;bad[1]+=1
  require(cert.circuit.score(bad)>0,'noncanonical pair accepted')
 if n==2:
  for xs in ([0,0],[1,0]):
   try:cert.witness(xs,xs)
   except ValueError:pass
   else:raise RuntimeError(('invalid domain accepted',xs))
 report['checks']['zero_horizon_mass_cases']+=1
rng=random.Random(20261003);counts=collections.Counter()
for width in range(1,10):
 c=Circuit([f'x{i}{s}' for i in range(width) for s in ('b','p','m')]);e=Emitter(c,None)
 raw=[]
 for i in range(width):
  u=sub(var(3*i+1),var(3*i+2))
  raw.append(dict(raw=var(3*i),u=u,ID=const(11+i),arity=const(2+i%2),old=[const(2*i+j-10) for j in range(3)],new=[const(-2*i-j+10) for j in range(3)]))
 lanes=e.lanes(raw,2*width,4)
 for repeat in range(30):
  bits=[rng.randrange(2) for i in range(width)];us=[rng.randrange(-20,21) for i in range(width)];inp=[]
  for b,u in zip(bits,us):inp.extend([b]+natural_pairs([u]))
  values=c.evaluate(inp)
  expected=sorted([i for i in range(width) if bits[i] and all(j==i or not bits[j] or abs(us[j]-us[i])>4 for j in range(width))],key=lambda i:us[i])
  counts['compaction_multiple_live_cases']+=int(len(expected)>=2)
  for k,lane in enumerate(lanes):
   vals={field:ev(lane[field],values) for field in ('present','ID','u','arity')}
   vals.update({field:[ev(p,values) for p in lane[field]] for field in ('old','new')})
   if k<len(expected):
    i=expected[k];want=dict(present=1,ID=11+i,u=us[i],arity=2+i%2,old=[2*i+j-10 for j in range(3)],new=[-2*i-j+10 for j in range(3)])
   else:want=dict(present=0,ID=0,u=0,arity=0,old=[0]*3,new=[0]*3)
   if vals!=want:raise RuntimeError((width,repeat,k,vals,want,bits,us))
  counts['compaction_padding_cases']+=1
  counts['lane_payloads_checked']+=len(lanes)

report['checks'].update(counts)
report['checks']=dict(report['checks']);report['result']='pass'
(OUT/('audit-emitter-receipt-optimized.json'if not __debug__ else 'audit-emitter-receipt.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
