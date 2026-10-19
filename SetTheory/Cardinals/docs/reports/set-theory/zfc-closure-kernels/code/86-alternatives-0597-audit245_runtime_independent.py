"""Independent runtime replay against the recovered, previously reviewed engine.
Inputs from the 245 archive are parsed as data. Its checker code is not imported.
"""
from pathlib import Path
import os,sys,json,inspect,importlib.util,hashlib,time,collections
R=Path(__file__).resolve().parent;A=R/'audit245_runtime_copy';B=R.parent/'context_folds';began=time.monotonic()
os.environ['ZFC246_BASE']=str(B/'recovered/63');os.environ['ZFC246_TABLE']=str(A/'machine/zfc245_old.tm')
spec=importlib.util.spec_from_file_location('old_reviewed_fold',B/'recovered/64/experiments/decoder/fold_search246.py');f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
assert len(f.T)==490
src=inspect.getsource(f.A.run);assert src.count('40-len(pc)')==1
exec(src.replace('40-len(pc)','64-len(pc)'),f.A.__dict__)
logical=json.loads((A/'certificate/sites_logical.json').read_text());physical=json.loads((A/'certificate/sites_physical.json').read_text())
assert len(logical)==len(physical)==6460
assert [[p,op,f.L.PHYSICAL[r]if op in('CI','CD')else r]for p,op,r in logical]==physical
original=f.L.program_sites(B/'recovered/63/sources/Prog254.v')
assert [(op,r)for p,op,r in logical]==[(op,r)for p,op,r in original]
leaves={p:(op,r)for p,op,r in physical};prefixes={p[:i]for p in leaves for i in range(len(p))}
assert len(leaves)==6460 and len(prefixes)==6459 and not prefixes.intersection(leaves)
assert all(p+b in prefixes or p+b in leaves for p in prefixes for b in '01')
def inc(word):
 n=len(word);v=(int(word,2)if word else 0)+1
 return (format(v%(1<<n),'0'+str(n)+'b')if n else ''),v==(1<<n)
def strip(word,bit,n):
 k=len(word)
 while k and n:
  k-=1;n-=word[k]==bit
 return word[:k]
def leaf(word):
 p=''
 for i in range(51):
  p+=word[i]if i<len(word)else'0'
  if p in leaves:
   assert '1'not in word[len(p):];return p
 raise AssertionError('No decoded leaf')
failures=[];case_count=rules=normalized=0;minimum=10**9;deltas=collections.Counter()
for p,op,r in physical:
 for zero in ((True,False)if op=='CD'else(None,)):
  guard=(r,zero)if op=='CD'else None;effect=None;extra=0;overflow=False
  if op=='CI':nxt,overflow=inc(p);effect=('inc',r)
  elif op=='CD'and not zero:nxt,overflow=inc(p);effect=('dec',r);extra=1
  elif op=='CD':nxt,overflow=inc(strip(p,'0',1))
  elif op=='CB':nxt,overflow=inc(strip(p,'0',r))
  elif op=='CC':nxt=strip(p,'1',r)
  else:assert op=='CH';nxt=''
  delta=extra+int(overflow);gap=64+delta-len(nxt);assert gap>=0
  target=f.A.canon([('b',1)],[('b',int(b))for b in nxt]+[('r',0,1,gap),('b',1),('box',('plain',effect))])
  try:
   rr,t=f.A.run(f.T,p,guard,target,halt=op=='CH',fuel=1000);assert t>0;rules+=sum(rr.values());minimum=min(minimum,t)
  except (AssertionError,KeyError)as e:failures.append([case_count,p,op,r,zero,repr(e)])
  if op!='CH':
   cp=leaf(nxt);assert nxt+'0'*gap==cp+'0'*(64+delta-len(cp));normalized+=1;deltas[delta]+=1
  case_count+=1
assert case_count==8391 and normalized==8390 and not failures
root=leaf('');assert root+'0'*(64-len(root))=='0'*64
# Independent total-table parsing and canonical renumbering equality.
def parse(path):
 t={};start=None
 for line in path.read_text().splitlines():
  if line.startswith('#! start'):start=int(line.split()[-1]);continue
  if not line.strip()or line.startswith('#'):continue
  q,b,w,d,s=line.split();q,b,w,s=map(int,(q,b,w,s));assert b in(0,1)and w in(0,1)and d in('L','R')and(q,b)not in t;t[q,b]=(w,d,s)
 return t,start
old,start=parse(A/'machine/zfc245_old.tm');canonical,newstart=parse(A/'machine/zfc245.tm');mapping={int(k):v for k,v in json.loads((A/'machine/renumbering.json').read_text())['old_to_canonical'].items()}
assert start==95 and newstart==0 and len(canonical)==490
assert {q for q,b in canonical}==set(range(245)) and {s for w,d,s in canonical.values()}-set(range(245))=={245}
assert { (mapping[q],b):(w,d,mapping[s])for(q,b),(w,d,s)in old.items()}==canonical
sha=hashlib.sha256((A/'machine/zfc245.tm').read_bytes()).hexdigest();assert sha=='17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13'
result=dict(status='PASS',canonical_sha256=sha,working_states=245,binary_rows=490,renumbering_exact=True,unchanged_inherited_macro_support_rows=len(f.P),source_leaf_order_and_operands_exact=True,guarded_cases=case_count,symbolic_rules=rules,minimum_literal_steps=minimum,nonhalting_successors_normalized=normalized,gap_increments=dict(deltas),maximum_depth=max(map(len,leaves)),maximum_zero_run=max(len(x)for p in leaves for x in p.split('1')),failures=failures,seconds=time.monotonic()-began,scope='Universal affine instruction replay and finite pointer normalization relative to the supplied source sites, using the previously recovered baseline engine. Source calibration and exact finite blank boot are separately audited.')
(R/'audit245_runtime_independent.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
