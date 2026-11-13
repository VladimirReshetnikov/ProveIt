#!/usr/bin/env python3
"""Independent structural AC graph-vs-source comparison; no Lean execution."""
import ast,collections,gzip,hashlib,json,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2];p=r/'research/normalized106-graph-syntax-binding';g=r/'research/fourteen-normalized-product106/polynomial.json';stages=r/'reviews/nine-variable-ipra-equal-length-stages-77-81-overlap/observations/stages-077-081/author';src=stages/'078/ModelCarrierSyntax.lean'
sha=lambda b:hashlib.sha256(b).hexdigest()
pins={p/'check.py':'3d36c67101606c5d0d8b1e47c0c00fa06e5eceb0370a1baa4b086b5017128c65',p/'result.json':'2ea08d98108465c1d1e48e1296e32a2f15aceebadae682231c00b87e8c00d552',p/'outer-terminal.json':'ede299f578e43719e4e673307fd95b7626a05298b8e96e717f25746ec03234f3',g:'0485cd1e884b918d766261b1780be117238f0813a965c6d8ae4d805176a5f6e1',src:'8d40486fd9adf151e905977c01cbc1a2aa7142fbd02c5e4293906c6865e5a43a'}
for f,h in pins.items():
 if sha(f.read_bytes())!=h:raise ValueError(('pin',str(f)))
graph=json.loads(g.read_bytes()); rows=graph['source']; names=graph['witnesses'];ports=graph['fixed_numerals']
if len(rows)!=67 or collections.Counter(x[1] for x in rows)!={'*':38,'+':16,'-':13} or names!=['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma'] or ports!=['beta','K0','MC','MF']:raise ValueError('graph inventory')
# Canonical DAG independently flattens only + and *, retaining ordered subtraction.
class Algebra:
 def __init__(self):self.memo={};self.nodes=[]
 def node(self,k):
  if k not in self.memo:self.memo[k]=len(self.nodes);self.nodes.append(k)
  return self.memo[k]
 def leaf(self,x):return self.node(('leaf',str(x)))
 def op(self,op,a,b):
  if op=='-':return self.node(('-',a,b))
  args=[]
  for n in (a,b):
   t=self.nodes[n];args.extend(t[1] if t[0]==op else (n,))
  return self.node((op,tuple(sorted(args))))
A=Algebra();v={n:A.leaf(n) for n in names+ports};edges={}
for n,op,x,y in rows:
 if n in v or op not in ('+','-','*'):raise ValueError('duplicate row')
 def term(t):return A.leaf(t) if isinstance(t,int) else v[t]
 v[n]=A.op(op,term(x),term(y));edges[n]=(x,y)
live=set();used=set();todo=[graph['output']]
while todo:
 n=todo.pop()
 if n in edges and n not in live:live.add(n);todo.extend(edges[n])
 elif isinstance(n,str) and n not in edges:used.add(n)
if len(live)!=67 or used!=set(names+ports):raise ValueError('liveness')
body=src.read_text().split('def expressionAt106 (p : Fin 4 → ℤ) : Expr (Fin 14) :=',1)[1].split('/-- The 66/118 polynomial:',1)[0]
# Parse the Lean let declarations independently; continuation lines attach to the last expression.
chunks=[];out=[]
for line in body.splitlines():
 t=line.strip()
 if not t:continue
 if t.startswith('let '):chunks.append(t)
 elif out:out.append(t)
 elif t.startswith('P * Q'):out.append(t)
 elif chunks:chunks[-1]+=' '+t
 else:raise ValueError('unexpected source line')
env={'port'+str(i):A.leaf(n) for i,n in enumerate(ports)}
def expr(t):
 t=re.sub(r'Expr\.constant\s*\(p\s+(\d+)\)',lambda m:'port'+m.group(1),t).replace('^','**')
 def go(x):
  if isinstance(x,ast.Name):return env[x.id]
  if isinstance(x,ast.Constant) and type(x.value) is int:return A.leaf(x.value)
  if isinstance(x,ast.BinOp):
   a=go(x.left)
   if isinstance(x.op,ast.Pow):
    if not isinstance(x.right,ast.Constant) or x.right.value not in (2,3):raise ValueError('power')
    for _ in range(x.right.value-1):a=A.op('*',a,go(x.left))
    return a
   op={ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}.get(type(x.op))
   if op is None:raise ValueError('operator')
   return A.op(op,a,go(x.right))
  raise ValueError(('syntax',ast.dump(x)))
 return go(ast.parse(t,mode='eval').body)
seen=[]
for chunk in chunks:
 m=re.fullmatch(r'let\s+(\w+)(?:\s*:\s*Expr\s*\(Fin\s+14\))?\s*:=\s*(.*)',chunk)
 if not m:raise ValueError(('let',chunk))
 name,t=m.groups()
 if name in seen:raise ValueError('duplicate let')
 seen.append(name);var=re.fullmatch(r'\.var\s+(\d+)',t)
 if var:
  i=int(var.group(1))
  if i>=len(names) or name!=names[i]:raise ValueError('witness index')
  env[name]=A.leaf(name)
 else:env[name]=expr(t)
if seen[:14]!=names:raise ValueError('witness order')
cuts={'b':'qm','q':'q','C':'C','X':'X','Y':'Y','E':'E','k':'k','ell':'ell','c':'c','a':'a','H':'H','delta':'Delta','D':'main_root','rank':'R','tau':'tau','V':'V','P':'N0','Q':'N1','W':'Nt'}
for a,b in cuts.items():
 if env[a]!=v[b]:raise ValueError(('cut',a,b))
if expr(' '.join(out))!=v[graph['output']]:raise ValueError('output mismatch')
# Reject ordered-subtraction corruption using the same exact comparator.
if A.op('-',A.leaf('x'),A.leaf('y'))==A.op('-',A.leaf('y'),A.leaf('x')):raise ValueError('subtraction accidentally commutative')
for name,meta in graph['coefficient_binding']['ports'].items():
 raw=(g.parent/'coefficients'/meta['file']).read_bytes();data=gzip.decompress(raw)
 if sha(raw)!=meta['gzip_sha256'] or sha(data)!=meta['raw_sha256'] or len(data)!=meta['raw_bytes']:raise ValueError(('port',name))
if sha((stages/'078/receipt.json').read_bytes())!='00300fc41cf787db439a99d4afe49e0d14cffd1aa4fad505a3ad18aac750e420' or sha((stages/'079/receipt.json').read_bytes())!='33f040272cf2bc0203e21521ba20d5499bb6c39adc8de02e817a2e41b334318d':raise ValueError('historical stage receipt drift')
a=json.loads((stages/'078/receipt.json').read_bytes());b=json.loads((stages/'079/receipt.json').read_bytes());wanted='9eaaefb9b4121df6d9c8f6f1c5feef1cc837fc38f51a831a005db072bdaaf900'
if a['status']!='PASS' or a['source_sha256']!=pins[src] or a['output']['sha256']!=wanted or b['status']!='PASS' or b['direct']['DiophantineConsistency.ModelCarrierSyntax']['record']['sha256']!=wanted:raise ValueError('stage 078/079 receipt linkage')
if sha(Path('/tmp/nine-ipra-guarded-author-20261102-h/lib/DiophantineConsistency/ModelCarrierSyntax.olean').read_bytes())!=wanted:raise ValueError('historical syntax object drift')
run=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120)
if run.returncode!=0 or run.stderr or run.stdout!=(p/'result.json').read_bytes():raise ValueError(('checker rerun',run.returncode,run.stderr[:200]))
t=json.loads((p/'outer-terminal.json').read_bytes())
if t['terminal_exit_code']!=0:raise ValueError('outer observation')
print(json.dumps({'status':'PASS_INDEPENDENT_STRUCTURAL_COMPARISON','rows':len(rows),'live':len(live),'cuts':len(cuts),'operation_counts':dict(collections.Counter(row[1] for row in rows)),'retained_stage_078_to_079_object_sha256':wanted,'author_checker_rerun_exit':run.returncode,'scope':'Exact source/tree comparison modulo AC; no Lean replay, numerical current-port proof or degree audit.'},sort_keys=True,indent=2))
