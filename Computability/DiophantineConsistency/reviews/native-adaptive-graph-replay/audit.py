"""Independent literal syntax audit; reads JSON data and Lean text only.
No project imports, Lean invocation, coefficient construction or degree claim.
"""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2]
GRAPH=D/'candidates/free-j-polarized-positive/source/positive/p13_free_J.json'
SOURCE=D/'Lean/DiophantineConsistency/NativeAdaptiveGraph.lean'
CHECKS=D/'Lean/DiophantineConsistency/NativeAdaptiveGraphChecks.lean'
def require(b,m):
 if not b:raise RuntimeError(m)
def pin(p):
 b=Path(p).read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
require(pin(GRAPH)['sha256']=='a6c378ffe706da6ccb17250c31183b0cbff7bdd2c21b85cf0fc393a73bd987b8','inert graph pin')
g=json.loads(GRAPH.read_text());source=SOURCE.read_text()
inputs=['J','F','alpha','f','i','T','X','Y','r','eta','zeta','u','gamma']
ports=['beta','K0','MC','MF']
require(g['witnesses']==inputs and g['fixed_numerals']==ports and g['output']=='P13','input/port/output contract')
fields=['qm','q','q3','C','E','k','c','a','H','delta','ell','U','Bt','rank','V','y','I','Z','M','W','Dstar','A0','A1','Fs','Fa','out']
alias={'delta':'Delta','rank':'R','y':'g78','out':'P13'}
expected_fields=[(f,alias.get(f,f)) for f in fields]
def region(s,a,b):
 require(s.count(a)==s.count(b)==1,'unique boundary')
 return s.split(a)[1].split(b)[0]
def parse(s):
 als=region(s,'-- BEGIN INPUT ALIASES','-- END INPUT ALIASES')
 aliases=[]
 for l in als.splitlines():
  if not l.strip():continue
  m=re.fullmatch(r'\s*let (\w+) := (x|ports) (\d+)\s*',l);require(m is not None,'alias grammar')
  aliases.append((m[1],m[2],int(m[3])))
 body=region(s,'-- BEGIN LITERAL GRAPH','-- END LITERAL GRAPH')
 rows=[];known=set(inputs+ports)
 for l in body.splitlines():
  if not l.strip():continue
  m=re.fullmatch(r'\s*let (\w+) := (\w+) ([*+\-]) (\w+)\s*',l);require(m is not None,'gate grammar')
  name,left,op,right=m.groups()
  def arg(t):
   if t.isdecimal():return int(t)
   require(t in known,'defined operand '+t);return t
  a,b=arg(left),arg(right);require(name not in known,'unique producer')
  rows.append([name,op,a,b]);known.add(name)
 tail=s.split('-- END LITERAL GRAPH')[1].split('\ndef value')[0].strip()
 require(tail.startswith('{ ') and tail.endswith(' }'),'record grammar')
 ret=[]
 for term in tail[2:-2].split(', '):
  m=re.fullmatch(r'(\w+):=(\w+)',term);require(m is not None,'field grammar');ret.append(m.groups())
 require(re.search(r'def value \(ports : Fin 4 → A\) \(x : Fin 13 → A\) : A := \(core ports x\)\.out',s) is not None,'actual output projection')
 return aliases,rows,ret
want_alias=[(n,'x',i) for i,n in enumerate(inputs)]+[(n,'ports',i) for i,n in enumerate(ports)]
def check(s):
 a,r,f=parse(s)
 require(a==want_alias,'actual aliases')
 require(r==g['source'],'every ordered literal gate')
 require(f==expected_fields,'actual cut/output field binding')
 return a,r,f
aliases,rows,ret=check(source)
require(len(rows)==88,'delivered gate count')
mutations=[]
for i,(name,op,left,right) in enumerate(rows):
 old=f'  let {name} := {left} {op} {right}'
 newop={'+':'-','-':'+','*':'+'}[op]
 mutations.append((f'gate-{i}-operator',source.replace(old,f'  let {name} := {left} {newop} {right}',1)))
 newleft=0 if left!=0 else 1
 mutations.append((f'gate-{i}-operand',source.replace(old,f'  let {name} := {newleft} {op} {right}',1)))
for name,kind,i in aliases:
 old=f'  let {name} := {kind} {i}'
 j=(i+1)%(13 if kind=='x' else 4)
 mutations.append((f'alias-{name}',source.replace(old,f'  let {name} := {kind} {j}',1)))
for name,producer in ret:
 replacement='qm' if producer!='qm' else 'q'
 mutations.append((f'field-{name}',source.replace(name+':='+producer,name+':='+replacement,1)))
mutations.append(('output-projection',source.replace('(core ports x).out','(core ports x).A0',1)))
rejected=[]
for label,bad in mutations:
 require(bad!=source,'actual mutation '+label)
 try:check(bad)
 except RuntimeError:rejected.append(label)
 else:raise RuntimeError('undetected '+label)
result=dict(status='PASS',scope='Exact literal JSON-to-Lean aliases, ordered binary gates and cut/output projections only. No degree, complete current-port, optimality, converse or ConZFC metric claim.',
 graph=pin(GRAPH),source=pin(SOURCE),checks=pin(CHECKS),auditor=pin(__file__),
 aliases=aliases,rows=rows,fields=ret,rejected_mutations=rejected,
 counts=dict(inputs=13,ports=4,ordered_gates=len(rows),cut_fields=len(ret),actual_corruptions_rejected=len(rejected)))
out=Path(__file__).with_name('BINDING.json');out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='PASS',counts=result['counts'],certificate=pin(out)),indent=2))
