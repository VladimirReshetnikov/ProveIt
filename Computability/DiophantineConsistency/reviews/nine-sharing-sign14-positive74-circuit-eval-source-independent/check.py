#!/usr/bin/env python3
import hashlib,json,random,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-positive74-circuit-eval-draft';src=p/'Sign14Positive74CircuitEval.lean';s=src.read_text();sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert re.findall(r'^import (\S+)$',s,re.M)==['DiophantineConsistency.Sign14Positive74Circuit'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('| .var i => .var i','| .port i => .constant (p i)','| .lit z => .constant z','| .reg j => s.getD j (.constant 0)','s ++ [symOp g.op (symArg p s g.left) (symArg p s g.right)]','(gates.foldl (symStep p) []).getD 73 (.constant 0)','circuitExpr p = Sign14Positive74.expression p','| .var i => v i','| .port i => (p i : R)','| .lit z => (z : R)','| .reg j => s.getD j 0','s ++ [numOp g.op (numArg p v s g.left) (numArg p v s g.right)]','(gates.foldl (numStep p v) []).getD 73 0','circuitEval p v = (Sign14Positive74.expression p).evalRing v'):assert z in s
assert s.count('| .add, a, b => a + b')==2 and s.count('| .sub, a, b => a - b')==2 and s.count('| .mul, a, b => a * b')==2
circuit=(root/'research/nine-sharing-sign14-positive74-circuit-draft/Sign14Positive74Circuit.lean').read_text();body=circuit.split('def gates : List Gate := [',1)[1].split(']',1)[0];gs=re.findall(r'⟨\.(add|sub|mul), \.(var|port|lit|reg) (\d+), \.(var|port|lit|reg) (\d+)⟩',body);assert len(gs)==74
ext=json.loads((root/'research/nine-sharing-sign14-positive74-candidate/seed.json').read_text());names=['beta','K0','MC','MF'];P=1000000007;gen=random.Random(79248)
def ev(t,v,p):
 op=t[0]
 if op=='var':return v[t[1]-1]
 if op=='port':return p[names.index(t[1])]
 if op=='num':return t[1]%P
 a,b=ev(t[1],v,p),ev(t[2],v,p)
 return {'add':lambda:(a+b)%P,'sub':lambda:(a-b)%P,'mul':lambda:a*b%P}[op]()
for _ in range(16):
 v=[gen.randrange(P) for _ in range(14)];p0=[gen.randrange(P) for _ in range(4)];regs=[]
 def get(ty,j):return {'reg':lambda:regs[j],'var':lambda:v[j],'port':lambda:p0[j],'lit':lambda:j%P}[ty]()
 for op,a,i,b,j in gs:
  A,B=get(a,int(i)),get(b,int(j));regs.append({'add':lambda:(A+B)%P,'sub':lambda:(A-B)%P,'mul':lambda:A*B%P}[op]())
 assert regs[-1]==sum(ev(row['expr'],v,p0)**2 for row in ext['residuals'])%P
for f in ('nine-sharing-sign14-positive74-circuit-source-independent','nine-sharing-sign14-positive74-circuit-retry01-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_SOURCE_AUDIT','source_sha256':sha(src),'scope':'append-once symbolic/ring evaluator structurally matches gate semantics; both proposed rfl equalities and Lean compilation untested; external file comparison separate'},indent=2))
