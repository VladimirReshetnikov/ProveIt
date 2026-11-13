#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-positive74-lean-draft';seed=root/'research/nine-sharing-sign14-positive74-candidate/seed.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(seed)=='10d4e4739d5e6657cc43ea71792c363bf0e292fd65f0cf11372fd20b4b5de15b' and sha(p/'generate.py')=='948f01ba49207c9c420d2745c061f672776ba435871b28b490ceab905e6a3398' and sha(p/'result.json')=='3f559e75dfeeda692436cdd60f6430c367d837deb8b09299de537d1063e4f0f1';expected=['5c2e89995e6671f1373af5cf5760057f1f1f3e452bf27a0c1bba772750b8bbcf','05354596346cb3b858c77dda9ca4d2d57461fd44c9ab885f7b34de01dfaf2c3f','773ed6488e117bf85881bc9436264c47de450d4510bd92e9b44e241972be4c7d','b98932a88f5328d3f2728b6ba9919d8bae4fb152ea92cf70a2c4bb330f79de73','901110aaf772532e351984af50efaca5fb774a00102c3e03e24ad184afeae48e','20376e2d79d1ae8ea0673af90c2a9bcfefb458cc245d4e0c3609a6143016cb5b','5dcb20a862137769ba66ae21cb5300dc72114b29abd725e8088f97c129ed1ff5','77d6a324074d36e8a214e72b13897c3bac26934eb5c00ec14a5704a9fbdbc31d','27ae3ca71e9cc1732e9f2fcba05a90a4cdab3c8f6aaadf2d0d06fd447522fd9f'];nodes=[];ports=['beta','K0','MC','MF']
def atom(x):
 if m:=re.fullmatch(r'g(\d\d) p',x):i=int(m.group(1));assert i<len(nodes);return nodes[i]
 if m:=re.fullmatch(r'Expr.var (\d+)',x):i=int(m.group(1));assert 0<=i<14;return ('var',i+1)
 if m:=re.fullmatch(r'Expr.constant \(p (\d+)\)',x):i=int(m.group(1));assert 0<=i<4;return ('port',ports[i])
 if m:=re.fullmatch(r'Expr.constant (\d+)',x):return ('num',int(m.group(1)))
 raise AssertionError(x)
for i in range(9):
 q=p/f'Sign14Positive74Nodes{i:02}.lean';assert sha(q)==expected[i];s=q.read_text();imports=re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M);assert imports==[('DiophantineConsistency.Sign14Optimized86Expression' if i==0 else f'DiophantineConsistency.Sign14Positive74Nodes{i-1:02}')]
 assert not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
 matches=re.findall(r'^def g(\d\d) \(p : Fin 4 → ℤ\) : Expr \(Fin 14\) := (.+)$',s,re.M);assert len(matches)==(8 if i<8 else 1)
 for label,expr in matches:
  assert int(label)==len(nodes);m=re.fullmatch(r'\((.*?)\) ([+*\-]) \((.*?)\)',expr);assert m,expr;nodes.append(({'+':'add','-':'sub','*':'mul'}[m.group(2)],atom(m.group(1)),atom(m.group(3))))
assert len(nodes)==65 and len(set(nodes))==65
q=p/'Sign14Positive74Expression.lean';assert sha(q)=='520fdc20731a5a433a79fa0e167df77d0cd1cc22e67930a2c236cdd9623fe772';s=q.read_text();assert re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==['DiophantineConsistency.Sign14Positive74Nodes08'];rows=re.findall(r'^def row(\d\d) \(p : Fin 4 → ℤ\) : Expr \(Fin 14\) := \(g(\d\d) p\)$',s,re.M);assert rows==[('00','23'),('01','41'),('02','48'),('03','61'),('04','64')]
def tup(x):return tuple(tup(y) if isinstance(y,list) else y for y in x)
candidate=json.loads(seed.read_text());assert all(nodes[int(g)]==tup(candidate['residuals'][int(i)]['expr']) for i,g in rows)
body=' '.join(re.search(r'def expression \(p : Fin 4 → ℤ\) : Expr \(Fin 14\) :=\n(.*?)\n\nend ',s,re.S).group(1).split());assert body=='row00 p * row00 p + row01 p * row01 p + row02 p * row02 p + row03 p * row03 p + row04 p * row04 p'
visited=set()
def visit(x):
 if x[0] in ('add','sub','mul') and x not in visited:visited.add(x);visit(x[1]);visit(x[2])
for _,g in rows:visit(nodes[int(g)])
assert visited==set(nodes)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-candidate-independent/check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_SOURCE_STRUCTURE','node_count':len(nodes),'roots':[int(g) for _,g in rows],'scope':'source-only positive-input DAG matches external AST; no checked Lean coordinate transport or file theorem'},indent=2))
