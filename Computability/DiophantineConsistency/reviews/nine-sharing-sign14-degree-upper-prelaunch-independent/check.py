#!/usr/bin/env python3
"""Independently compute structural degrees from staged Lean source; no Lean run."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-degree-upper-check';base=root/'research/nine-sharing-sign14-staged-syntax-check/src/DiophantineConsistency';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='e2ea07c58678851c104564609722c7dc092c11d026f7428de158ba23b6a7be97' and sha(p/'source-manifest.json')=='e3a22e4e516ea349b1ff13506217f9e757b0ad45380bee922ee9e864d0fef629' and sha(p/'framework-survey.py')=='7ef01d6d527341f5891f17361e885d0883ac8e13e192778f340ea9027198660b'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==18;seen=set()
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');text=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',text,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',text)
 assert all(d in seen for d in e['imports'] if d in [x['module'] for x in rows]);seen.add(e['module'])
lex=re.compile(r'\s*(Expr\.constant|Expr\.var|shared[0-9]{2}|[0-9]+|p|ℤ|[()+*:\-])');degrees={}
def structural_degree(line):
 tokens=[];pos=0
 while pos<len(line):
  m=lex.match(line,pos);assert m,(pos,line[pos:pos+30]);tokens.append(m.group(1));pos=m.end()
 i=0
 def take(expect=None):
  nonlocal i
  x=tokens[i];i+=1
  if expect is not None:assert x==expect
  return x
 def term():
  take('(');t=tokens[i]
  if t.startswith('shared'):
   name=take();take('p');take(')');return ('degree ('+name+' p)',degrees[name])
  if t=='Expr.var':
   take();v=int(take());assert 1<=v<=14;take(')');return ('1',1)
  if t=='Expr.constant':
   take();take('(');v=take()
   if v=='p':assert 0<=int(take())<4
   else:int(v);take(':');take('ℤ')
   take(')');take(')');return ('0',0)
  a,da=term();op=take();b,db=term();take(')');assert op in ('+','-','*');return (('('+a+' + '+b+')') if op=='*' else ('max ('+a+') ('+b+')'), da+db if op=='*' else max(da,db))
 out=term();assert i==len(tokens);return out
for i in range(44):
 name=f'shared{i:02}';s=(base/f'SharingSeed14Shared{i//5:02}.lean').read_text();m=re.search(r'^def '+name+r' \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n  (.*)$',s,re.M);assert m;form,degrees[name]=structural_degree(m[1]);proof=(p/f'src/DiophantineConsistency/Sign14SharedDegree{i//5:02}.lean').read_text();assert f'theorem {name}_degree (p : Fin 4 → ℤ) : degree ({name} p) ≤ {degrees[name]} := by' in proof and f'  change {form} ≤ {degrees[name]}' in proof
rowdegrees=[]
for i in range(5):
 name=f'row{i:02}';s=(base/f'SharingSeed14Row{i:02}.lean').read_text();m=re.search(r'^def '+name+r' \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n  (.*)$',s,re.M);assert m;form,d=structural_degree(m[1]);rowdegrees.append(d);proof=(p/f'src/DiophantineConsistency/Sign14RowDegree{i:02}.lean').read_text();assert f'theorem {name}_degree (p : Fin 4 → ℤ) : degree ({name} p) ≤ {d} := by' in proof and f'  change {form} ≤ {d}' in proof
assert rowdegrees==[22,22,2,62,46]
res=(p/'src/DiophantineConsistency/Sign14DegreeResiduals.lean').read_text();comp=(p/'src/DiophantineConsistency/Sign14DegreeCompose.lean').read_text();struct=(p/'src/DiophantineConsistency/Sign14DegreeStructural.lean').read_text()
assert all(f'row{i:02}_degree p' in res for i in range(5)) and 'degree e ≤ 62' in res and 'degree (row00 p) ≤ 62' in res
assert all(t in comp for t in ('theorem seed_degree_le','theorem expression_degree_le','theorem expression_polynomial_degree_le','theorem current_polynomial_degree_le','≤ 124','removeInput_degree_le','polynomial_degree_le')) and 'sum_squares_degree_le' in struct and 'degree_subst_le' in struct
check=root/'reviews/nine-sharing-sign14-expression-eval-terminal-independent/check.py';assert sha(check)=='4e4e42a17bfdaca569da35ea60752aa257dae9622fb403b3df7b1257bc87b3ae';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'outer-result.json' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':18,'shared_nodes':44,'row_degrees':rowdegrees,'scope':'proposed symbolic arbitrary-port totalDegree ≤124; no Lean theorem or external binding'},indent=2))
