#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-prefix-code-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='7ecf604bd541f087e5a50d7b4034504802e1d9cd78d4a92c4365ba5be6efdf74' and sha(p/'source-manifest.json')=='097ebc0d72e897583b34930d2cc33a1563a9bd6b984582e013ecf6394ed5567a'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==14
for idx,e in enumerate(rows):
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
 expected='Sign14PrefixReflection' if idx==0 else rows[idx-1]['module'].split('.')[-1];assert e['imports']==['DiophantineConsistency.'+expected]
def codeparse(text):
 t=re.findall(r'Code\.(?:var|port|one|two|three|four|add|sub|mul)|shared\d\d|\d+|[()]',text);i=0
 def rec():
  nonlocal i
  x=t[i];i+=1
  if x=='(': v=rec();assert t[i]==')';i+=1;return v
  if x in ('Code.add','Code.sub','Code.mul'):return (x[5:],rec(),rec())
  if x in ('Code.var','Code.port'):n=t[i];i+=1;return (x[5:],int(n))
  if x.startswith('shared'):return ('shared',int(x[6:]))
  assert x in ('Code.one','Code.two','Code.three','Code.four');return ('num',{'Code.one':1,'Code.two':2,'Code.three':3,'Code.four':4}[x])
 v=rec();assert i==len(t);return v
def stagedparse(text):
 text=re.sub(r'\(Expr\.constant \(p (\d+)\)\)',r'P\1',text);text=re.sub(r'\(Expr\.constant \((\d+) : ℤ\)\)',r'N\1',text);text=re.sub(r'\(Expr\.var (\d+)\)',r'V\1',text);text=re.sub(r'\(shared(\d\d) p\)',r'S\1',text);t=re.findall(r'[PNVS]\d+|[()+*\-]',text);i=0
 def rec():
  nonlocal i
  x=t[i];i+=1
  if x=='(':
   l=rec()
   if t[i]==')':i+=1;return l
   op=t[i];i+=1;r=rec();assert t[i]==')';i+=1;return ({'+':'add','-':'sub','*':'mul'}[op],l,r)
  return ({'P':'port','N':'num','V':'var','S':'shared'}[x[0]],int(x[1:]))
 v=rec();assert i==len(t);return v
staged={x['module'].split('.')[-1]:x for x in json.loads((root/'research/nine-sharing-sign14-staged-syntax-check/source-manifest.json').read_text())['rows']}
for name,count,blocks in [('shared',44,9),('row',5,5)]:
 found=[]
 for k in range(blocks):
  cn=f'Sign14PrefixCodeShared{k:02}' if name=='shared' else f'Sign14PrefixCodeRow{k:02}';ln=f'SharingSeed14Shared{k:02}' if name=='shared' else f'SharingSeed14Row{k:02}'
  cs=(p/'src/DiophantineConsistency'/(cn+'.lean')).read_text();lp=root/'research/nine-sharing-sign14-staged-syntax-draft'/(ln+'.lean');assert sha(lp)==staged[ln]['source_sha256'];ls=lp.read_text()
  cd=dict(re.findall(r'^def ('+name+r'\d\d) : Code := (.+)$',cs,re.M));ld=dict(re.findall(r'^def ('+name+r'\d\d) \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n  (.+)$',ls,re.M));assert cd.keys()==ld.keys()
  for key in cd:
   assert codeparse(cd[key])==stagedparse(ld[key]),key
   assert f'theorem {key}_interpret (p : Fin 4 → ℤ) :\n    interpret p {key} = SharingSeed14Degree124.{key} p := by' in cs
   assert f'#print axioms DiophantineConsistency.Sign14PrefixCode.{key}_interpret' in cs;found.append(int(key[len(name):]))
 assert sorted(found)==list(range(count))
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-staged-syntax-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
c=root/'reviews/nine-sharing-sign14-prefix-reflection-retry03-terminal-independent/check.py';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':14,'shared':44,'rows':5,'scope':'interpretation of symbolic code vs staged syntax, conditional on Lean; no long-row byte/JSON/PDF theorem'},indent=2))
