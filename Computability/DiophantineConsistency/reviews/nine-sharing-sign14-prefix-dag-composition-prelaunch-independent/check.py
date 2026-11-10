#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-prefix-dag-composition-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='598cda754c73e5fd5acc03af2e6d51f54b44930f48f41ca74729c15f39983070' and sha(p/'source-manifest.json')=='6324e437e9de7b54f2c9302801ff4a638c76431da371f45e93a6f2b1efa2ca5d'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==20
sources={}
for i,e in enumerate(rows):
 n=e['module'].split('.')[-1];q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
 prev='Sign14PrefixCodeRow04' if i==0 else rows[i-1]['module'].split('.')[-1];assert e['imports']==['DiophantineConsistency.'+prev];sources[n]=s
m=json.loads((root/'research/nine-sharing-sign14-prefix-dag-fragments/manifest.json').read_text());assert len(m['fragments'])==29 and len(m['shared'])==44 and len(m['rows'])==5
def encode_term(text):
 toks=re.findall(r'Code\.(?:var|port|one|two|three|four|add|sub|mul)|\d+|[()]',text);i=0
 def rec():
  nonlocal i
  x=toks[i];i+=1
  if x=='(':v=rec();assert toks[i]==')';i+=1;return v
  if x in ('Code.add','Code.sub','Code.mul'):return {'Code.add':'+','Code.sub':'-','Code.mul':'*'}[x]+rec()+rec()
  if x in ('Code.var','Code.port'):
   n=int(toks[i]);i+=1;return chr(97+n) if x=='Code.var' else 'BKCF'[n]
  return {'Code.one':'1','Code.two':'2','Code.three':'3','Code.four':'4'}[x]
 v=rec();assert i==len(toks);return v.encode()
for i,e in enumerate(m['fragments']):
 name=f'fragment{i:03}';q=p/'src/DiophantineConsistency'/(name+'.prefix');orig=root/'research/nine-sharing-sign14-prefix-dag-fragments'/(name+'.prefix');assert sha(q)==sha(orig)==e['sha256'] and len(q.read_bytes())==e['length'];s=sources[f'Sign14PrefixDagFragments{i//5:02}'];assert f'def {name} : List Char := (include_str "{name}.prefix").toList' in s
 match=re.search(r'^theorem '+name+r'_eq : '+name+r' = encode \((.+)\) := by rfl$',s,re.M);assert match and encode_term(match.group(1))==q.read_bytes();assert f'#print axioms DiophantineConsistency.Sign14PrefixDag.{name}_eq' in s
def render(node):
 if node[0]=='frag':return f'fragment{node[1]:03}'
 if node[0]=='ref':return f'shared{node[1]:02}Bytes'
 return f"('{node[1]}' :: ({render(node[2])} ++ {render(node[3])}))"
def deps(node):
 if node[0]=='frag':return [f'fragment{node[1]:03}_eq']
 if node[0]=='ref':return [f'shared{node[1]:02}Bytes_eq']
 return deps(node[2])+deps(node[3])
for kind,count in [('shared',44),('row',5)]:
 for i,node in enumerate(m['shared' if kind=='shared' else 'rows']):
  ident=f'{kind}{i:02}';s=sources[f'Sign14PrefixDagShared{i//5:02}' if kind=='shared' else f'Sign14PrefixDagRow{i:02}'];assert f'def {ident}Bytes : List Char := {render(node)}' in s and f'theorem {ident}Bytes_eq : {ident}Bytes = encode Sign14PrefixCode.{ident} := by' in s
  ds=list(dict.fromkeys(deps(node)));assert f"simp only [{', '.join(ds)}] <;> rfl" in s and f'#print axioms DiophantineConsistency.Sign14PrefixDag.{ident}Bytes_eq' in s
for f in ('nine-sharing-sign14-prefix-dag-fragments-independent','nine-sharing-sign14-prefix-code-terminal-independent','nine-sharing-sign14-prefix-dag-lemma-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and all(f'fragment drift fragment{i:03}.prefix' in r for i in range(29))
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':20,'fragments':29,'shared':44,'rows':5,'scope':'compositional separately embedded fragment DAG encodings; original file/JSON/PDF relation external'},indent=2))
