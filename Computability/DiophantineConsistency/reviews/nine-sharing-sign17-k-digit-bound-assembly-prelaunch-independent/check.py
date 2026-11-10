#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-digit-bound-assembly-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p/'run.py')=='212a6b70fb55a36739e774952b4206c9119ef8864c9323f8efd316550abc13bf' and sha(p/'source-manifest.json')=='93cd9f0798ea4731df09378979cd189881081004b6738227dff3f473c19a77f2'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign17KDigitBoundAssembly.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign17KDigitBoundAssembly' and e['imports']==['DiophantineConsistency.Sign17KDigitBoundProbe']+['DiophantineConsistency.Sign17KDigitBoundBlock%02d'%i for i in range(1,15)] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='bfd26e2230b9039c406ec73c51a9aed5d69877d678b0ae325ba85356261605b3' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for x in ('theorem coefficients_bound (i : Fin 986)', 'Sign17KDigitBoundProbe.first_block_bound', 'Sign17KDigitBoundProbe.tail_block_bound', 'Sign17KDigitBoundProbe.control_block_bound', 'theorem actual_digits_bound', 'Sign17KDigitBoundProbe.stream_bound', 'coefficients_bound d hd'):assert x in s
for i in range(1,15):assert s.count(f'Sign17KDigitBoundBlock{i:02}.bound')==1
sizes=[96]+[96+64*i for i in range(1,14)]+[942];assert sum([32]+[64]*14+[14]+[44])==986
for size in sizes:assert f'h{size} : ∀ i : Fin {size}' in s
for f in ('nine-sharing-sign17-k-digit-bound-blocks-terminal-independent','nine-sharing-sign17-k-digit-bound-probe-retry-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
states=[]
for stem,dir in [('nine-sharing-sign17-k-digit-bound-blocks-check','/tmp/nine-sharing-sign17-k-digit-bound-blocks-20261110'),('nine-sharing-sign17-k-digit-bound-probe-retry-check','/tmp/nine-sharing-sign17-k-digit-bound-probe-retry-20261110')]:
 st=json.loads((root/'research'/stem/'attempt01/state.json').read_text());assert st['status']=='PASS';base=Path(dir);m={str(Path(k).relative_to(base/'lib')):v for k,v in st['overlay_links'].items()};states.append((st,base,m))
a,b=states;overlap=set(a[2])&set(b[2]);assert len(overlap)==1188 and all(a[2][k]==b[2][k] for k in overlap);init=a[0]['rows'][0]['dependencies']['Init'];assert all(row['dependencies']['Init']==init for st,_,_ in states for row in st['rows'])
for st,base,_ in states:
 for row in st['rows']:
  q=base/'lib/DiophantineConsistency'/(row['module']+'.olean');assert q.is_file() and sha(q)==row['object_sha256']
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','provider_overlay_overlap':len(overlap),'scope':'proposed all-coefficient and stream bounds; no byte/file theorem'},indent=2))
