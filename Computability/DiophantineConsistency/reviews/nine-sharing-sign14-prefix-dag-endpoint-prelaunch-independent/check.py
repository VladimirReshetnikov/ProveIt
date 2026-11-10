#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-prefix-dag-endpoint-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='ef7856801fc25a2b71069d40370cb6cb6641499ea6f32a5695b9a7cf4a7ba7f3' and sha(p/'provider-survey.py')=='ae817a1110660d5ee98638c4bf18e9c6b0ab6ffe36f90cf8872ee94a252ad7b6' and sha(p/'source-manifest.json')=='a588766196f03dfd3e83a7aa82d14dec2c72cea0e0b9cd60652f17c5780c1ccd'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14PrefixDagEndpoint.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14PrefixDagEndpoint' and e['imports']==['DiophantineConsistency.Sign14PrefixDagDegree','DiophantineConsistency.Sign14DirectNoAliasTranslated'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('theorem native_equivalence : nativeTheory ⊢','theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢','theorem standard_translated_equivalence : IPRAStandardTheory.standardTheory ⊢','IPRAExpressionNative.nativeNoZero expression','rw [expression_eq]','Sign14DirectNoAlias.native_equivalence','Sign14DirectNoAlias.standard_equivalence','Sign14DirectNoAlias.standard_translated_equivalence'):assert t in s
assert s.count('rw [expression_eq]')==3
for f in ('nine-sharing-sign14-prefix-dag-degree-retry01-terminal-independent','nine-sharing-sign14-endpoint-terminal-independent','nine-sharing-sign14-prefix-dag-degree-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider-survey.py')],capture_output=True,text=True,check=True,timeout=180);v=json.loads(x.stdout);assert not x.stderr and v['status']=='PASS' and v['overlap_count']==1099 and len(v['extra'])==601
own={'Sign14DirectNoAliasNative','Sign14DirectNoAliasStandard','Sign14DirectNoAliasTranslated'};assert set(v['own'])==own
base=Path('/tmp/nine-sharing-sign14-prefix-dag-degree-retry01-check-20261110/lib');states=['nine-sharing-sign14-endpoint-check','nine-sharing-sign14-concrete-polynomial-bridge-check','nine-sharing-sign15-concrete-polynomial-bridge-check','nine-sharing-sign14-expression-equivalence-check','nine-sharing-sign14-current-iff-check','nine-sharing-sign14-expression-eval-check'];checked=[]
for stem in states:
 st=json.loads((root/'research'/stem/'attempt01/state.json').read_text());assert st['status']=='PASS'
 for row in st['rows']:
  for mod,d in row['dependencies'].items():
   if mod=='Init':continue
   rel=mod.replace('.','/')+'.olean';name=mod.split('.')[-1];found=v['own'].get(name) if name in own else v['extra'].get(rel)
   if found is None:
    z=base/rel
    assert z.is_file(), (row['module'],mod,'missing from client base/extra/own')
    found={'realpath':str(z.resolve()),'sha256':sha(z)}
   assert found['realpath']==d['realpath'] and found['sha256']==d['sha256'],(row['module'],mod);checked.append((row['module'],mod))
assert len(checked)>=15 and any(a=='Sign14DirectNoAliasTranslated' and b.endswith('Sign14DirectNoAliasStandard') for a,b in checked)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'exact provider local object closure' in r and 'final producer local binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','own':sorted(own),'captured_direct_edges':len(checked),'overlaps':1099,'extra':601,'scope':'conditional on Lean, symbolic fragment-DAG endpoint transfer; original-file/JSON/PDF external, not full transitive trace'},indent=2))
