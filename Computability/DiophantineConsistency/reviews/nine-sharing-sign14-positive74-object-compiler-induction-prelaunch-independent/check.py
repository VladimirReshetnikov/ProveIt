#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-compiler-induction-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='f68cb1d8f5eb35a6713db0724dca5997033ccca004f2df2479f43c8dc7b59bba' and sha(p/'source-manifest.json')=='6a766dc4d9aa9b59a6120787bbf044cf65bdc347ec8924701513fe97183022c3'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectCompilerInduction';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectCompilerOps'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(h : extended nativeTheory ⊢! eqAt (compiledOpen p v) (compiledOpen q w))','Aligned v w (.add p q) (.add p\' q\')','Aligned v w (.mul p q) (.mul p\' q\')','binaryOpen addCode (compiledOpen p v) (compiledOpen q v)','binaryOpen mulCode (compiledOpen p v) (compiledOpen q v)','simpa only [compiled_add]','simpa only [compiled_mul]'):assert z in s
for f in ('nine-sharing-sign14-positive74-object-compiler-ops-retry01-terminal-independent','nine-sharing-sign14-positive74-object-function-binary-retry01-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
b=json.loads((root/'research/nine-sharing-sign14-positive74-object-compiler-ops-retry01-check/attempt01/state.json').read_text());old=json.loads((root/'research/nine-sharing-sign14-positive74-object-function-binary-retry01-check/attempt01/state.json').read_text());k='/tmp/nine-sharing-sign14-positive74-object-compiler-ops-retry01-check-20261110/lib/DiophantineConsistency/Sign14Positive74ObjectFunctionBinary.olean';v=b['overlay_links'][k];assert Path(k).resolve()==Path(v).resolve() and sha(Path(v))==old['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'conditional structural compiled-tree equality given explicit native leaf proofs'},indent=2))
