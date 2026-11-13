#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-coefficient-decompose-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='d8edd107dc6a17482d54c4e8b9916caf82600f7f340cdfa31b7b2fff22129895' and sha(p/'source-manifest.json')=='9147cbcdf18bdc37a19fbdbe326add295c62b58d1683fe9c07fbcc1c24a08c4f'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign17KCoefficientDecompose';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign17KStreamBump'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='a7f29a260aeae51f92705faf2c7433915069be82892c8ff647e78d1252d875e6' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
fwd=s.split('theorem coefficient_list :',1)[1].split(':= by',1)[0];rev=s.split('theorem coefficient_list_reversed :',1)[1].split(':= by',1)[0];parts=lambda z:re.findall(r'List\.ofFn (Sign17K(?:TileCoefficients\d\d|ControlBlocks))\.literal',z)
expected=[f'Sign17KTileCoefficients{i:02}' for i in range(16)]+['Sign17KControlBlocks'];assert parts(fwd)==expected and parts(rev)==expected[::-1] and rev.count('.reverse')==18 and 'List.ofFn (Fin.append a b) = List.ofFn a ++ List.ofFn b' in s
up=root/'research/nine-sharing-sign17-k-literal-coefficient-union-retry-check/src/DiophantineConsistency'
for k in range(8):
 size=[96,224,352,480,608,736,864,942][k];t=(up/f'Sign17KTileCoeffUnion{size}.lean').read_text();assert f'Sign17KTileCoefficients{2*k:02}.literal' in t and f'Sign17KTileCoefficients{2*k+1:02}.literal' in t
assert 'Sign17KTileCoeffUnion942.literal Sign17KControlBlocks.literal' in (up/'Sign17KLiteralCoefficients.lean').read_text()
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-stream-bump-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
prior=json.loads((root/'research/nine-sharing-sign17-k-stream-bump-check/attempt01/state.json').read_text());assert prior['status']=='PASS';obj=Path('/tmp/nine-sharing-sign17-k-stream-bump-20261110/lib/DiophantineConsistency/Sign17KStreamBump.olean');assert sha(obj)==prior['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic append and symbolic coefficient vector forward/reverse decomposition; fixture/file linkage separate'},indent=2))
