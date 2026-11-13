#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-byte-binding-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='91d34ac30e7128cd9c2f4c8e6fd1952b1bedb4bac7b8a06e70dd7efd2d000b4d' and sha(p/'source-manifest.json')=='1b7cdfa17c7553f4953e75f7d1dcda701c9ae7a42e664f853e23f01115595d74'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign17KByteBinding';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();imports=[f'DiophantineConsistency.Sign17KStreamCompare{i:02}' for i in range(8)];assert e['module']=='DiophantineConsistency.'+n and e['imports']==imports and sha(q)==sha(repo/e['source'])==e['source_sha256']=='8aaaea50d8fe5c5eaaf32b06a352c006f04e25afef3140946a30030ed2933552' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==imports and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert 'actualDigits.drop 2048 = []' in s and 'Sign17KByteCompose.digitList.drop 2048 = []' in s and 'theorem fixture_digits : actualDigits = Sign17KByteCompose.digitList' in s and 'theorem K_bytes : Nat.ofDigits 256 Sign17KByteCompose.byteList = K' in s
for i in range(8):
 offset=i*256;assert f'have h{i} : actualDigits.drop {offset} = Sign17KByteCompose.digitList.drop {offset}' in s and f'Sign17KStreamCompare{i:02}.chunk' in s and f'using h{i+1}' in s
assert 'rw [actual_ends, fixture_ends]' in s and 'List.take_append_drop n xs' in s and 'List.take_append_drop n ys' in s and 'Sign17KByteCompose.fixture_value.symm' in s and 'Sign17KStreamExplicit.digits_explicit' in s and 'Nat.ofDigits_digits radix K' in s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-stream-compare-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
prior=json.loads((root/'research/nine-sharing-sign17-k-stream-compare-check/attempt01/state.json').read_text());assert prior['status']=='PASS' and len(prior['rows'])==8
for row in prior['rows']:assert sha(Path('/tmp/nine-sharing-sign17-k-stream-compare-20261110/lib/DiophantineConsistency')/(row['module']+'.olean'))==row['object_sha256']
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed symbolic K equality to in-Lean byte-list decoding; no external file theorem'},indent=2))
