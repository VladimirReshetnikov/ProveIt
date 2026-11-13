#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-byte-compose-retry-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p/'run.py')=='eb4e79830d9151b78834648b6aaa4f17117d33fbede8fc5c7bce5c7d2491dbf5' and sha(p/'source-manifest.json')=='8989500927384eed560c50b6812460428fd73a7a5dddadd8794ca17e2d58a5c4';e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign17KByteCompose.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign17KByteCompose' and e['imports']==[f'DiophantineConsistency.Sign17KByteAlignment{i:02}' for i in range(8)] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='80f338d5b675c5192db43c8b7065c7ca7a34e0b3577cb5c1dd93d92ef4dac3e8' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for line in ('def digitBlocks :','def byteBlocks :'):
 row=next(x for x in s.splitlines() if x.startswith(line));assert [int(x) for x in re.findall(r'Sign17KByteAlignment(\d\d)\.',row)]==list(range(8))
assert [int(x) for x in re.findall(r'Sign17KByteAlignment(\d\d)\.aligned',s)]==list(range(8)) and 'theorem flatten_tail' in s and 'theorem fixture_value' in s
assert (1<<47)**8==256**47 and sum(x*(1<<47)**i for i,x in enumerate([0,0,0,0,1]))==sum(x*256**i for i,x in enumerate([0]*23+[16]))
assert 'digitBlocks.flatten ++ [0, 0, 0, 0, 1]' in s and len(re.search(r'def byteList.*?\[([^\]]+)\]',s,re.S).group(1).split(','))==24
old=(root/'research/nine-sharing-sign17-k-byte-compose-check/src/DiophantineConsistency/Sign17KByteCompose.lean').read_text()
for field in ('digitBlocks','byteBlocks'):
 prefix=f'def {field} : List (List ℕ) := ';oldline=next(x for x in old.splitlines() if x.startswith(prefix));newparts=[f'Sign17KByteAlignment{i:02}.{field}' for i in range(8)];rhs=newparts[-1]
 for part in reversed(newparts[:-1]):rhs=part+' ++ ('+rhs+')'
 old=old.replace(oldline,prefix+rhs)
assert old==s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-byte-compose-failure-independent/check.py')],capture_output=True,check=True,timeout=180)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-byte-alignment-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
prior=json.loads((root/'research/nine-sharing-sign17-k-byte-alignment-check/attempt01/state.json').read_text());assert prior['status']=='PASS' and len(prior['rows'])==9
rtext=(p/'run.py').read_text();assert "need('Init' in deps" in rtext and "env['LEAN_NUM_THREADS']='1'" in rtext and "'-M3600'" in rtext and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in rtext
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','full_blocks':252,'tail_digits':5,'tail_bytes':24,'scope':'fixture-value composition only; symbolic K stream/file binding separate'},indent=2))
