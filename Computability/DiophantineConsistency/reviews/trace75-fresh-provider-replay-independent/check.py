from pathlib import Path
from hashlib import sha256
import json,os
base=Path('research/trace75-fresh-provider-rebuild');obs=base/'observations/attempt01';outer=base/'observations/outer-attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 assert p.is_file(),p
 return {'path':str(p),'resolved':str(p.resolve(strict=True)),'sha256':sha(p),'link':os.readlink(p) if p.is_symlink() else None}
def bundle(stem,suffixes):return {s:rec(str(stem)+s) for s in suffixes}
def h(rec):return None if rec is None else rec['sha256']
def hashes(bundle):return {s:h(x) for s,x in bundle.items()}
p=obs/'result.json';assert sha(p)=='b74858343a05be6710e0666abb86189aea375ebd4d494411fee00d31e9f31e1a';j=json.loads(p.read_text());assert j['status']=='PASS'
t=outer/'terminal.json';assert sha(t)=='4c310be9b2ee9aa32378f27869c87e7bbbd8af2512f3b6391d02518e3dcbc7af';o=json.loads(t.read_text());assert o['exit']==0 and o['child_result_sha256']==sha(p) and o['wrapper_sha256_before']==o['wrapper_sha256_after']==sha(base/'run-outer.py')=='0ed48c144b4cccc026bd4967d1e410889f8379a522999f66bcf21279aff06d1d' and sha(outer/'stdout')==o['stdout_sha256'] and sha(outer/'stderr')==o['stderr_sha256'] and not (outer/'stderr').read_text();assert o['inputs_before']==o['inputs_after']
for k,v in o['inputs_before'].items():assert sha(k)==v
assert sha(base/'run-v2.py')==j['runner_sha256']=='9aaffde57346464f11a963ff4960592c871cd88c3eef8badd5652f6515fca67b'
for k,v in j['inputs'].items():assert sha(k)==v
plan=json.loads(Path('research/trace75-fresh-provider-plan/observations/plan-attempt01/result.json').read_text());scan=json.loads(Path('research/trace75-bfs-provider-preflight/observations/scan-attempt01/result.json').read_text());bfs=json.loads(Path('research/direct-bfs-80-coherent-rebuild/observations/attempt01/result.json').read_text());initial=json.loads(Path('research/direct-bfs-80-coherent-rebuild/observations/attempt01/initial-project.json').read_text());outs=json.loads(Path('research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json').read_text());old=bfs['closure']['project'];lib=Path(j['output_root'])/'lib';src=Path(j['output_root'])/'src';pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');core=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
assert j['env']=={'PATH':'/usr/bin:/bin','LEAN_PATH':str(lib)+':'+str(pack),'LEAN_NUM_THREADS':'1'} and j['reader_env']=={'PATH':'/usr/bin:/bin'}
assert sha(obs/'initial-union.json')==j['initial_union_sha256'];ini=json.loads((obs/'initial-union.json').read_text());assert len(ini)==1963 and len(j['supplements'])==40
expected=dict(initial);assert not set(expected)&set(bfs['built']);expected.update(bfs['built']);assert len(expected)==1931
for n in j['supplements']:
 c=plan['classification'];e=c['different'].get(n) or c['absent'].get(n);assert e;expected[n]=e['trace']
assert set(ini)==set(expected)
for n,v in ini.items():
 e=expected[n]
 for s in v:
  a=v[s];b=e[s];assert h(a)==h(b) and (a is None or a['resolved']==b['resolved']),(n,s)
assert j['stage_order']==plan['stage_order'] and len(j['stages'])==14 and len(set(j['stage_order']))==14
for i,st in enumerate(j['stages'],1):
 n=st['module'];row=plan['producers'][n];receipt=json.loads(Path(row['receipt']).read_text());a=Path(row['receipt']).parent
 assert st['index']==i and n==j['stage_order'][i-1] and st['status']=='PASS' and st['exit']==0 and st['reason'] is None and st['env']==j['env']
 assert st['source']==row['source'] and st['source_sha256']==row['source_sha256']==sha(row['source'])==sha(a/'source.txt')==sha(src/(n+'.lean'))==sha(obs/f'stage-{i:02}.source.lean')
 for typ in ('stdout','stderr'):
  now=obs/f'stage-{i:02}.{typ}';baseline=a/typ;assert sha(now)==st[typ+'_sha256']==sha(baseline)==receipt[typ+'_sha256']
 assert st['command'][0].endswith('/bin/lean') and st['command'][-1]==str(lib/(n+'.olean')) and st['command'][-4]==f'--root={src}' and st['command'][-3]==str(src/(n+'.lean')) and st['command'][-2]=='-o'
 assert st['preflight']['mem_available_kib']>=8*1024**2 and len(st['preflight']['lean'])<2
 assert all(s['mem_available_kib']>=8*1024**2 and len(s['lean'])<=2 for s in st['samples'])
 assert st['object']['.olean']['link'] is None and bundle(lib/n,st['object'].keys())==st['object'];assert n not in expected;expected[n]=st['object']
 assert st['object']['.olean']['sha256']==scan['selected_project'][n]['.olean']['sha256']
assert len(expected)==j['union_count']==1977
actual={str(p.relative_to(lib)) for p in lib.rglob('*') if p.is_file() or p.is_symlink()};wanted={n.replace('.','/')+s for n,b in expected.items() for s,v in b.items() if v is not None};assert actual==wanted
for n,e in expected.items():
 now=bundle(lib/n.replace('.','/'),e.keys());assert hashes(now)==hashes(e)
 for s,v in e.items():assert v is None or now[s]['resolved']==v['resolved']
selected=j['selected_project'];external=j['selected_outside'];heads=j['serialized_headers'];assert len(selected)==248 and len(external)==28 and set(selected)==set(heads)==set(j['header_reuse']) and not j['headers']
for n,b in selected.items():assert n in expected and bundle(lib/n.replace('.','/'),b.keys())==b and hashes(b)==hashes(expected[n])
for n,b in external.items():
 rel=n.replace('.','/')+'.olean';found=None
 for root in (lib,pack,core):
  p=root/rel
  if os.path.lexists(p):assert p.is_file();found=p;break
 assert found and str(found)==b['.olean']['path'] and bundle(str(found)[:-6],b.keys())==b and n in outs and hashes(b)==hashes(outs[n])
for n in j['header_reuse']:
 val=selected[n]['.olean']['sha256'];sc=scan['selected_project'].get(n);pr=old.get(n)
 if sc is not None and sc['.olean']['sha256']==val:assert heads[n]==scan['headers'][n]
 else:assert pr is not None and pr['record']['sha256']==val and heads[n]==pr['imports']
for root,r in j['closures'].items():
 q=[root];inside=set();outside=set()
 while q:
  n=q.pop()
  if n in inside or n in outside:continue
  if n in heads:inside.add(n);q.extend(heads[n])
  else:assert n in external;outside.add(n)
 assert inside==set(r['project']) and outside==set(r['outside'])
 if root=='DirectBFSBandCarry':
  assert len(inside)==46 and len(outside)==6
  for n in inside:assert n in old and hashes(selected[n])==hashes(old[n]['companions'])
 else:assert root=='Trace75FixedCongruence' and len(inside)==208 and len(outside)==27
for n,hv in [('DiophantineConsistency.ModelRatioBounds','8ba17e0bed97840d42029767098fc5830d2990020d5200e1b9c6f737e88e6818'),('DiophantineConsistency.ArithmeticNegativeNorms','33cf47041c950f77cd4535d629dcddfa27ff9ea1fcd21cc1af0fb732dd5eb319')]:
 assert selected[n]['.olean']['sha256']==hv and n in j['closures']['Trace75FixedCongruence']['project']
print('PASS: actual recorded outer exit 0; 14 exact-source/stage/report guarded successes; all 14 output hashes match prior objects despite replay with fresh selected seeds.')
print('PASS: 1963 initial → 1977 final union, 248 project/28 outside; exact-hash reuse of all 248 retained headers; 46 BFS project companion matches; trace75 208/27 and BFS 46/6 reachability; two fresh seeds selected.')
print('Current post-run recheck and retained runner evidence, not independent Lean replay or full historical/package/dynamic/file provenance.')
