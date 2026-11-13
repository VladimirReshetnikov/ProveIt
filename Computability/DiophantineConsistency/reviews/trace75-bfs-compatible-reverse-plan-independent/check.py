from pathlib import Path
import hashlib,json,os,re
root=Path(__file__).resolve().parents[2];h=root/'research/trace75-bfs-compatible-reverse-plan'; a=h/'observations/source-plan-attempt01/result.json'; b=h/'observations/outside-attempt01/result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(h/'plan.py')=='00c0376315b481b52d462856ac788f2ba640ea1748fbf163b3627635f57b57a4' and sha(h/'capture-outside.py')=='aab6bb6c5b4f3bf49819e238b52bbbeec3f19c3f17d47148b6b2e2c58146c35f'
assert sha(a)=='369d06ba5bd50b038d7279324819bcb76bb45e7bc8c0c1ff727eccb3c32c86af' and sha(b)=='8847a09fb7925816ab7ceaab0d61a12c0b814b2a7571daae32ea1f510c779016'
s=json.loads(a.read_text());o=json.loads(b.read_text());assert s['status']==o['status']=='PASS' and len(s['stages'])==13 and sha(s['historical_direct_plan'])==s['historical_direct_plan_sha256']
old=json.loads(Path(s['historical_direct_plan']).read_text());assert len(old['stages'])==13
seen=set();projects=set();outside=set()
for row,prev in zip(s['stages'],old['stages']):
 n=row['module'];assert n==prev['module'] and row['prior_direct']==prev['direct'] and row['imports']==prev['imports'];src=Path(row['source']);receipt=Path(row['receipt']);d=json.loads(receipt.read_text());assert sha(src)==sha(row['snapshot'])==row['source_sha256']==row['snapshot_sha256'] and sha(receipt)==row['receipt_sha256']
 assert d['exit']==0 and d['reason'] is None and d['object_sha256']==row['historical_object_sha256']
 assert sha(row['stdout'])==row['stdout_sha256']==d['stdout_sha256'] and sha(row['stderr'])==row['stderr_sha256']==d['stderr_sha256']
 assert Path(row['stdout']).read_text()==row['expected_stdout'] and not Path(row['stderr']).read_bytes() and not re.search(r'(?i)\b(?:warning|error)(?:\([^:\n]*\))?:|\bsorryAx\b',row['expected_stdout'])
 names=re.findall(r'^#print axioms\s+([^\s]+)',src.read_text(),re.M);assert len(names)==1 and row['expected_stdout'].startswith("'"+names[0]+"' depends on axioms:")
 assert re.findall(r'^import\s+([^\s]+)',src.read_text(),re.M)==row['imports']
 for mod,rec in row['prior_direct'].items():
  if rec['kind']=='stage':assert mod in seen
  elif rec['kind']=='project':projects.add(mod)
  elif rec['kind']=='outside':outside.add(mod)
  else:raise AssertionError(rec)
 seen.add(n);print(n,'source',src,'receipt',receipt,'stage imports',','.join(k for k,v in row['prior_direct'].items() if v['kind']=='stage'))
assert len(projects)==11 and len(outside)==4
outside_base=root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json';assert sha(outside_base)==o['outside_baseline_sha256']; assert outside-set(json.loads(outside_base.read_text()))=={o['module']}=={'Mathlib.Algebra.Order.Ring.Basic'}
pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');core=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean');rel=o['module'].replace('.','/');candidates=[p/(rel+'.olean') for p in (pack,core) if os.path.lexists(p/(rel+'.olean'))];assert candidates and candidates[0].is_file() and candidates[0]==pack/(rel+'.olean')
for suffix,record in o['record'].items():
 p=Path(str(candidates[0])[:-6]+suffix)
 if record is None:assert not os.path.lexists(p)
 else:assert p.is_file() and str(p)==record['path'] and str(p.resolve(strict=True))==record['resolved'] and sha(p)==record['sha256'] and (os.readlink(p) if p.is_symlink() else None)==record['link']
parent=json.loads((root/'research/trace75-bfs-compatible-provider-plan/observations/plan-attempt01/result.json').read_text());assert set(parent['inherited_baseline_affected'])=={'DiophantineConsistency.ModelArithmetic','DiophantineConsistency.ModelExponentialCongruence','PellOddFold','PellRecovery'}
print('PASS 13 source/receipt/import rows, 11 distinct prior project inputs, 4 prior outside inputs; one outside bundle and 4 inherited baseline names')
