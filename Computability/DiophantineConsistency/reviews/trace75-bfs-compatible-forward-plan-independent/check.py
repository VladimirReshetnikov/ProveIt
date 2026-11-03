from pathlib import Path
import hashlib,json,os,re
root=Path(__file__).resolve().parents[2];h=root/'research/trace75-bfs-compatible-forward-plan';res=h/'observations/plan-attempt01/result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(h/'plan.py')=='c01a02e548f456872b6c7d5c4e4b9f4fc4c2d3ff163c8d884f9e2af04171119f' and sha(res)=='baa12a3a2a04ecfa32e0f925c8a79a4b2f7b520691a6c506a851b6f7a3473199'
d=json.loads(res.read_text());assert d['status']=='PASS' and d['planner_sha256']==sha(h/'plan.py') and len(d['stages'])==21 and len(d['direct'])==42 and d['direct_hash_changes']==[] and d['direct_outside_absent_from_bfs_capture']==[]
inputs={'research/trace75-bfs-compatible-provider-rebuild/observations/attempt01/result.json':d['parent_result_sha256'],'research/trace75-bfs-compatible-provider-rebuild/observations/outer-attempt01/terminal.json':d['parent_outer_sha256'],'reviews/trace75-bfs-compatible-provider-result-independent/README.md':d['parent_audit_sha256'],'research/trace75-bfs-model-halt-prototype/observations/attempt01/result.json':d['prior_client_result_sha256']}
for n,v in inputs.items():assert sha(root/n)==v
parent=json.loads((root/'research/trace75-bfs-compatible-provider-rebuild/observations/attempt01/result.json').read_text());outer=json.loads((root/'research/trace75-bfs-compatible-provider-rebuild/observations/outer-attempt01/terminal.json').read_text());hist=json.loads((root/'research/trace75-bfs-model-halt-prototype/observations/attempt01/result.json').read_text());assert parent['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==d['parent_result_sha256']
names=[r['module'] for r in d['stages']];assert len(set(names))==21 and names[-1]=='Trace75BFSModelHalt';producer_roots=list(reversed(hist['env']['LEAN_PATH'].split(':')[:-2]));assert len(producer_roots)==21
base=Path(parent['output_root'])/'lib';pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');core=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean');outside=json.loads((root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json').read_text())
def select(n,roots):
 for q in roots:
  p=Path(q)/(n.replace('.','/')+'.olean')
  if os.path.lexists(p):assert p.is_file();return p
 raise AssertionError(n)
seen=set();nonstage=set()
for row,producer in zip(d['stages'],producer_roots):
 n=row['module'];receipt=Path(row['receipt']);r=json.loads(receipt.read_text());src=Path(row['source']);snap=Path(row['snapshot']);stdout=Path(row['stdout']);stderr=Path(row['stderr']);assert sha(receipt)==row['receipt_sha256'] and r['status']=='PASS' and r['stage']['exit']==0 and r['stage']['reason'] is None
 assert sha(src)==sha(snap)==row['source_sha256']==row['snapshot_sha256'] and sha(stdout)==row['stdout_sha256']==r['stage']['stdout_sha256'] and sha(stderr)==row['stderr_sha256']==r['stage']['stderr_sha256'] and not stderr.read_bytes() and not re.search(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b',stdout.read_text())
 assert Path(row['old_object']).parent==Path(producer) and sha(row['old_object'])==row['old_object_sha256']==r['object_sha256']
 imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M);assert imports==row['imports']==[x for x in row['prior_serialized_headers'] if x!='Init'] and row['prior_serialized_headers']==r['header_imports']
 for dep,rec in row['direct'].items():
  if rec['kind']=='stage':assert dep in seen
  else:
   nonstage.add(dep);now=select(dep,[base,pack,core]);old=select(dep,r['env']['LEAN_PATH'].split(':'));assert str(old)==rec['old_selected'] and sha(old)==rec['old_sha256']==sha(now)==rec['bundle']['.olean']['sha256']
   if rec['kind']=='outside':assert dep in outside
   for ext,item in rec['bundle'].items():
    p=Path(str(now)[:-6]+ext)
    if item is None:assert not os.path.lexists(p)
    else:assert p.is_file() and str(p)==item['path'] and str(p.resolve(strict=True))==item['resolved'] and sha(p)==item['sha256'] and (os.readlink(p) if p.is_symlink() else None)==item['link']
 seen.add(n);print(n,'source',src,'receipt',receipt)
assert nonstage==set(d['direct'])
reverse=json.loads((root/'research/trace75-bfs-compatible-reverse-plan/observations/source-plan-attempt01/result.json').read_text()); reverse_names={r['module'] for r in reverse['stages']};assert not (set(names)&reverse_names) and not (nonstage&reverse_names)
print('PASS 21 source/receipt/header rows, 42 non-stage first selections and historical hashes, outside baseline, no reverse-stage name collisions')
