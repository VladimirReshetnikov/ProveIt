from pathlib import Path
import hashlib,json,subprocess,re,os
repo=Path('/home/codex/.codex/worktrees/ec20/Proofs')
out=Path('/tmp/k215-phase9-upstream-merge-peer')
base='507ccc5db72bd8448347e928016bded6df084d04'
upstream='159397838a0af11c030bba140fa5618664cb5a9b'
formal=Path('Computability/BusyBeaver/Research/ZFC/k225-formal')
merge_path=formal/'verification/k215/simplification/phase9/upstream-merge/merge.json'
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=repo)
def blob(rev,p):return git('show',f'{rev}:{p}')
def mode(rev,p):return git('ls-tree',rev,'--',str(p)).decode().split()[0]
def index_mode(p):return git('ls-files','--stage','--',str(p)).decode().split()[0]
manifest_bytes=(repo/merge_path).read_bytes(); manifest=json.loads(manifest_bytes)
assert manifest['checked_phase9_commit']==base and manifest['upstream_commit']==upstream
assert git('rev-parse','HEAD').decode().strip()==base
assert git('rev-parse','MERGE_HEAD').decode().strip()==upstream
rows=manifest['upstream_paths'];assert len(rows)==13
actual_paths=set(git('diff','--name-only',base+'...'+upstream).decode().splitlines())
assert actual_paths=={r['path'] for r in rows}
checks=[]
for row in rows:
 p=row['path']; raw=(repo/p).read_bytes(); old=blob(base,p) if row['decision']=='retained_checked_Rocq_bytes' else None
 incoming=blob(upstream,p); staged=blob('',p)
 assert sha(raw)==row['selected_sha256'] and len(raw)==row['bytes']
 assert sha(incoming)==row['upstream_sha256']
 if old is not None:
  assert raw==old==staged
  assert index_mode(p)==mode(base,p)==mode(upstream,p)
 elif row['decision']=='imported_research_verbatim':
  assert raw==incoming==staged
  assert index_mode(p)==mode(upstream,p)
 else:
  assert row['decision']=='reconciled_overview'
 checks.append({'path':p,'decision':row['decision'],'sha256':sha(raw),'index_matches_selected':staged==raw,'index_sha256':sha(staged),'mode':index_mode(p)})
assert sum(r['decision']=='retained_checked_Rocq_bytes' for r in checks)==4
assert sum(r['decision']=='imported_research_verbatim' for r in checks)==8
invpath=Path('/tmp/k215-phase9-main/full-run2/inventory.json'); invbytes=invpath.read_bytes(); inv=json.loads(invbytes)
assert len(inv['modules'])==197
canonical_review=json.loads(Path('/tmp/k215-phase9-main/canonical-review.json').read_text())
assert sha(invbytes)==canonical_review['full_inventory_sha256']
lean=[]
for row in inv['modules']:
 p=Path(canonical_review['ledger'][row['module']]['canonical']).relative_to(repo); raw=(repo/p).read_bytes(); expected=row['source_sha256']
 assert sha(raw)==expected==canonical_review['ledger'][row['module']]['source']
 assert raw==blob(base,p)==blob('',p)
 assert mode(base,p)==index_mode(p)
 lean.append({'module':row['module'],'path':str(p),'sha256':expected})
assert len(manifest['retained_exact_checked_Lean_sources'])==11
for row in manifest['retained_exact_checked_Lean_sources']:
 p=row['destination'];raw=(repo/p).read_bytes()
 assert len(raw)==row['bytes'] and sha(raw)==row['source_sha256']
 assert p in {r['path'] for r in lean}
docs=[formal/'README.md',formal/'rho8cd/PROVEIT_STATUS.md',formal/'verification/k215/simplification/phase9/README.md',merge_path.parent/'README.md']
links=[]
for p in docs:
 raw=(repo/p).read_text()
 for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)',raw):
  target=target.strip().strip('<>'); path=target.split('#',1)[0]
  if not path or re.match(r'\w+://',path):continue
  resolved=((repo/p).parent/path).resolve()
  assert resolved.exists(),(p,target)
  links.append({'document':str(p),'target':target})
assert (repo/merge_path).read_bytes()==manifest_bytes
result={'status':'PASS_READ_ONLY_PENDING_MERGE_BOUNDARY','checked_phase9_commit':base,'upstream_commit':upstream,'manifest_sha256':sha(manifest_bytes),'upstream_changed_paths':13,'retained_Rocq_paths':4,'verbatim_research_paths':8,'unchanged_Lean_sources':197,'adopted_Lean_sources':11,'all_197_worktree_and_index_equal_checkpoint':True,'all_4_Rocq_worktree_and_index_equal_checkpoint':True,'all_8_research_worktree_and_index_equal_upstream':True,'local_document_links_checked':len(links),'overview_index_still_upstream_pending_root_stage':not checks[0]['index_matches_selected'],'checks':checks,'Lean_source_pins':lean,'document_pins':{str(p):sha((repo/p).read_bytes()) for p in docs},'scope':'Read-only Git blob/index/current-source checks and ordinary documentation scope review. No compiler, generator, search, proof execution, canonical mutation, or merge commit. The reconciled overview is unstaged at review time and must be staged by root before commit; imported files and retained production already match index. No new rho8cd kernel or full mathematical derivation review is claimed.'}
(out/'review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['checks','Lean_source_pins','document_pins']}))
