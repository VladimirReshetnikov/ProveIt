from pathlib import Path
import ast,hashlib,json,os,subprocess
R=Path('/home/codex/.codex/worktrees/ec20/Proofs'); O=Path('/tmp/k215-upstream49-merge-review')
BASE='437804fcdd5550fec6ece3b6073c616690d4625f';UP='49e99c5b7cc6c2e164331961de28bad3904361fd'
L='Computability/BusyBeaver/Lean/BusyBeaver/ZFC/';F='Computability/BusyBeaver/Research/ZFC/k225-formal/'
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def meta(b):return {'bytes':len(b),'sha256':sha(b),'git_blob':blob(b)}
def at(rev,path):
 raw=git('ls-tree',rev,'--',path)
 if not raw:return {'absent':True}
 left,p=raw.rstrip(b'\n').split(b'\t',1); mode,kind,oid=left.decode().split();assert p.decode()==path and kind=='blob'
 b=git('cat-file','blob',oid);assert blob(b)==oid
 return dict(meta(b),mode=mode,absent=False)
def current(path):
 p=R/path
 if not p.exists():assert not p.is_symlink();return {'absent':True}
 assert p.is_file()and not p.is_symlink()
 return dict(meta(p.read_bytes()),mode='100755'if p.stat().st_mode&0o111 else'100644',absent=False)
def index(path):
 raw=git('ls-files','--stage','-z','--',path)
 if not raw:return {'absent':True}
 entries=[]
 for record in raw.rstrip(b'\0').split(b'\0'):
  left,p=record.split(b'\t',1);mode,oid,stage=left.decode().split();assert p.decode()==path
  b=git('cat-file','blob',oid);entries.append(dict(meta(b),mode=mode,stage=int(stage)))
 return {'absent':False,'entries':entries}
head=git('rev-parse','HEAD').decode().strip(); actual_origin=git('rev-parse','origin/main').decode().strip()
raw=git('diff','--name-status','-z',BASE,UP).split(b'\0');rows=[]
assert raw[-1]==b'';raw=raw[:-1];assert len(raw)==20
for status,path in zip(raw[::2],raw[1::2]):
 path=path.decode();status=status.decode();assert status in ['A','M']
 b=git('show',UP+':'+path); dest=O/'upstream'/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 row={'path':path,'status':status,'base':at(BASE,path),'head':at(head,path),'upstream':at(UP,path),'worktree':current(path),'index_observation':index(path),'upstream_snapshot':str(dest)}
 row['current_equals_upstream']=row['worktree'].get('sha256')==row['upstream']['sha256']
 if path.endswith('ZFModelSemantics.lean'):action='KEEP_CANONICAL_ABSENT; retain upstream bytes as immutable proposal data'
 elif path.endswith('.lean'):action='PRESERVE_EXACT_CHECKED_WORKTREE; retain upstream bytes as immutable proposal data'
 elif path.endswith('derivation_core.txt'):action='PRESERVE_PINNED_f0a2_INPUT; retain new six-goal derivation separately as proposal data'
 elif path.endswith('generate_domrho8_cd.py'):action='OPTIONAL_EXACT_UPSTREAM_INERT_RESEARCH_IMPORT; no renderer execution or checked-production claim'
 else:action='RECONCILE_DOCUMENTATION_ONLY; distinguish upstream claimed build from our retained checked sources'
 row['recommended_action']=action;rows.append(row)
assert len(rows)==10
adoptpath=Path('/tmp/k215-phase12-import-proposal/adoption.json');adopt=json.loads(adoptpath.read_text())
protected=[]
for entry in adopt['files']:
 target=Path(entry['target']);path=target.relative_to(R).as_posix()if target.is_absolute()else str(target)
 cur=current(path);assert cur['sha256']==entry['sha256'];protected.append({'path':path,'reason':'exact adopted phase12 source/producer','checked_sha256':entry['sha256'],'current':cur,'head':at(head,path),'upstream':at(UP,path)})
assert len(protected)==8
for suffix,prefix,reason in [
 (L+'DominatedImplication.lean','a128ddd54','phase11 checked core retained throughout phase12'),
 (L+'Lukasiewicz.lean','5bae','checked unchanged implication bridge retained throughout phase12'),
 (F+'rho8cd/derivation_core.txt','f0a2e60d','literal input of maintained31fdd producer'),
 (F+'generate_dominated_implication_lean.py','31fdd538','maintained checked producer, not upstream research renderer'),
]:
 cur=current(suffix);assert cur['sha256'].startswith(prefix),(suffix,cur)
 protected.append({'path':suffix,'reason':reason,'checked_sha256':cur['sha256'],'current':cur,'head':at(head,suffix),'upstream':at(UP,suffix)})
assert len(protected)==12
for row in protected:
 dst=O/'checked'/row['path'];dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes((R/row['path']).read_bytes());row['checked_snapshot']=str(dst)
producerpath=R/(F+'generate_dominated_implication_lean.py');tree=ast.parse(producerpath.read_text());pins=None
for node in tree.body:
 if isinstance(node,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='INPUT_PINS'for t in node.targets):pins=ast.literal_eval(node.value)
assert isinstance(pins,dict)and len(pins)==3
pinrows=[]
for relative,expected in pins.items():
 path=F+relative;cur=current(path);assert cur['sha256']==expected
 pinrows.append({'path':path,'expected_sha256':expected,'current':cur,'upstream':at(UP,path)})
absences=[]
for suffix in ['dominated_implication_templates/core-prefix.txt','dominated_implication_templates/core-suffix.txt']:
 path=F+suffix;assert current(path)['absent'];absences.append({'path':path,'current':current(path),'upstream':at(UP,path)})
# Re-read source bytes only. Root may stage/commit concurrently; no index equality assumption is made.
assert all(current(row['path'])==row['worktree']for row in rows)
assert all(current(row['path'])==row['current']for row in protected)
result={'status':'PASS_READONLY_EXACT_MERGE_BOUNDARY_CENSUS','base':BASE,'upstream':UP,'observed_head':head,'observed_origin':actual_origin,'changed_path_count':len(rows),'changed_paths':rows,'protected_checked_paths':protected,'maintained_producer_input_pins':pinrows,'retired_template_absences':absences,'phase12_adoption_sha256':sha(adoptpath.read_bytes()),'reader_sha256':sha(Path(__file__).read_bytes()),'scope':'Git blob/file byte census and own AST literal INPUT_PINS read only; no Lean/Rocq/compiler/renderer/producer execution, no Git/index/canonical mutation. Index is an observation during root staging. Upstream claims are data, not newly accepted execution.'}
(O/'review.json').write_text(json.dumps(result,indent=2)+'\n')
maprows=[]
for row in rows:
 maprows.append({'original_path':row['path'],'source_commit':UP,'source_git_blob':row['upstream']['git_blob'],'source_sha256':row['upstream']['sha256'],'source_mode':row['upstream']['mode'],'source_snapshot':row['upstream_snapshot'],'proposed_raw_target':F+'verification/k215/simplification/phase12/upstream-merge/inputs/'+row['path'].removeprefix('Computability/BusyBeaver/'),'production_action':row['recommended_action'],'preserved_sha256':row['worktree'].get('sha256'),'preserved_absence':row['worktree']['absent']})
(O/'proposal-map.json').write_text(json.dumps({'status':'PROPOSED_ONLY_NO_CANONICAL_WRITES','files':maprows,'protected_current':protected,'scope':'Root chooses raw copies or exact Git references. Existing research renderer may be imported verbatim as inert research; its supplied commands are not run. Documentation requires explicit reconciliation.'},indent=2)+'\n')
print(json.dumps({'status':result['status'],'head':head,'paths':len(rows),'protected':len(protected),'review_sha256':sha((O/'review.json').read_bytes()),'proposal_map_sha256':sha((O/'proposal-map.json').read_bytes()),'all_current_source_bytes_unchanged':True,'upstream_source_rows':[{ 'path':r['path'],'git_blob':r['upstream']['git_blob'],'sha256':r['upstream']['sha256'],'current_sha256':r['worktree'].get('sha256')}for r in rows]},indent=2))
