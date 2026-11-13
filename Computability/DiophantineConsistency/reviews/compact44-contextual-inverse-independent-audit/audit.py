#!/usr/bin/env python3
"""Independent paired artifact review; contextual historical parent only."""
import hashlib,importlib.util,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('requires nonoptimized python3 -I -S')
BASE=Path(__file__).resolve().parents[2];ROOT=BASE.parents[1]
PKG=BASE/'research/ordinary12-ipra-bridge/compact44-inverse-lookup-prototype';EVIDENCE=PKG/'contextual-evidence'
OUT=Path('/tmp/ipra-compact-inverse-contextual-pair-01');PARENT=Path('/tmp/ipra-compact-row-transport-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');VIEW=Path('/tmp/ipra-historical-audit-review-01')
CONTEXT=BASE/'reviews/historical-row-contextual-audit/contextual-chain.py';ROW_AUDIT=BASE/'reviews/compact44-row-match-independent-audit/CHECK.json';PRELAUNCH=BASE/'reviews/compact44-contextual-output-guard-independent-audit'
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
SOURCE_HASH='b895139b27408838294f99cc14b8d7fd3cf9e37afef4d667f85a3baace8a9fc8';DRIVER_HASH='37cd77db39cbdc732a80cec5ccc373a5cea05ac0ba6644788e2905525e5d7388';RECEIPT_HASH='4dcbdb75860c71610ff389cdd7a6bce7ffaa374d46efa2a0c26f0a7c20aafe15'
NAMES=['CompactInverseDraft.inverse_forward','CompactInverseDraft.inverse_image','CompactInverseDraft.inverseLookup_defined'];AXIOMS={'propext','Classical.choice','Quot.sound'}
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
commit='0031a59b32';prefix=EVIDENCE.relative_to(ROOT).as_posix()+'/'
files=subprocess.run(['git','ls-tree','-r','--name-only',commit,'--',prefix],cwd=ROOT,text=True,capture_output=True,check=True,timeout=30).stdout.splitlines()
need(len(files)==4,'four evidence files')
for name in files:
 blob=subprocess.run(['git','show',commit+':'+name],cwd=ROOT,capture_output=True,check=True,timeout=30).stdout
 need(hashlib.sha256(blob).hexdigest()==H(ROOT/name),'evidence drift '+name)
need(H(PKG/'contextual-replay.py')==DRIVER_HASH and H(PKG/'CompactInverseInventory.lean')==SOURCE_HASH,'source or driver')
need(H(EVIDENCE/'receipt.json')==H(OUT/'receipt.json')==RECEIPT_HASH,'receipt')
term=json.loads((EVIDENCE/'terminal-observation.json').read_bytes())
need(term=={'session_id':80478,'observed_exit':0,'status':'PASS_CONTEXTUAL_COMPACT_INVERSE_LOOKUP_PAIR','receipt_sha256':RECEIPT_HASH,'protected_head':'73ad8806e1684415cc759ca57cce7361ce1ada01'},'actual outer observation')
need(H(PRELAUNCH/'CHECK.json')=='94d0424cd5215536ddf19e412cac3002def80e753571262fe0816a21e6817ae3' and H(PRELAUNCH/'terminal-observation.json')=='3ff6e0a85496ed989bea6da2b9f6fb5ae0477fe36a40e9bcd3524a250bccf40d','prelaunch review pins')
pre=json.loads((PRELAUNCH/'CHECK.json').read_bytes());need(pre['status']=='PASS_INDEPENDENT_CONTEXTUAL_OUTPUT_GUARD_PREFLIGHT' and pre['drivers']['compact44-inverse-lookup-prototype/contextual-replay.py']==DRIVER_HASH,'prelaunch review')
spec=importlib.util.spec_from_file_location('driver',PKG/'contextual-replay.py');driver=importlib.util.module_from_spec(spec);spec.loader.exec_module(driver);driver.pins()
r=json.loads((EVIDENCE/'receipt.json').read_bytes());need(r['status']==term['status'] and r['driver_sha256']==DRIVER_HASH and r['source_sha256']==SOURCE_HASH and r['contextual_historical_view']==str(VIEW) and len(r['rows'])==2,'receipt metadata')
need(r['parent_audit_before']==r['parent_audit_after']=='PASS_INDEPENDENT_COMPACT_ROW_MATCH_AUDIT','context parent statuses')
src=OUT/'src/DiophantineConsistency/CompactInverseInventory.lean';need(src.is_file() and not src.is_symlink() and H(src)==SOURCE_HASH and [x for x in src.read_text().splitlines() if x.startswith('import ')]==['import DiophantineConsistency.CompactRowComplete'],'frozen source/import')
expectedguards=set();result=[]
for side,row in zip(('author','peer'),r['rows']):
 lib=OUT/side/'lib';parent=PARENT/side/'lib';obj=lib/'DiophantineConsistency/CompactInverseInventory.olean';log=OUT/side/'CompactInverseInventory.log';copied=EVIDENCE/(side+'.log')
 need(row['side']==side and type(row['exit']) is int and row['exit']==0 and type(row['deps_exit']) is int and row['deps_exit']==0 and row['stop_reason'] is None,'child exits '+side)
 need(obj.is_file() and not obj.is_symlink() and H(obj)==row['object_sha256'] and log.is_file() and H(log)==H(copied)==row['log_sha256'],'artifact hashes '+side)
 cmd=row['command'];need(cmd==[str(driver.LEAN),'-M4000','-j1','-DElab.async=false',f'--root={OUT/"src"}',str(src),'-o',str(obj)],'command '+side)
 init=PACKAGE/'Init.olean';dep=lib/'DiophantineConsistency/CompactRowComplete.olean';need(init.is_file() and dep.is_file() and dep.resolve()==(parent/'DiophantineConsistency/CompactRowComplete.olean').resolve(),'required direct imports '+side)
 deps=row['deps_stdout'].splitlines();need(set(deps)=={str(init),str(dep)} and deps.count(str(init))==2 and deps.count(str(dep))==1,'recorded deps '+side)
 for path in (init,dep,obj):
  expectedguards.update(str(path)[:-6]+s for s in SUFFIXES)
  entry=r['direct_guards'].get(str(path));need(entry is not None and entry['sha256']==H(path) and entry['realpath']==str(path.resolve()),'direct/output hash '+str(path))
 text=log.read_text();reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M)
 need([x[0] for x in reports]==NAMES and all({a.strip() for a in x[1].split(',')}==AXIOMS for x in reports) and [list(x) for x in reports]==row['axiom_reports'] and not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text),'logs/axioms '+side)
 before={x.relative_to(parent) for x in parent.rglob('*.olean')};after={x.relative_to(lib) for x in lib.rglob('*.olean')};need(len(before)==1210 and after==before|{Path('DiophantineConsistency/CompactInverseInventory.olean')},'overlay inventory '+side)
 for rel in before:
  a=lib/rel;b=parent/rel;need(a.is_file() and b.is_file() and a.resolve()==b.resolve() and H(a)==H(b),'overlay object '+str(a))
 result.append({'side':side,'object_sha256':H(obj),'log_sha256':H(log),'compiler_exit':0,'deps_exit':0,'inherited_oleans':len(before),'recorded_init_lines':2})
need(result[0]['object_sha256']==result[1]['object_sha256'] and result[0]['log_sha256']==result[1]['log_sha256'],'paired results differ')
need(set(r['direct_guards'])==expectedguards and len(expectedguards)==50,'guard coverage')
for name,value in r['direct_guards'].items():
 p=Path(name)
 if value is None:need(not os.path.lexists(p),'unexpected companion '+name)
 else:need(p.is_file() and H(p)==value['sha256'] and str(p.resolve())==value['realpath'],'companion drift '+name)
proc=subprocess.run([sys.executable,'-I','-S','-B',str(CONTEXT),'row',str(VIEW)],cwd=ROOT,capture_output=True,timeout=1800)
need(proc.returncode==0 and not proc.stderr and json.loads(proc.stdout)==json.loads(ROW_AUDIT.read_bytes()),('contextual parent rerun',proc.returncode,proc.stderr[-4000:]))
# Recheck guarded inputs after the contextual callback; not continuous protection.
for name,value in r['direct_guards'].items():
 p=Path(name)
 if value is None:need(not os.path.lexists(p),'late companion '+name)
 else:need(p.is_file() and H(p)==value['sha256'] and str(p.resolve())==value['realpath'],'late guard drift '+name)
need(H(src)==SOURCE_HASH and not src.is_symlink() and H(EVIDENCE/'receipt.json')==RECEIPT_HASH,'post-parent source or receipt drift')
print(json.dumps({'status':'PASS_INDEPENDENT_CONTEXTUAL_INVERSE_PAIR','evidence_commit':commit,'receipt_sha256':RECEIPT_HASH,'source_sha256':SOURCE_HASH,'recorded_outer_session':80478,'recorded_outer_exit':0,'protected_head':term['protected_head'],'contextual_parent_rerun_exit':0,'direct_and_output_guard_slots':50,'runs':result,'scope':'Bounded inverse lookup in every IΣ₁ model; inverse image assumes j<943 and j≠1. Historical contextual parent rerun, not unchanged live parent. No word construction, graph-port binding, machine or internal iPRA result. Inherited loader/package/transitive/dynamic and sampled-resource boundaries remain.'},indent=2,sort_keys=True))
