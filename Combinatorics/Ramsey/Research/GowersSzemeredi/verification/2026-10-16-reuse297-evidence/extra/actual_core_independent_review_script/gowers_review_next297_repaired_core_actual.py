import sys;sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,subprocess,re,datetime,functools
ROOT=Path('/home/codex/.codex/worktrees/9c9b/Proofs');ATT=Path('/tmp/gowers-next297-repaired6a75-core-attempt1');OUT=Path('/tmp/gowers-next297-repaired-core-actual-independent-review');OLD='9dce5ce380082bb050254e9625c6aa1ce48ae34a';NEW='6a753d0702d1691c25a21bdbdb58e29412931be5';REL='Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs18GeneralIteration.lean';CHECKER='Combinatorics/Ramsey/scripts/check_gowers.py'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def canonical(v):return json.dumps(v,sort_keys=True,separators=(',',':'))
def same(a,b):return canonical(a)==canonical(b)
def pairs(xs):
 d={}
 for k,v in xs:assert k not in d;d[k]=v
 return d
def read(p):return json.loads(Path(p).read_text(),object_pairs_hook=pairs)
def git(*args,data=None):return subprocess.check_output(['git','--no-optional-locks',*args],cwd=ROOT,input=data)
rp=ATT/'receipt.json';assert sha(rp)=='49317f4283d64f5bbbce9ce003be2958756c554e95178286382c25d507b6500e';r=read(rp);snap=Path(r['snapshot_path']);assert sha(snap)==r['snapshot_sha256']=='e3f24c8ebfe20b2a248076497748ca1cbd2f2c1d5176e56ce45af9eebe6011b3';s=read(snap);ledgerp=Path('/tmp/gowers-next297-repaired6a75-source-ledger-v2.json');assert sha(ledgerp)=='b80bac73cb45ab37ebc5200f7bae496e4926f8afe242d5f7acf4d49cea72bbf7';ledger=read(ledgerp)
assert r['status']=='passed'and r['mode']=='core'and type(r['terminal_exit'])is int and r['terminal_exit']==0
assert r['source_commit']==s['source_commit']==ledger['source_commit']==NEW and s['root']==str(ROOT)
assert same(ledger['snapshot'],{'path':str(snap),'sha256':sha(snap)})
oldp=Path(ledger['pre_repair_snapshot']['path']);assert sha(oldp)==ledger['pre_repair_snapshot']['sha256'];os=read(oldp);assert os['source_commit']==OLD
assert same(s['modes'],os['modes'])and same(s['graph'],os['graph'])and same(s['tools'],os['tools'])and same(s['plan'],os['plan'])
assert s['source_hashes'].keys()==os['source_hashes'].keys();changed_paths=[p for p in s['source_hashes']if s['source_hashes'][p]!=os['source_hashes'][p]];assert changed_paths==[REL],changed_paths
assert git('diff','--name-only',OLD,NEW).decode().splitlines()==[REL]
a=git('show',OLD+':'+REL).decode();b=git('show',NEW+':'+REL).decode();before='Q.isProper_of_step_pos (by decide)';after='Q.isProper_of_step_pos (by change 0 < (1 : Nat); decide)';assert a.count(before)==1 and a.replace(before,after)==b and len(a.splitlines())==len(b.splitlines())==66
assert hashlib.sha256(b.encode()).hexdigest()==s['source_hashes'][REL]=='ea464a5217c03066e2e3b7343f1a6dddf393010ab8d02717ed57e0347a8d13e1'
assert (ROOT/REL).read_text()==b
keys={'schema_version','mode','source_commit','snapshot_path','snapshot_sha256','runner_sha256','command','expected_modules','started_at','source_guard_before','previous_receipt'};started=read(ATT/'started.json');assert set(started)==keys==set(r['started_keys'])and len(r['started_keys'])==len(keys);assert same(started,{k:r[k]for k in started})and r['previous_receipt']is None
launched=read(ATT/'launched.json');assert set(launched)=={'pid','command','cwd','observed_at'}and type(launched['pid'])is int and launched['pid']>0;assert same(launched,r['launched'])and launched['cwd']==str(ROOT)and same(launched['command'],r['command'])
spec=s['modes']['core'];assert spec['roots']==['GowersSzemeredi.Proofs18FinalStep']and spec['module_count']==573 and spec['input_count']==576 and spec['source_lines']==124991
assert r['command'][1:]==[CHECKER,*spec['roots']]and Path(r['command'][0]).name.startswith('python')and r['expected_modules']==573
for path,h in s['tools'].items():assert sha(path)==h,path
assert s['tools'][str(Path('/tmp/gowers-next297-native-tools/run.py'))]==r['runner_sha256']=='bf1aa169ed14fc098fd20c57a93a8c9904718bfc2b2648997384a3effd61e83a';assert sha(s['plan']['path'])==s['plan']['sha256']
log=Path(r['log']);assert log==ATT/'native.log';text=log.read_text();assert sha(log)==r['log_sha256']=='d9f5a476f4caaf055ef180136ebe9427112f0f9b7225076bfdf529aa658fdadb';foot=re.findall(r'^Checked (\d+) modules \(including up-to-date dependencies\)\.$',text,re.M);assert foot==['573']and text.rstrip().endswith('Checked 573 modules (including up-to-date dependencies).');assert re.search(r'error(?:\([^)]*\))?:',text,re.I)is None
term=read(ATT/'terminal.json');termkeys={'command','started_at','finished_at','terminal_exit','terminal_module_count','terminal_module_count_matches','contains_error_diagnostic','log','log_sha256'};assert set(term)==termkeys and same(term,{k:r[k]for k in term});assert type(term['terminal_exit'])is int and term['terminal_exit']==0 and type(term['terminal_module_count'])is int and term['terminal_module_count']==573 and term['terminal_module_count_matches']is True and term['contains_error_diagnostic']is False
stamps=[s['captured_at'],r['started_at'],launched['observed_at'],r['finished_at'],r['verified_at'],r['recorded_at']];times=[datetime.datetime.fromisoformat(t)for t in stamps];assert all(t.tzinfo for t in times)and times==sorted(times)
assert r['source_stability_verified']is True and r['artifact_stability_verified']is True;guard={'source_commit':NEW,'protected_file_count':len(s['source_hashes']),'source_hashes':s['source_hashes']};assert same(guard,r['source_guard_before'])and same(guard,r['source_guard_after'])
def modpath(m):return ('Combinatorics/Ramsey/Lean/'if m.startswith('GowersSzemeredi')else'lib/openai-math/lean/')+m.replace('.','/')+'.lean'
configs=[CHECKER,'lean-toolchain','lake-manifest.json'];facades=['Combinatorics/Ramsey/Lean/GowersSzemeredi.lean','Combinatorics/Ramsey/Lean/GowersSzemeredi/Audit.lean','Combinatorics/Ramsey/Lean/GowersSzemeredi/PortImportAudit.lean'];inventory='Combinatorics/Ramsey/gowers-proof-status.json';expected={modpath(m)for m in s['graph']}|set(configs+facades+[inventory]);assert len(expected)==1962 and set(s['source_hashes'])==expected and len(s['graph'])==1955
@functools.lru_cache(None)
def closure(m):return frozenset({m}).union(*(closure(d)for d in s['graph'][m]if d in s['graph']))
core=sorted(closure(spec['roots'][0]));assert core==spec['modules']==spec['cumulative_modules']and len(core)==573
assert set(r['artifacts_after'])==set(core)and set(r['artifacts_before'])==set(core)
for m,v in r['artifacts_after'].items():assert set(v)=={'mtime_ns','size','fresh'}and type(v['mtime_ns'])is int and v['mtime_ns']>0 and type(v['size'])is int and v['size']>0 and v['fresh']is True,m
# Committed/source byte validation only. No .olean or other current cache/artifact reads.
input_bytes=''.join(NEW+':'+p+'\n'for p in s['source_hashes']).encode();raw=git('cat-file','--batch',data=input_bytes);offset=0
for path,h in s['source_hashes'].items():
 end=raw.index(b'\n',offset);header=raw[offset:end].split();assert len(header)==3 and header[1]==b'blob';size=int(header[2]);blob=raw[end+1:end+1+size];assert hashlib.sha256(blob).hexdigest()==h,path;assert sha(ROOT/path)==h,path;offset=end+size+2
assert offset==len(raw)
assert sum(len((ROOT/modpath(m)).read_text().splitlines())for m in core)==124991
owner=next(x for x in ledger['owners']if x['file']==REL);assert owner['draft_sha256']==s['source_hashes'][REL]and owner['pre_repair_sha256']==os['source_hashes'][REL]
assert ledger['inventory_sha256']==s['source_hashes'][inventory]and ledger['combined_modules']==1955 and ledger['protected_files']==1962
prior_meta=ledger['supersedes_ledger_metadata'];assert sha(prior_meta['path'])==prior_meta['sha256'];assert same(read(prior_meta['path'])['snapshot'],ledger['pre_repair_snapshot'])
assert not any(p.name.startswith('failure')for p in ATT.iterdir())
pins={str(p):sha(p)for p in[rp,ATT/'started.json',ATT/'launched.json',ATT/'terminal.json',log,snap,ledgerp,oldp]};assert pins[str(rp)]=='49317f4283d64f5bbbce9ce003be2958756c554e95178286382c25d507b6500e'
OUT.mkdir(exist_ok=False)
report=dict(status='PASS independent completed core evidence and repaired-source attribution review',findings=[],source_commit=NEW,previous_failed_source_commit=OLD,actual_core=dict(mode='core',command=r['command'],terminal_exit=0,module_count=573,input_count=576,source_lines=124991,started_at=r['started_at'],finished_at=r['finished_at'],verified_at=r['verified_at'],recorded_at=r['recorded_at'],footer_exact=True,error_diagnostic_absent=True,typed_started_launched_terminal_receipt_equality=True,chronology_valid=True),evidence_pins=pins,source_checks=dict(primary_snapshot_sha256=sha(snap),source_hash_paths=1962,snapshot_graph_modules=1955,all_snapshot_bytes_current_and_committed_exact=True,core_closure_reproduced=True,source_guards_typed_exact=True,only_git_change_from_failed_source=REL,exact_repair_before=before,exact_repair_after=after,repair_source_sha256=s['source_hashes'][REL],source_line_delta=0,inventory_unchanged=True),ledger_v2=dict(path=str(ledgerp),sha256=sha(ledgerp),primary_snapshot_is_repaired=True,pre_repair_snapshot_explicit_and_preserved=True,predecessor_v1_stale_primary_reference_retained_as_history=True),artifact_scope=dict(recorded_after_entries=573,recorded_fresh_flags_all_true=True,recorded_native_runner_stability_verified=True,current_artifact_recheck_performed=False,reason='Shared1906 is live; this review reads only immutable completed core evidence and source files. It does not inspect changing cache artifacts.'),limitations=['One completed core checker command is certified here; no separate per-module terminal exits are claimed.','The core footer explicitly includes up-to-date dependencies. Recorded freshness/stability is not a claim that every module rebuilt in this invocation.','The live shared1906 attempt and future supplemental outcome are outside this review; no full three-stage success is inferred.'],no_native_helper_entrypoint_repository_git_cache_mutation=True,live_shared_logs_and_artifacts_untouched=True,review_script=dict(path=str(Path(__file__)),sha256=sha(__file__)))
(OUT/'report.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');(OUT/'freeze.json').write_text(json.dumps({'assets':[{'path':str(p),'sha256':sha(p)}for p in sorted(OUT.iterdir())if p.is_file()],'review_script':report['review_script']},indent=2)+'\n');print(json.dumps({'report_path':str(OUT/'report.json'),'report_sha256':sha(OUT/'report.json'),'freeze_sha256':sha(OUT/'freeze.json'),'core573':'PASS','repair_only_one_line':True},indent=2))
