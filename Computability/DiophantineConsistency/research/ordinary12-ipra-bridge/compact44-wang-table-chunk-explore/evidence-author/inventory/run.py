#!/usr/bin/env python3
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys,traceback
from pathlib import Path
BASE=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-wang-table-chunk-explore')
BUILD=Path('/tmp/ipra-wang-chunk-author-build-02'); OUT=Path('/tmp/ipra-wang-chunk-author-inventory-02');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');MON=BASE.parent/'free-j-current-denominator-composition/replay.py'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj
try:
 need(not os.path.lexists(OUT),'output occupied');need(shutil.disk_usage('/tmp').free>=4*1024**3,'disk reserve')
 need(H(BUILD/'RESULT.json')=='f79b98bb500a0cf2af5dfda7f7341468348bfc4f53664d6e15fb804902a23a3d','build receipt drift')
 need(H(BASE/'replay.py')=='0c954807b7d8b75d299f4534a246c41fe541395b0d626a8a9a06ed9e512bd8e0','runner drift')
 need(H(MON)=='2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8','monitor drift')
 runner=load(BASE/'replay.py','runner');monitor=load(MON,'monitor')
 src=BASE/'follow-up/FinalWangTableInventory.lean';source_hash=H(src);table=BUILD/'lib/DiophantineConsistency/ArithmeticWangTable.olean'
 need(table.is_file() and not table.is_symlink(),'table is not built regular object')
 direct={};runner.merge_guards(direct,runner.slots(Path(str(table)[:-6])))
 for root in [BUILD/'lib',PKG]:runner.merge_guards(direct,runner.slots(root/'Init'))
 need((PKG/'Init.olean').is_file(),'missing Init');runner.check(direct)
 OUT.mkdir();frozen=OUT/'frozen';frozen.mkdir();snap=frozen/src.name;shutil.copyfile(src,snap);need(H(snap)==source_hash and not snap.is_symlink(),'source mismatch')
 env={'PATH':'/usr/bin:/bin','HOME':'/home/codex','LEAN_PATH':str(BUILD/'lib')+':'+str(PKG)}
 dp=subprocess.run([str(LEAN),'--deps',str(snap)],env=env,text=True,capture_output=True,timeout=120)
 expected={str((PKG/'Init.olean').resolve()),str(table.resolve())};got={str(Path(x).resolve()) for x in dp.stdout.splitlines() if x.strip()};need(dp.returncode==0 and not dp.stderr and got==expected,('dependency mismatch',dp.returncode,dp.stdout,dp.stderr))
 runner.check(direct);cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={frozen}',str(snap),'-o',str(OUT/'FinalWangTableInventory.olean')]
 code,peak,reason=monitor.monitored(cmd,env,OUT/'compiler.log',timeout=120)
 observation={'command':cmd,'compiler_exit':code,'reason':reason,'peak_sampled_rss_bytes':peak,'deps_command':[str(LEAN),'--deps',str(snap)],'deps_stdout':dp.stdout,'source_sha256':source_hash,'table_sha256':H(table),'build_receipt_sha256':H(BUILD/'RESULT.json'),'direct_slots':direct,'scope':'single author exploratory; same build provider, inherited transitive ancestry not authenticated'}
 (OUT/'observation.json').write_text(json.dumps(observation,indent=2)+'\n')
 need(type(code) is int and code==0 and reason is None,('compiler failed',code,reason));text=(OUT/'compiler.log').read_text();need(not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text),'diagnostics rejected')
 reports=runner.report_inventory(snap.read_text(),text);need(len(reports)==29,'report count');runner.check(direct);need(H(snap)==source_hash and not snap.is_symlink(),'final source drift')
 obj=OUT/'FinalWangTableInventory.olean';need(obj.is_file() and not obj.is_symlink(),'bad output');outslots=runner.slots(OUT/'FinalWangTableInventory');need(all((v is not None) if k==str(obj) else v is None for k,v in outslots.items()),'unexpected companion')
 observation.update(status='PASS_AUTHOR_ONLY_FINAL_AXIOM_INVENTORY',reports=reports,output_slots=outslots,compiler_log_sha256=H(OUT/'compiler.log'));(OUT/'observation.json').write_text(json.dumps(observation,indent=2)+'\n');print(json.dumps({'status':observation['status'],'reports':len(reports),'compiler_exit':code,'peak_sampled_rss_bytes':peak,'observation_sha256':H(OUT/'observation.json')},sort_keys=True))
except Exception as exc:
 print('INVENTORY_FAILED',repr(exc),flush=True);traceback.print_exc();sys.exit(1)
