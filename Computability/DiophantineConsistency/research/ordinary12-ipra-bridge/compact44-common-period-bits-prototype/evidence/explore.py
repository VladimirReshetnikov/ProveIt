#!/usr/bin/env python3
import hashlib,importlib.util,json,os,shutil,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated:raise RuntimeError('isolated nonoptimized Python required')
ROOT=Path.cwd()/'Computability/DiophantineConsistency';BASE=ROOT/'research/ordinary12-ipra-bridge';OUT=Path('/tmp/compact44-common-period-build');PARENT=Path('/tmp/ipra-direct-symbolic-k-pair-01/author/lib');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');AUDIT=ROOT/'reviews/compact44-direct-symbolic-k-pair-independent-audit/CHECK.json';MONITOR=BASE/'free-j-current-denominator-composition/replay.py';LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');RESERVE=4*1024**3
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
need(H(AUDIT)=='5aecb3c05962fd5f13650899bac9ce6f2406827a8d08f43714ddd2966716a634','parent receipt drift')
a=json.loads(AUDIT.read_bytes());need(a['status']=='PASS_INDEPENDENT_DIRECT_SYMBOLIC_K_PAIR_AUDIT' and a['recorded_outer_exit']==0,'parent audit schema')
receipt=json.loads((BASE/'compact44-direct-symbolic-k-pair-prototype/evidence/receipt.json').read_bytes());need(H(BASE/'compact44-direct-symbolic-k-pair-prototype/evidence/receipt.json')==a['receipt_sha256'],'parent receipt mismatch')
row=next(r for r in receipt['runs'] if r['side']=='author');need(len(row['steps'])==7,'seed rows')
for step in row['steps']:
 obj=(PARENT/Path(*step['module'].split('.'))).with_suffix('.olean');need(obj.is_file() and H(obj)==step['object_sha256'],('parent object drift',str(obj)))
same=json.loads((BASE/'compact44-same-witness-saturation-closure-plan/scan.json').read_bytes())['source_order'];copy=json.loads((BASE/'compact44-period-copy-closure-plan/scan.json').read_bytes())['source_order']
rows=same+copy[:4]+copy[7:]
# period-copy closure rows 7,8,9 are support, copy support and period.
selector=BASE/'compact44-selector-period-prototype/CompactSelectorPeriod.lean';common=Path('/tmp/compact44-common-period-bits-plan/CompactCommonPeriodBits.lean')
rows += [{'module':'DiophantineConsistency.CompactSelectorPeriod','source':str(selector),'source_sha256':'1b01e1c5585ecab636d94624d670354e659eb85bb219f44a482d28114c79a492'},{'module':'DiophantineConsistency.CompactCommonPeriodBits','source':str(common),'source_sha256':'23ab0a6d005f15336abbeae3703ad761979b5fb91eb4def6eee20c6ff75b3711'}]
need(len(rows)==12 and len({r['module'] for r in rows})==12,'unexpected source order')
for x in rows:need(H(x['source'])==x['source_sha256'],('source drift',x['source']))
need(shutil.disk_usage('/tmp').free>=RESERVE,'space below reserve')
need(not (OUT/'lib').exists() and not (OUT/'src').exists(),'fresh exploratory overlay required')
spec=importlib.util.spec_from_file_location('monitor',MONITOR);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor);monitor.overlay(PARENT,OUT/'lib');(OUT/'src').mkdir();env={'PATH':'/usr/bin:/bin','HOME':'/home/codex','LEAN_PATH':str(OUT/'lib')+':'+str(PACKAGE)};steps=[]
for row in rows:
 name=row['module'];stem=name.rsplit('.',1)[1];src=OUT/'src'/(stem+'.lean');obj=OUT/'lib/DiophantineConsistency'/(stem+'.olean');log=OUT/(stem+'.log');need(shutil.disk_usage('/tmp').free>=RESERVE,'space below reserve before '+stem);need(not obj.exists() and not obj.is_symlink(),('target collision',stem));shutil.copyfile(row['source'],src);need(H(src)==row['source_sha256'],('frozen source drift',stem))
 cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={OUT/"src"}',str(src),'-o',str(obj)];code,peak,reason=monitor.monitored(cmd,env,log,timeout=120);step={'module':name,'source_sha256':H(src),'exit':code,'stop_reason':reason,'peak_rss_bytes':peak,'log_sha256':H(log),'free_bytes_after':shutil.disk_usage('/tmp').free,'command':cmd};steps.append(step);(OUT/'progress.json').write_text(json.dumps(steps,indent=2)+'\n');print(json.dumps(step),flush=True)
 need(code==0 and reason is None and 'warning:' not in log.read_text() and 'error:' not in log.read_text() and 'sorryAx' not in log.read_text(),('compiler failure',stem,code,reason));need(obj.is_file() and not obj.is_symlink(),'missing output '+stem);need(step['free_bytes_after']>=RESERVE,'space below reserve after '+stem)
print('EXPLORATORY_COMMON_PERIOD_BUILD_COMPLETED',flush=True)
