#!/usr/bin/env python3
"""Retained translated-client terminal/provider audit; no Lean invocation."""
import hashlib,json,os,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1]
q=D/'research/p72-p13-p14-translated-fresh';a=q/'attempt01';out=Path('/tmp/p72-p13-p14-translated-fresh-20261105');fresh=Path('/tmp/p72-current-base-extension-attempt02-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='4ff660480d707567c0d2267087f038ecc5b0e3dd62b902238cdf27b687e61223'
assert sha(q/'run.py')=='cfdd0d172f518ba611dd28a4c5dbbe2b5c495c5f66a4cb0216d7af83ee9b5abc'
assert sha(q/'P72Translated.lean')==sha(out/'P72Translated.lean')=='324803ca69036a8731c1bb9a65fd635e8a48d29a998c57023eef8f6f1901691a'
assert sha(out/'P72Translated.olean')=='eaf40d67d9c83a790b2e1cfaada204b0d6d254f3e2eb8605a7b088d9f9e1d8c9'
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['object_sha256']==sha(out/'P72Translated.olean') and s['runner_sha256']==sha(q/'run.py')
outer=json.loads((a/'outer-terminal.json').read_text());assert outer['actual_session']==81196 and outer['exit_code']==0 and outer['observed_output']=='PASS fresh P13/P14 translated consistency\n'
assert s['preflight_before']==s['preflight_after']=={'audit_stdout_sha256':'a8eb52729db2c06ef98cb0b906efed0f63ab492f04a32d0cf40d1c4f6dd5b595'}
for typ,r in zip(('deps','compile'),s['runs']):
 assert r['exit']==0 and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids']
 assert sha(a/(typ+'.txt'))==sha(out/(typ+'.txt'))==r['log_sha256']
assert len(s['runs'])==2
for path,v in s['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:
  p=Path(path);assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256']
for dep,v in s['dependencies'].items():assert Path(v['path']).is_file() and str(Path(v['path']).resolve())==v['realpath'] and sha(v['path'])==v['sha256']
n='DiophantineConsistency.Compact44.IPRAOrdinary72P14';assert set(s['dependencies'])=={'Init',n}
assert s['dependencies'][n]['path']==str(fresh/'lib/DiophantineConsistency/Compact44/IPRAOrdinary72P14.olean') and s['dependencies'][n]['sha256']=='ca06ffe7d590b250f7585ae75f7aa4a8d9c6e8a12b14096dc56ec55caeed41aa'
assert sha(fresh/'lib/DiophantineConsistency/Compact44/IPRAOrdinary72.olean')=='ef08b9c68b1f7a770f698b14fc65d221c7db399d924b69c9a3aa9e978464a48a'
text=(a/'compile.txt').read_text();reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text)
assert [k for k,_ in reports]==['DiophantineConsistency.P72Translated.standard_translated_p13','DiophantineConsistency.P72Translated.standard_translated_p14']
assert all(set(x.strip() for x in v.split(','))=={'propext','Classical.choice','Quot.sound'} for _,v in reports)
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_REVIEW_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':sha(out/'P72Translated.olean'),'outer_receipt_sha256':sha(a/'outer-terminal.json'),'recorded_session':outer['actual_session'],'recorded_outer_exit':outer['exit_code'],'guard_slots':len(s['direct_guard']),'axiom_report_names':[k for k,_ in reports],'scope':'Retained and live direct provider point observations; no Lean replay or independent historical outer-session observation.'},indent=2,sort_keys=True))
