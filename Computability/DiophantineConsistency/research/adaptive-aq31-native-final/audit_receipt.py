#!/usr/bin/env python3
"""Rehash the matched focused replay; this is not another Lean replay."""
import hashlib,json,os,re
from pathlib import Path
root=Path(__file__).resolve().parents[2]
packet=root/'reviews/adaptive-aq31-native-final-replay'
receipt_path=packet/'receipt.json'; observation_path=packet/'terminal-observation.json'
manifest_path=root/'research/adaptive-aq31-native-final/manifest.json'
receipt=json.loads(receipt_path.read_text()); observation=json.loads(observation_path.read_text()); manifest=json.loads(manifest_path.read_text())
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(ok,detail):
    if not ok: raise ValueError(detail)
def guard(paths):
    for name,entry in paths.items():
        p=Path(name)
        if entry is None: require(not os.path.lexists(p),('unexpected companion',name))
        else: require(p.is_file() and str(p.resolve())==entry['realpath'] and sha(p)==entry['sha256'],('companion mismatch',name))
require(receipt['status']=='MATCHED_PASS' and len(receipt['runs'])==2,'status')
require(observation=={'tool_session':21337,'observed_exit_code':0,'observed_stdout':'MATCHED_PASS 23 rows','receipt_sha256':sha(receipt_path)},'actual process observation')
require(sha(manifest_path)==receipt['manifest_sha256'] and sha(root/'research/adaptive-aq31-native-final/replay.py')==receipt['driver_sha256'],'input identity')
for p,h in receipt['fixed'].items(): require(sha(p)==h,('prior input',p))
guard(receipt['fallback']); require(len(receipt['fallback'])==230,'fallback coverage')
require(receipt['runs'][0]['rows']==receipt['runs'][1]['rows'],'row mismatch')
total_guards=total_reports=0
for run in receipt['runs']:
    overlay=Path(run['run'])/'lib'; rows=run['rows']
    require([r['module'] for r in rows]==manifest['modules'],'row order')
    for row in rows:
        module=row['module']; src=packet/run['label']/'src/DiophantineConsistency'/(module+'.lean'); log=packet/run['label']/'logs'/(module+'.log'); obj=overlay/'DiophantineConsistency'/(module+'.olean')
        require(row['exit']==0 and sha(src)==row['source_sha256']==manifest['sources'][module],('source',module))
        require(sha(log)==row['log_sha256'] and sha(obj)==row['object_sha256'],('output',module))
        if module in receipt['prior_objects']: require(row['object_sha256']==receipt['prior_objects'][module],('rebuilt object',module))
        out=log.read_text(); require(not any(s in out for s in ('error:','warning:','sorryAx')),('log',module))
        reports=re.findall(r"^'[^']+' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",out,re.M|re.S)
        require(len(reports)==manifest['reports'][module],('report count',module,len(reports)))
        for report in reports: require({v.strip() for v in report.split(',') if v.strip()} <= {'propext','Classical.choice','Quot.sound'},('axioms',module,report))
        total_reports+=len(reports)
        for dep,h in row['direct_inputs'].items():
            p=Path(dep); require(sha(p if p.is_absolute() else overlay/p)==h,('direct input',module,dep))
    require(len(run['guards'])==run['guarded_companion_paths'],'guard count');guard(run['guards']);total_guards+=len(run['guards'])
require(len(receipt['prior_objects'])==16 and total_reports==84,'coverage')
result={'status':'PASS','receipt_sha256':sha(receipt_path),'observation_sha256':sha(observation_path),'audit_script_sha256':sha(__file__),'runs':2,'rows_per_run':23,'axiom_reports_total':total_reports,'direct_companion_guards_total':total_guards,'fallback_guards':len(receipt['fallback']),'prior_objects':len(receipt['prior_objects']),'scope':'Read-only receipt, output, direct-input and companion recheck; no separate Lean replay or transitive provenance audit.'}
(packet/'independent-audit.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result,sort_keys=True))
