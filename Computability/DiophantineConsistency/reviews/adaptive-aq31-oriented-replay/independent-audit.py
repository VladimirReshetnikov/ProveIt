#!/usr/bin/env python3
"""Recheck focused replay receipts, outputs, direct inputs and companion guards."""
import hashlib
import json
import os
import re
import sys
from pathlib import Path

root = Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency')
name = sys.argv[1]
if name != 'adaptive-aq31-oriented-replay':
    raise ValueError('unsupported packet')
packet = root / 'reviews' / name
receipt_path = packet / 'receipt.json'
obs_path = packet / 'terminal-observation.json'
receipt = json.loads(receipt_path.read_text())
obs = json.loads(obs_path.read_text())
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(ok, msg):
    if not ok:
        raise ValueError(msg)
require(receipt['status']=='MATCHED_PASS' and len(receipt['runs'])==2, 'receipt state')
require(obs['observed_exit_code']==0 and obs['observed_stdout']==f"MATCHED_PASS {len(receipt['runs'][0]['rows'])} rows", 'terminal observation')
require(receipt['runs'][0]['rows']==receipt['runs'][1]['rows'], 'row comparison')
total_guards=0; total_reports=0
for run in receipt['runs']:
    overlay=Path(run['run'])/'lib'
    for row in run['rows']:
        module=row['module']
        source=packet/run['label']/'src'/'DiophantineConsistency'/(module+'.lean')
        log=packet/run['label']/'logs'/(module+'.log')
        obj=overlay/'DiophantineConsistency'/(module+'.olean')
        require(row['exit']==0 and sha(source)==row['source_sha256']==receipt['base']['sources'][module], ('source',module))
        require(sha(obj)==row['object_sha256'] and sha(log)==row['log_sha256'], ('object/log',module))
        output=log.read_text()
        require(not any(x in output for x in ('error:', 'warning:', 'sorryAx')), ('log',module))
        reports=re.findall(r"^'[^']+' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",output,re.M|re.S)
        for report in reports:
            require({v.strip() for v in report.split(',') if v.strip()} <= {'propext','Classical.choice','Quot.sound'}, ('axiom',module,report))
        total_reports+=len(reports)
        for dep,h in row['direct_inputs'].items():
            p=Path(dep)
            require(sha(p if p.is_absolute() else overlay/p)==h, ('direct input',module,dep))
    require(len(run['guards'])==run['guarded_companion_paths'], 'guard count')
    for path,rec in run['guards'].items():
        p=Path(path)
        if rec is None:
            require(not os.path.lexists(p), ('new companion',path))
        else:
            require(p.is_file() and str(p.resolve())==rec['realpath'] and sha(p)==rec['sha256'], ('companion drift',path))
    total_guards+=len(run['guards'])
expected_rows=5
expected_reports=10
require(len(receipt['runs'][0]['rows'])==expected_rows and total_reports==expected_reports, 'counts')
result={'status':'PASS','packet':name,'receipt_sha256':sha(receipt_path),'observation_sha256':sha(obs_path),'audit_script_sha256':sha(__file__),'runs':2,'rows_per_run':expected_rows,'axiom_reports_total':total_reports,'guard_paths_total':total_guards,'scope':'Read-only receipt, output and direct-companion recheck; no Lean replay or transitive provenance audit.'}
(packet/'independent-audit.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result,sort_keys=True))
