#!/usr/bin/env python3
"""Read fresh terminal artifacts only; no delivered imports or replay."""
from pathlib import Path
import hashlib,json
P=Path('/tmp/zfc-intake196/scanner/extracted/ZFC_217_Scanner_Source_Research_2026-10-21')
R=Path('/tmp/zfc-intake196/source157-execution/run1')
O=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=json.loads((R/'actual.json').read_text());plan=json.loads((O/'replay-plan.json').read_text());checks=[]
def ck(ok,n):
 if not ok:raise AssertionError(n)
 checks.append(n)
ck(a['status']=='PASS_ALL_SIX_SELECTED'and len(a['jobs'])==6,'terminal six-leaf census')
ck(a['optimization']==0,'assertions enabled')
ck(a['plan_sha256']==sha(O/'replay-plan.json')and a['runner_sha256']==sha(O/'run_selected.py'),'actual plan and runner hashes')
ck(a['original_inputs']=={x['path']:x['sha256']for x in plan['inspected_closure']+plan['selected_data']},'all original selected pins')
ck(a['after_inputs']==a['adapted_inputs']and a['inputs_unchanged']is True,'all adapted source/data remained unchanged')
changed=[k for k in a['original_inputs']if a['original_inputs'][k]!=a['adapted_inputs'][k]]
ck(changed==['source-layout/verify_sources.py'],'only approved adapter changed')
pairs={'scanner-local':'proofs/scanner/certificate.json','literal-packet':'verification/packet.json','restricted-L-matrices':'formalism/matrices/receipt.json','seed-reflexivity':'formalism/seed/seed_reflexivity_receipt.json','local7-source-counterexample':'formalism/source_counterexample/receipt.json','source-recodings':'source-layout/receipts/verification.json'}
results={};records=[]
for j in a['jobs']:
 name=j['name'];p=Path(j['result']);x=json.loads(p.read_text());old=json.loads((P/pairs[name]).read_text());results[name]=x
 ck(j['status']=='PASS'and j['exit_code']==0 and j['seconds']<j['timeout_seconds']==120,'bounded process '+name)
 ck(sha(p)==j['result_sha256'],'actual result pin '+name)
 for stream in ['stdout','stderr']:
  ck(sha(Path(j[stream]))==j[stream+'_sha256'],'raw '+stream+' '+name)
 ck(not Path(j['stderr']).read_bytes(),'empty stderr '+name)
 ck(x==old,'every JSON field agrees with delivered receipt '+name)
 ck(j['environment_overrides']=={'PYTHONOPTIMIZE':'','PYTHONDONTWRITEBYTECODE':'1'},'assertion environment '+name)
 records.append(dict(name=name,seconds=j['seconds'],result_sha256=sha(p),delivered_result_json_equal=True,semantic_gates=j['semantic_gates']))
# Independent compact semantic cross-check, separate from the runner's gate code.
x=results['literal-packet'];s=x['short_scanner_startup'];f=x['short_scanner_counterexample']
ck((s['steps'],s['earlier_complete_nonroot_frames'],len(s['one_cells']),len(s['spares']))==(104082,30,139,59),'full-startup result and intermediate distinction')
ck(set(f['expected_one_cells'])^set(f['actual_one_cells'])=={12,14},'wrong address is exact two-cell difference')
x=results['source-recodings'];ck(len(x['records'])==6 and all(r['no_stray_suffix_checks']==6176 for r in x['records']),'all 37056 guarded no-stray checks')
ck([r['metrics']['maximum_depth']for r in x['records']]==[45,47,43,43,43,43],'exact source depth census')
x=results['seed-reflexivity'];ck(sum(x['rules'].values())==79 and x['rules']['mp']==40 and x['rules']['gen']==1,'closed derivation rule census')
x=results['restricted-L-matrices'];ck([m['excluded_gated_bundle_counterexample']['value']for m in x['matrices']]==[1,2],'neither fragment model validates full bundle')
ck(sum(len(j['semantic_gates'])for j in a['jobs'])==45,'runner semantic gate count')
review=dict(status='ACTUAL_ARTIFACT_REVIEW_PASS',role='drop_contract authored the runner and performed this separate read-only artifact audit; this is not an independent second-agent peer.',actual=dict(path=str(R/'actual.json'),sha256=sha(R/'actual.json')),checks=len(checks),check_labels=checks,jobs=records,source_scope='Six selected inexpensive ordinary certificates/counterexamples. All fresh JSON values equal delivered receipts. No old full runtime, search, wrapper, delivery-manifest or proof-assistant execution.',history='Own runner draft1 failed AST parse before execution; preserved under source157-review/history/runner-draft1. No delivered check failed.',source_boundaries=['Scanner proof still requires non-scanner77/1 preservation.','Wrong ordinal40 return refutes source-interface equivalence, not every possible blank-run calibration.','Seed theorem uses inherited strong compiler and calibrated native calculus.','Matrices exclude the exact gated bundle.','Six source recodings have no physical allocation/runtime acceptance.'])
(O/'actual-review.json').write_text(json.dumps(review,indent=2)+'\n')
print(json.dumps({'status':review['status'],'checks':len(checks),'actual_sha256':review['actual']['sha256'],'review_sha256':sha(O/'actual-review.json')},indent=2))
