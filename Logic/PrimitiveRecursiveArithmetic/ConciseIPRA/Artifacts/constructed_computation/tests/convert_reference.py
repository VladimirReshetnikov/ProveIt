"""Record canonical conversion of every legacy fixture in the supplied set.

Cases identical to already replayed fixtures reuse the verification receipt.
Only genuinely different converted packets are executed again.
"""
import json
from pathlib import Path
from convert import convert
from verify import run

ROOT=Path(__file__).resolve().parents[1]
old=json.loads((ROOT/'reference/old_witness_cases.json').read_text())['cases']
new={c['name']:c for c in json.loads((ROOT/'tests/cases.json').read_text())['cases']}
receipt=json.loads((ROOT/'evidence/verification.json').read_text())
records=[]
for c in old:
    try:packet=convert(c['packet'])
    except ValueError:
        if c['name'] not in receipt['legacy_counter_shape_negatives_replaced']:raise
        records.append({'case':c['name'],'status':'obsolete_wrapper_case_replaced','passed':True})
        continue
    if packet==new[c['name']]['packet']:
        reused=[r for r in receipt['results'] if r['case']==c['name']]
        if len(reused)!=4 or not all(r['passed'] for r in reused):raise AssertionError(c['name'])
        records.append({'case':c['name'],'status':'identical_to_replayed_new_fixture','passed':True})
    else:
        runs=[{'optimized':opt,**run(ROOT/'code/checker.py',packet,opt)} for opt in (False,True)]
        ok=all(r['protocol'] and r['accepted']==c['accept'] for r in runs)
        records.append({'case':c['name'],'status':'separate_converted_packet','runs':runs,'passed':ok})
        if not ok:raise AssertionError(records[-1])
output={'legacy_cases':len(old),'canonical_translations':sum(r['status']!='obsolete_wrapper_case_replaced' for r in records),
 'identical_packets_reusing_existing_replay':sum(r['status']=='identical_to_replayed_new_fixture' for r in records),
 'additional_cli_runs':sum(len(r.get('runs',[])) for r in records),'records':records,'result':'PASS'}
(ROOT/'evidence/canonical_conversion.json').write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps({k:v for k,v in output.items() if k!='records'},indent=2))
