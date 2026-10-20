#!/usr/bin/env python3
"""Read-only integrity and cross-receipt checks. No received code is executed."""
import hashlib,json,sys
from pathlib import Path
from collections import Counter
assert __debug__ and not sys.flags.optimize
D=Path(__file__).resolve().parent
manifest=json.loads((D/'PROVENANCE.json').read_text())
files=0
for path,entry in manifest.items():
 if path.startswith('upstream:'):continue
 p=D/path
 assert p.is_file(),path
 assert hashlib.sha256(p.read_bytes()).hexdigest()==entry['sha256'],path
 files+=1
R=D/'replay'
def data(s):return json.loads((R/s).read_text())
E='research218_encoding/';A='research218_baseline_audit/'
b=data(E+'RETURN_FULL_RESULT.json')
assert b['status']=='PASS_FULL_UNIVERSAL_RUNTIME' and (b['cases'],b['expected_cases'],b['rows'],b['rules'],b['captures'])==(6167,6167,438,1515040,1432)
assert len(data(E+'RETURN_FULL_CONTRACTS.json'))==1432
assert len(data(E+'RETURN_FULL_CASES.json'))==6167
f=data(E+'COOPERATIVE27_ALL_ACTIONS_CONCRETE.json');assert f['status']=='COMPLETE_CONCRETE_COOPERATIVE27_FILTER'
assert len(f['actions'])==872 and len({tuple(x['action'])for x in f['actions']})==872
counts=Counter(x['status']for x in f['actions']);assert counts=={'CONCRETE_REJECTION':834,'UNKNOWN_CAPPED':38}
assert Counter(x['reason']for x in f['actions']if x['status']=='CONCRETE_REJECTION')=={'first_clean_dispatch':710,'exact_cycle':121,'halt_or_missing_row':3}
assert all(not x['passed_fixtures'] and x['capped_fixtures']==list(range(18)) for x in f['actions']if x['status']=='UNKNOWN_CAPPED')
assert len(f['fixtures'])==len(f['baseline_controls'])==18
for x in f['baseline_controls']:assert x['actual']==f['fixtures'][x['fixture']]['expected']
c=data(E+'COOPERATIVE27_CAP_CERTIFICATES.json')
assert c['status']=='COMPLETE_BOUNDED_CAP_CLASSIFICATION' and (c['proved'],c['unknown'])==(3,35)
assert {tuple(x['action'])for x in c['cases']}=={tuple(x['action'])for x in f['actions']if x['status']=='UNKNOWN_CAPPED'}
assert c['source_receipt_sha256']==hashlib.sha256((R/E/'COOPERATIVE27_ALL_ACTIONS_CONCRETE.json').read_bytes()).hexdigest()
r=data(A+'COOPERATIVE27_COUNTEREXAMPLE_AUDIT.json');assert r['status']=='FOUR_INDEPENDENT_COUNTEREXAMPLE_REPLAYS_PASS'
r=data(A+'COOPERATIVE27_DIVERGENCE_AUDIT.json');assert r['status']=='THREE_INDEPENDENT_DIVERGENCE_CERTIFICATES_ACCEPTED'
assert r['certificate_sha256']==hashlib.sha256((R/E/'COOPERATIVE27_CAP_CERTIFICATES.json').read_bytes()).hexdigest()
for name,n,sites,rules in [('09',115,78,25069),('13',131,90,27613)]:
 r=data(A+f'DIRECT{name}_RUNTIME_PILOT.json')
 assert (r['cases'],r['passed'],r['not_proved'],r['selected_sites'],r['rules_in_passed'])==(n,n,0,sites,rules)
 assert r['table_sha256']==hashlib.sha256((R/E/f'direct_equality_{name}/candidate.native.tm').read_bytes()).hexdigest()
prices=data(E+'ALL_RAW_SOURCE_PRICES.json');assert len(prices)==11
for r in prices:
 assert r['states']==220 and not r['binding_failures']
 assert r['table_sha256']==hashlib.sha256((R/E/r['name']/'candidate.native.tm').read_bytes()).hexdigest()
 assert r['source_sha256']==hashlib.sha256((R/'research218_source'/f"{r['name']}_sites.json").read_bytes()).hexdigest()
T={}
for line in (R/E/'direct_equality_09/candidate.native.tm').read_text().splitlines():
 if line and not line.startswith('#'):
  q,b,w,d,z=line.split();T[int(q),int(b)]=(int(w),d,int(z))
assert [(k,v)for k,v in T.items()if v[2]==303]==[((88,0),(0,'R',303))]
assert [(k,v)for k,v in T.items()if v[2]==122]==[((196,1),(1,'R',122))]
print(json.dumps({'status':'PASS_PACKAGE_INTEGRITY_AND_RECEIPT_CONSISTENCY','frozen_replay_files':files,'source_prices':11,'baseline_cases':6167,'cooperative_family':872,'concrete_rejections':834,'independently_reviewed_near_hits':4,'independently_reviewed_divergences':3,'unknown_actions':35,'scope':'Read-only byte integrity and receipt consistency; not a replay or a new machine theorem.'},indent=2))
