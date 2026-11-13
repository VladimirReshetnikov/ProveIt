#!/usr/bin/env python3
"""Read-only audit of the retained byte-recipe endpoint run."""
import hashlib,json,os,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/p72-byte-recipe-endpoints-fresh';a=q/'attempt01';out=Path('/tmp/p72-byte-recipe-endpoints-fresh-20261105');fresh=Path('/tmp/p72-current-base-extension-attempt02-20261105');trans=Path('/tmp/p72-p13-p14-translated-fresh-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='e6f65d1b0f174040abe9d64f8d0622395ea75b62217bf7b686e9453b402aa46c'
assert sha(q/'run.py')=='e14af51406e092ebbd40d57f4568afdebd5eb823f3553f98ebc893e528b14bce'
assert sha(q/'P72ByteEndpoints.lean')==sha(out/'P72ByteEndpoints.lean')=='d2920d8dc8bdc492d5390ec39eeb68b9cc164274ac42465dca4d9cbceb0f348f'
assert sha(out/'P72ByteEndpoints.olean')=='eac163b2f9f9833e483be46ba87f3c48b7da6c0b051636dfed441665283d6c93'
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['runner_sha256']==sha(q/'run.py') and s['object_sha256']==sha(out/'P72ByteEndpoints.olean')
o=json.loads((a/'outer-terminal.json').read_text());assert o['actual_session']==37484 and o['exit_code']==0 and o['observed_output']=='PASS fresh P13/P14 byte-recipe endpoints\n'
assert s['preflight_before']==s['preflight_after']=={'audit_stdout_sha256':'a8eb52729db2c06ef98cb0b906efed0f63ab492f04a32d0cf40d1c4f6dd5b595'}
assert len(s['runs'])==2
for typ,r in zip(('deps','compile'),s['runs']):
 assert r['exit']==0 and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids']
 assert sha(a/(typ+'.txt'))==sha(out/(typ+'.txt'))==r['log_sha256']
for p,v in s['direct_guard'].items():
 if v is None:assert not os.path.lexists(p)
 else:assert Path(p).is_file() and str(Path(p).resolve())==v['realpath'] and sha(p)==v['sha256']
for dep,v in s['dependencies'].items():assert Path(v['path']).is_file() and str(Path(v['path']).resolve())==v['realpath'] and sha(v['path'])==v['sha256']
dn='DiophantineConsistency.Compact44.CompactBytePortsModelIff';assert set(s['dependencies'])=={'Init','P72Translated',dn}
assert s['dependencies']['P72Translated']['path']==str(trans/'P72Translated.olean') and sha(trans/'P72Translated.olean')=='eaf40d67d9c83a790b2e1cfaada204b0d6d254f3e2eb8605a7b088d9f9e1d8c9'
obj=fresh/'lib/DiophantineConsistency/Compact44/CompactBytePortsModelIff.olean';assert s['dependencies'][dn]['path']==str(obj) and sha(obj)=='981453496b3e62ebd83849f96aa8f009fe31c74948293a0e637fb585c1d3e1fb'
row=json.loads((fresh/'rows/0609.json').read_text());assert row['status']=='PASS' and row['module']==dn and row['object_sha256']==sha(obj)
reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(a/'compile.txt').read_text())
assert [k for k,_ in reports]==['DiophantineConsistency.P72ByteEndpoints.byteP_eq_ports','DiophantineConsistency.P72ByteEndpoints.translated_p13','DiophantineConsistency.P72ByteEndpoints.translated_p14']
assert all(set(x.strip() for x in v.split(','))=={'propext','Classical.choice','Quot.sound'} for _,v in reports)
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_REVIEW_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':sha(out/'P72ByteEndpoints.olean'),'outer_receipt_sha256':sha(a/'outer-terminal.json'),'author_recorded_session':o['actual_session'],'outer_exit':o['exit_code'],'guard_slots':len(s['direct_guard']),'axiom_report_names':[k for k,_ in reports],'scope':'Retained and live provider point observations; no Lean replay or independent historical outer-session observation.'},indent=2,sort_keys=True))
