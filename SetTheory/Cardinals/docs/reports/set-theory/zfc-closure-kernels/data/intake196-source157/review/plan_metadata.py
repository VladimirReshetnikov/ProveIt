#!/usr/bin/env python3
"""Create an unexecuted selected replay plan from inspected source/data."""
from pathlib import Path
import json,hashlib,ast
P=Path('/tmp/zfc-intake196/scanner/extracted/ZFC_217_Scanner_Source_Research_2026-10-21')
O=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
S=['proofs/scanner/check_scanner.py','code/check_packet.py','formalism/matrices/check_restricted_L.py','formalism/seed/check_seed_reflexivity.py','formalism/source_counterexample/check_local7_source.py','source-layout/verify_sources.py','source-layout/source_language.py']
inputs=['inputs/provenance.json','inputs/primary218.native.tm','inputs/dominated218.native.tm','inputs/primary-sites.json','inputs/dominated-sites.json','experiments/rejected-short-scanner217.native.tm','experiments/rejected-scanner-relay217.native.tm','experiments/rejected-equality-relay220.native.tm','formalism/seed/seed_reflexivity_proof.json']+[f'source-layout/data/{x}.json'for x in ['dominated203','seed205','zero5_walk206','zero5_dp0','zero5_dp1','zero5_dp2','zero5_dp3']]
closure=[]
for x in S:
 p=P/x;t=ast.parse(p.read_text());imports=[]
 for n in ast.walk(t):
  if isinstance(n,ast.Import):imports +=[a.name for a in n.names]
  elif isinstance(n,ast.ImportFrom):imports.append(n.module)
 closure.append(dict(path=x,sha256=sha(p),imports=sorted(set(imports))))
ad=json.loads((O/'adapter.json').read_text())
def job(name,script,args=None,expected=None,output_files=None):
 return dict(name=name,package=str(P),cwd='{COPY}',argv=['python3','-B','{COPY}/'+script]+(args or []),env={'PYTHONOPTIMIZE':'','PYTHONDONTWRITEBYTECODE':'1'},timeout=120,expected=expected,output_files=output_files or [])
jobs=[job('scanner-local','proofs/scanner/check_scanner.py',['{COPY}/inputs/primary218.native.tm','--output','{OUT}/scanner-local.json'],{'status':'EXACT_LOCAL_WHOLE_TAPE_PROOF','cases':3,'steps':[[1,1],[2,4],[3,3]],'whole_tape_under_constrained_cells':True},['{OUT}/scanner-local.json']),job('literal-packet','code/check_packet.py',expected={'status':'PACKET_LITERAL_EVIDENCE_PASS','new_verified_machine':False,'startup_steps':104082,'root_seed':[4,3,0,0,3,0,0,0,0],'wrong_interface_ordinal':40,'old_steps':588,'new_steps':662},output_files=['{COPY}/verification/packet.json']),job('restricted-L-matrices','formalism/matrices/check_restricted_L.py',expected={'status':'PASS','matrices':2,'retained_rows_each':7,'assignments_per_row':27,'S_counterexample':2,'K_counterexample':1,'excluded_full_bundle_values':[1,2]}),job('seed-reflexivity','formalism/seed/check_seed_reflexivity.py',expected={'status':'PASS','closed_proof_nodes':79,'native_conclusion':3}),job('local7-source-counterexample','formalism/source_counterexample/check_local7_source.py',expected={'status':'PASS_SOURCE_COUNTEREXAMPLE','after_replacement_T':5,'after_wrong_MP_T':1,'suffix_halts':True,'binary_run_claim':False}),job('source-recodings','source-layout/verify_sources.py',expected={'status':'EXACT_SOURCE_RECODING_CERTIFICATES_PASS','records':6,'seed_nodes':205,'five_zero_sources':5,'five_zero_nodes':206,'all_leaves':4751,'two_CFG_resolvers':True,'initializer37_equal':True},output_files=['{COPY}/source-layout/receipts/verification.json'])]
jobs[-1]['edits']=[dict(file='source-layout/verify_sources.py',before=ad['exact_removed_text'],after='    # Delivery-manifest replay omitted by intake policy; selected inputs are pinned in the replay plan.\n')]
plan=dict(status='UNEXECUTED_ROOT_SELECTION_PROPOSAL',source=157,package=str(P),jobs=jobs,inspected_closure=closure,selected_data=[dict(path=x,sha256=sha(P/x))for x in inputs],adapter=ad,notes=['Use fresh full package copy; preserve pristine receipts. No delivered wrapper, search, optimizer, old full runtime, compiler, Rocq or manifest execution.','All selected mathematical checkers are standard-library-only; only source-layout imports the inspected local source_language.py.','code/check_packet.py retains its four selected source/input provenance pins. Those are mathematical input identity checks, not a package-wide delivery manifest replay.','Semantic expected fields must be audited in resulting JSON/stdout; zero process exit alone is insufficient.','The nonderivability argument and safe-seed theorem remain ordinary mathematical review beyond their finite certificates.'])
(O/'replay-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
print(json.dumps({'jobs':len(jobs),'source_files':len(closure),'data_files':len(inputs),'plan_sha256':sha(O/'replay-plan.json')},indent=2))
