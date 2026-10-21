#!/usr/bin/env python3
"""Root-authorized selected leaf replay; never executes wrappers or manifests."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,time
P=Path('/tmp/zfc-intake191/K217_Search_Round_2026-10-20/K217_Search_Round_2026-10-20')
D=Path(sys.argv[1]).resolve(); D.mkdir(exist_ok=False)
C=D/'copy';shutil.copytree(P,C);(D/'logs').mkdir()
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
jobs=[
('crossover-source','research217_encoding/crossover30_table.py','research217_encoding/CROSSOVER30_ALLOCATION.json','PREFIX_PASS',60),
('h-pw','research217_native_basis_review/replay_h_pw.py','research217_native_basis_review/H_PW_NATIVE_REPLAY.json','PASS_FIXED_EXPLICIT_SUBSTITUTION_REPLAY',60),
('h-k-p-s','research217_native_basis_review/replay_hkp_s.py','research217_native_basis_review/H_K_P_S_NATIVE_REPLAY.json','PASS_97_EXPLICIT_ROWS_NATIVE_TRANSPORT',60),
('mixed-code4','research217_mixed_tag_basis/check_fixed_code4.py','research217_mixed_tag_basis/FIXED_CODE4_RECEIPT.json','PASS_FIXED_NATIVE_CODE4_PROOF',60),
('codec-scratch','research217_pairing_macros/prove_zero_flow.py','research217_pairing_macros/ZERO_FLOW_PROOF.json','CODEC_INDEPENDENT_SCRATCH_ENTRY_INVARIANT_PASS',60),
('crossover-startup','research217_bootstrap/bind_crossover30.py','research217_bootstrap/crossover30/CONTEXT_BINDING.json','FIRST_CLEAN_ROOT_REACHED',60),
('crossover-ray','research217_bootstrap/prove_crossover_blank_ray.py','research217_bootstrap/crossover30/FOLDED217_BLANK_RAY.json','EXACT_BLANK_OUTWARD_RAY_PROVED',60),
('crossover-runtime','research217_bootstrap/prove_crossover30_tags.py','research217_bootstrap/crossover30/INITIALIZED217_TAG_PROOF.json','ALL_INITIALIZED217_CASES_AND_CONSERVATIVE_TAGS_PASS',300)]
result={'status':'RUNNING','original':str(P),'copy':str(C),'python':sys.executable,'jobs':[],'scope':'Selected new leaves only; no delivered wrapper, checksum manifest, Coq, broad searches, or unchanged primary initialized runtime.'}
env=dict(os.environ);env.pop('PYTHONOPTIMIZE',None);env['PYTHONDONTWRITEBYTECODE']='1'
for name,script,receipt,expected,timeout in jobs:
    dst=C/receipt
    if dst.exists(): dst.unlink()
    cmd=[sys.executable,'-B',str(C/script)]; t=time.monotonic()
    try:
        with (D/'logs'/f'{name}.stdout').open('wb') as out,(D/'logs'/f'{name}.stderr').open('wb') as err:
            p=subprocess.run(cmd,cwd=C,env=env,stdout=out,stderr=err,timeout=timeout)
        code=p.returncode
    except subprocess.TimeoutExpired:code='TIMEOUT'
    record=json.loads(dst.read_text()) if dst.exists() else None
    ok=code==0 and record is not None and record.get('status')==expected
    checks={}
    if name=='crossover-source':checks={'novel_entries_zero':record is not None and record.get('novel_primitive_entry_count')==0,'states218':record is not None and record.get('table_states')==218}
    if name=='crossover-startup':checks={'step312909':record is not None and record.get('blank_endpoint',{}).get('step')==312909,'seed':record is not None and record.get('blank_endpoint',{}).get('clean',{}).get('registers')==[3,0,0,0,3,0,0,0,0]}
    if name=='crossover-runtime':checks={k:record is not None and record.get(k)==v for k,v in {'cases':6167,'rules':1515251,'row_coverage':434,'minimum_duration':12,'unknown_windows':[],'cases_sha256':'24cb25432fd8389c24e293cbe4ef4001f1ad3f50238d6859763509aaeca5809f'}.items()}
    ok=ok and all(checks.values())
    row={'name':name,'argv':cmd,'cwd':str(C),'timeout_seconds':timeout,'exit_code':code,'elapsed_seconds':time.monotonic()-t,'script_sha256':H(C/script),'receipt':receipt,'receipt_sha256':H(dst) if dst.exists() else None,'receipt_status':None if record is None else record.get('status'),'checks':checks,'accepted':ok}
    result['jobs'].append(row);result['status']='RUNNING' if ok else 'FAIL';(D/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(name,row['exit_code'],row['receipt_status'],ok,flush=True)
    if not ok:break
else:result['status']='EIGHT_SELECTED_LEAVES_PASS'
(D/'result.json').write_text(json.dumps(result,indent=2)+'\n')
