"""Portable standalone-program checks plus the essential DI-guard mutant."""
from pathlib import Path
import concurrent.futures
import hashlib
import json
import platform
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[1]
AFFINE=['code/checker.py','code/matched_checker.py','code/readable_checker.py']
OLD=['reference/old_table_matched.py','reference/old_table_plain.py','code/incidental_tokens.py','code/incidental_ast.py']

def run(path,payload,optimized=False,raw=False):
    result=subprocess.run([sys.executable,'-I','-S']+(['-O'] if optimized else [])+[str(path)],input=payload if raw else json.dumps(payload),text=True,capture_output=True,timeout=10)
    accepted=result.returncode==0 and result.stdout=='ACCEPT\n'
    protocol=accepted or result.returncode!=0 and result.stdout=='REJECT\n'
    return dict(accepted=accepted,protocol=protocol,exit_code=result.returncode)

def job(entry):
    program,optimized,case=entry
    result=run(ROOT/program,case['packet'],optimized,case.get('raw',False))
    return dict(program=program,optimized=optimized,case=case['name'],expected=case['accept'],passed=result['protocol'] and result['accepted']==case['accept'],**result)

def main():
    affine=json.loads((ROOT/'tests/affine_cases.json').read_text())
    old=json.loads((ROOT/'tests/source_cases.json').read_text())['cases']
    malformed=[dict(name=n,packet=p,accept=False,raw=True) for n,p in [('empty_input',''),('invalid_json','['),('object_root','{}'),('scalar_root','0'),('string_root','"abc"'),('null_root','null'),('boolean_root','true')]]
    jobs=[(p,o,c) for p in AFFINE for o in [False,True] for c in affine+malformed]
    jobs += [(p,o,c) for p in OLD for o in [False,True] for c in old+malformed]
    with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:rows=list(pool.map(job,jobs))
    bad=next(c['packet'] for c in affine if c['name']=='new_junk_bottom_fake_DI')
    text=(ROOT/'code/checker.py').read_text();needle='i(*a[2:], t=t, d=2)'
    if text.count(needle)!=1:raise ValueError('The exact DI guard changed; review the negative control.')
    with tempfile.TemporaryDirectory() as temporary:
        mutant=Path(temporary)/'deliberately_unsound_no_arity_guard.py'
        mutant.write_text(text.replace(needle,'i(a[2], t, 2)'))
        guard_control=dict(genuine=run(ROOT/'code/checker.py',bad),mutant=run(mutant,bad))
    guard_passed=(not guard_control['genuine']['accepted'] and guard_control['genuine']['protocol'] and guard_control['mutant']['accepted'] and guard_control['mutant']['protocol'])
    passed=all(r['passed'] for r in rows) and guard_passed
    receipt=dict(python=platform.python_version(),affine_case_count=len(affine),source_case_count=len(old),malformed_input_count=len(malformed),affine_programs=AFFINE,old_programs=OLD,complete_program_runs=len(rows),guard_runs=2,passed=passed,checker_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in AFFINE+OLD},guard_control=guard_control,results=rows,scope='Finite tests and a deliberate guard-deletion control; not proof-assistant metatheory.')
    (ROOT/'evidence/verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    sentence=(f"The supplied portable replay passed all {len(rows):,} complete-program executions: "
              f"{len(affine)} affine certificate cases, {len(old)} source/control cases, and "
              f"{len(malformed)} malformed-input cases, across three affine implementations and "
              "four source/control profiles, in ordinary and optimized Python modes. "
              "Two additional executions verify that deleting the exact paired-introduction guard "
              "accepts a code for absurdity that the genuine checker rejects. These are finite "
              "software checks, not a formal metatheorem.\n")
    (ROOT/'evidence/validation_summary.tex').write_text(sentence)
    print(json.dumps({k:v for k,v in receipt.items() if k!='results'},indent=2))
    if not passed:
        print(json.dumps([r for r in rows if not r['passed']],indent=2))
        raise SystemExit(1)

if __name__=='__main__':main()
