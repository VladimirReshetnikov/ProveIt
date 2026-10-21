#!/usr/bin/env python3
"""Offline reproduction of K217. Python 3.10+, standard library, assertions on.

Default: authenticated parent logic/source, exact construction, independent
source/fold/full-startup audits, and stored universal-receipt inventory.
--runtime additionally regenerates every quantified physical derivation.
"""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys, tempfile, time, zipfile

ROOT = Path(__file__).resolve().parent
PARENT = 'K218_Dominated_Rho8_2026-10-20'
PARENT_SHA = '080b4fe855c109ab77588c01c9e012d9572afa7721682306370ccb2eb22cbea9'

def need(ok, message):
    if not ok:
        raise ValueError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def execute(label, script, args, out):
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    cmd = [sys.executable, '-B', str(script), *map(str,args)]
    log = out/(label+'.log')
    with log.open('w', encoding='utf-8') as stream:
        result = subprocess.run(cmd, cwd=script.parent, env=env,
                                stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        print(log.read_text()[-12000:], file=sys.stderr)
        raise RuntimeError(label+' failed; see '+str(log))
    print(label+': PASS', flush=True)

def check_manifest():
    manifest = json.loads((ROOT/'manifest.json').read_text())
    for name, info in manifest['files'].items():
        p = ROOT/name
        need(p.is_file(), 'Missing packaged file: '+name)
        need(p.stat().st_size == info['bytes'] and digest(p) == info['sha256'],
             'Packaged bytes changed: '+name)
    print('package_integrity: PASS ('+str(len(manifest['files']))+' files)', flush=True)
    return len(manifest['files'])

def unpack_parent(where):
    archive = ROOT/'dependency'/(PARENT+'.zip')
    need(digest(archive) == PARENT_SHA, 'Wrong parent archive')
    where.mkdir(parents=True,exist_ok=True)
    with zipfile.ZipFile(archive) as z:
        for info in z.infolist():
            n = Path(info.filename)
            need(not n.is_absolute() and '..' not in n.parts,
                 'Unsafe archive path')
            need(n.parts and n.parts[0] == PARENT, 'Unexpected parent archive root')
            need((info.external_attr >> 16) & 0o170000 != 0o120000,
                 'Unexpected symlink in parent archive')
        z.extractall(where)
    return where/PARENT

def verify(out, runtime):
    out.mkdir(parents=True, exist_ok=True)
    begun = time.monotonic()
    count = check_manifest()
    with tempfile.TemporaryDirectory(prefix='proveit_k217_dependency_') as tmpname:
        tmp = Path(tmpname)
        upstream = unpack_parent(tmp/'dependency')
        execute('inherited_logic_source_and_startup',upstream/'verify_all.py',[],out)
        machine = ROOT/'machine'
        rebuilt = tmp/'reconstructed'
        execute('deterministic_construction',ROOT/'code/construct217.py',[
            '--baseline-table',machine/'baseline218.native.tm',
            '--baseline-source',machine/'baseline_sites218.json',
            '--output',rebuilt],out)
        for name in ['k217.native.tm','k217.tm','prefold218.native.tm','sites217.json']:
            need((rebuilt/name).read_bytes() == (machine/name).read_bytes(),
                 'Reconstruction differs: '+name)
        shutil.copyfile(rebuilt/'reconstruction.json',out/'reconstruction.json')
        execute('independent_source_and_full_startup',ROOT/'code/audit217.py',[
            '--input',machine,'--output',out/'independent_source_startup.json'],out)
        execute('independent_four_case_fold',ROOT/'code/check_fold217_four_cases.py',[
            '--old',machine/'prefold218.native.tm','--new',machine/'k217.native.tm',
            '--output',out/'independent_fold.json'],out)
        execute('independent_calibration_local_audit',ROOT/'code/review_k217.py',[
            ROOT,'--output',out/'independent_review.json'],out)
        execute('optional_fixed_core_source',ROOT/'appendix/fixed_core/verify_fixed_core.py',[
            ROOT/'appendix/fixed_core','--output',out/'fixed_core_source.json'],out)
        # Rebuild the typeset table in scratch, without changing the report source.
        execute('complete_table_appendix',ROOT/'code/make_table_tex.py',[
            '--table',machine/'k217.tm','--output',tmp/'full_table.tex'],out)
        need((tmp/'full_table.tex').read_bytes() == (ROOT/'appendix/full_table.tex').read_bytes(),
             'Typeset appendix differs from the canonical machine')
        common = ['--upstream',upstream,'--table',machine/'k217.native.tm',
                  '--sites',machine/'sites217.json']
        execute('runtime_receipt_audit',ROOT/'code/verify_runtime217.py',[
            *common,'--out',out/'runtime_receipt_audit','--receipt-only',
            '--receipts',ROOT/'evidence/runtime'],out)
        if runtime:
            execute('complete_symbolic_runtime_replay',ROOT/'code/verify_runtime217.py',[
                *common,'--out',out/'runtime_replay'],out)
            # Both are already independently byte-pinned by the runtime driver.
            for name in ['runtime_cases.json','startup.json']:
                need((out/'runtime_replay'/name).read_bytes() ==
                     (ROOT/'evidence/runtime'/name).read_bytes(),
                     'Regenerated receipt differs: '+name)
    result = {
        'status':'ALL_REQUESTED_K217_CHECKS_PASS',
        'working_states':217,'transition_rows':434,
        'native_sha256':digest(ROOT/'machine/k217.native.tm'),
        'canonical_sha256':digest(ROOT/'machine/k217.tm'),
        'source_sha256':digest(ROOT/'machine/sites217.json'),
        'authenticated_files':count,'guarded_cases':6176,'blank_startup_steps':312617,
        'quantified_runtime_recomputed':runtime,
        'proof_status':'Ordinary mathematical proof with executable induction certificates; no newly compiled exact-K217 proof-assistant endpoint.',
        'seconds':round(time.monotonic()-begun,3),
    }
    (out/'verification_summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)

def main():
    need(__debug__ and not sys.flags.optimize,
         'Assertions are required: disable -O/-OO and PYTHONOPTIMIZE.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--runtime',action='store_true',help='Regenerate all quantified runtime proofs')
    ap.add_argument('--output',type=Path,help='Directory for persistent local replay receipts')
    a = ap.parse_args()
    if a.output:
        out = a.output.resolve()
        need(out != ROOT and ROOT not in out.parents,
             'Choose a replay output directory outside the authenticated package.')
        verify(out,a.runtime)
    else:
        with tempfile.TemporaryDirectory(prefix='proveit_k217_verify_') as d:
            verify(Path(d),a.runtime)

if __name__ == '__main__':
    main()
