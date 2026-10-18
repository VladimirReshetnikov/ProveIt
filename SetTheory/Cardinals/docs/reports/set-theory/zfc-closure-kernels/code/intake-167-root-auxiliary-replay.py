#!/usr/bin/env python3
"""Root replay of reviewed finite source-71 auxiliary checks on a fresh copy."""
from pathlib import Path
import hashlib, json, os, shutil, signal, subprocess, time

ROOT = Path('/tmp/zfc244-rotation-aux-replay')
PLAN = Path('/tmp/zfc244-d91a27b462-inspection/intake/auxiliary-replay-plan.json')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not ROOT.exists(), 'Fresh output required'
plan = json.loads(PLAN.read_text())
source = Path(plan['package'])
ROOT.mkdir()
copy = ROOT/'copy'
shutil.copytree(source, copy)
shutil.copyfile(__file__, ROOT/'runner.py')
shutil.copyfile(PLAN, ROOT/'plan.json')
record = dict(status='RUNNING', scope='Finite auxiliary checks and source-family regeneration; no search campaign or proof compiler.', jobs=[], skipped=['logical-certificates: already executed separately', 'selected-conjunction-seed: optional search preparation', 'selected-embedding-seed: optional search preparation'])
def save():
    (ROOT/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
save()
for job in plan['jobs']:
    if job['key'] in {'logical-certificates','selected-conjunction-seed','selected-embedding-seed'}:
        continue
    cwd = copy/job['cwd']
    entry = cwd/job['argv'][2]
    assert sha(entry) == job['entrypoint_sha256'], str(entry)
    start = time.monotonic()
    outpath,errpath = ROOT/(job['key']+'.stdout.log'),ROOT/(job['key']+'.stderr.log')
    timeout = False
    with outpath.open('wb') as out, errpath.open('wb') as err:
        proc = subprocess.Popen(job['argv'],cwd=cwd,stdout=out,stderr=err,start_new_session=True)
        try:
            proc.wait(timeout=job['proposed_process_group_timeout_seconds'])
        except BaseException as ex:
            try: os.killpg(proc.pid,signal.SIGKILL)
            except ProcessLookupError: pass
            proc.wait()
            timeout = isinstance(ex,subprocess.TimeoutExpired)
            if not timeout: raise
    row = dict(key=job['key'], command=job['argv'], cwd=str(cwd), seconds=time.monotonic()-start, timeout_seconds=job['proposed_process_group_timeout_seconds'], timed_out=timeout, exit_code=proc.returncode, entrypoint_sha256=sha(entry), stdout=str(outpath), stdout_sha256=sha(outpath), stderr=str(errpath), stderr_sha256=sha(errpath), scope=job['scope'])
    if job['key']=='printed-table':
        row['required_output_present']='PASS_PRINTED_244_STATE_TABLE' in outpath.read_text()
    record['jobs'].append(row)
    save()
    print(job['key'],proc.returncode,round(row['seconds'],3),flush=True)
    if proc.returncode or timeout or row.get('required_output_present') is False:
        record['status']='FAIL';save();raise SystemExit(1)
record['status']='PASS_COMMANDS_PENDING_INDEPENDENT_OUTPUT_REVIEW'
save()
print(ROOT/'verification.json',flush=True)
