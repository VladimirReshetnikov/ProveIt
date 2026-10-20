#!/usr/bin/env python3
"""Reviewer-owned bounded serial runner for exactly the reviewed six leaves."""
import hashlib,json,os,signal,subprocess,time
from pathlib import Path
BASE=Path('/tmp/zfc-intake189-opening/execution')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,v):p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
def main():
    plan=json.loads((BASE/'plan.json').read_text()); logs=BASE/'logs';logs.mkdir()
    assert __debug__ and not (BASE/'result.json').exists()
    env=dict(os.environ)
    for x in ('PYTHONPATH','PYTHONOPTIMIZE','PYTHONSTARTUP','PYTHONHOME'):env.pop(x,None)
    env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONHASHSEED']='0'
    def unchanged():return all(sha(Path(x['path']))==x['sha256'] for x in plan['inputs'])
    assert unchanged()
    result={'status':'RUNNING','plan_sha256':sha(BASE/'plan.json'),'scope':plan['scope'],'exclusions':plan['exclusions'],'jobs':[]}
    dump(BASE/'result.json',result)
    for j in plan['jobs']:
        a=logs/(j['name']+'.stdout.log');b=logs/(j['name']+'.stderr.log');start=time.monotonic();timeout=False
        with a.open('xb') as so,b.open('xb') as se:
            p=subprocess.Popen(j['argv'],cwd=plan['cwd'],env=env,stdout=so,stderr=se,start_new_session=True)
            try:code=p.wait(timeout=j['timeout_seconds'])
            except subprocess.TimeoutExpired:
                timeout=True;os.killpg(p.pid,signal.SIGKILL);code=p.wait()
        row={**j,'returncode':code,'timed_out':timeout,'seconds':time.monotonic()-start,'stdout':str(a),'stdout_sha256':sha(a),'stderr':str(b),'stderr_sha256':sha(b),'inputs_unchanged':unchanged()}
        result['jobs'].append(row);dump(BASE/'result.json',result);print(j['name'],code,round(row['seconds'],3),flush=True)
        if code or timeout or not row['inputs_unchanged']:
            result['status']='DIRECT_LEAF_FAILURE';dump(BASE/'result.json',result);raise SystemExit(1)
    result.update(status='FRESH_DIRECT_LEAVES_PASS',inputs_unchanged=unchanged(),total_process_seconds=sum(x['seconds'] for x in result['jobs']))
    dump(BASE/'result.json',result);print(result['status'],flush=True)
if __name__=='__main__':main()
