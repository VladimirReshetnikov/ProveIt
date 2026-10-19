"""Root intake runner: isolated copies, persistent logs, bounded process groups."""
import argparse
import json
import os
import pathlib
import shutil
import signal
import subprocess
import time

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('plan',type=pathlib.Path)
    parser.add_argument('--output',type=pathlib.Path,required=True)
    args=parser.parse_args()
    plan=json.loads(args.plan.read_text())
    root=args.output.resolve()
    root.mkdir(exist_ok=False,parents=True)
    record={'status':'RUNNING','plan':str(args.plan),'jobs':[]}
    copies={}
    for job in plan['jobs']:
        source=job['source']
        if source not in copies:
            copy=root/('source'+str(source))
            shutil.copytree(job['package'],copy)
            copies[source]=copy
        copy=copies[source]
        folder=root/job['name']
        folder.mkdir()
        out=folder/'result'
        def expand(s):
            return str(s).replace('{COPY}',str(copy)).replace('{OUT}',str(out)).replace('{JOB}',str(folder))
        adaptations=[]
        for edit in job.get('edits',[]):
            path=copy/edit['file']
            before=path.read_text()
            assert before.count(edit['before'])==1,(path,edit['before'])
            after=before.replace(edit['before'],edit['after'])
            path.write_text(after)
            adaptations.append(edit)
        env=os.environ.copy()
        for key in ('PYTHONPATH','PYTHONOPTIMIZE'):
            env.pop(key,None)
        env['PYTHONDONTWRITEBYTECODE']='1'
        env.update({k:expand(v) for k,v in job.get('env',{}).items()})
        command=[expand(s) for s in job['argv']]
        cwd=expand(job.get('cwd','{COPY}'))
        started=time.monotonic()
        with (folder/'stdout.log').open('w') as stdout,(folder/'stderr.log').open('w') as stderr:
            p=subprocess.Popen(command,cwd=cwd,env=env,stdout=stdout,stderr=stderr,start_new_session=True)
            try:
                rc=p.wait(timeout=job.get('timeout',1200))
                status='PASS' if rc in job.get('expected_exit',[0]) else 'FAIL'
            except subprocess.TimeoutExpired:
                os.killpg(p.pid,signal.SIGKILL)
                rc=p.wait()
                status='TIMEOUT'
        entry={'name':job['name'],'source':source,'command':command,'cwd':cwd,
               'status':status,'exit_code':rc,'seconds':time.monotonic()-started,
               'adaptations':adaptations,'stdout':str(folder/'stdout.log'),'stderr':str(folder/'stderr.log')}
        record['jobs'].append(entry)
        (root/'replay.json').write_text(json.dumps(record,indent=2)+'\n')
        print(json.dumps(entry),flush=True)
    record['status']='PASS' if all(j['status']=='PASS' for j in record['jobs']) else 'COMPLETED_WITH_LIMITATIONS'
    (root/'replay.json').write_text(json.dumps(record,indent=2)+'\n')
    print(record['status'],flush=True)

if __name__=='__main__':
    main()
