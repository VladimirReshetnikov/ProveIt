#!/usr/bin/env python3
"""Toy the monitored pair coordinator; no Lean or real provider execution."""
import hashlib,json,os
from pathlib import Path
import subprocess,sys,tempfile

HERE=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
BOOT="import runpy,sys; from pathlib import Path; p=Path(sys.argv[1]).resolve(strict=True); sys.path.insert(0,str(p.parent)); sys.argv=sys.argv[1:]; runpy.run_path(str(p),run_name='__main__')"
def isolated(script):return [sys.executable,'-I','-S','-c',BOOT,str(script)]
BUILDER=r'''
import argparse,json,os,pathlib,signal,subprocess,sys,time
assert __debug__ and sys.flags.isolated and sys.flags.no_site and not os.environ.get('PYTHONOPTIMIZE')
p=argparse.ArgumentParser();p.add_argument('--output',required=True);a,_=p.parse_known_args()
out=pathlib.Path(a.output);label=out.parent.name
assert os.environ['MONITOR_OUTPUT']==str(out) and pathlib.Path(os.environ['TMPDIR']).parent==out.parent
with open(os.environ['TOY_TRACE'],'a') as f:f.write('builder:'+label+'\n')
out.mkdir();print('BUILDER',label,flush=True)
if os.environ.get('TOY_HANG')==label:
 signal.signal(signal.SIGTERM,signal.SIG_IGN)
 code='import os,pathlib,signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); pathlib.Path(os.environ["MONITOR_OUTPUT"],"descendant").write_text(str(os.getpid())); time.sleep(60)'
 subprocess.Popen([sys.executable,'-c',code]);time.sleep(60)
if os.environ.get('TOY_BLOAT')==label:
 (out/'large').write_bytes(b'x'*200000);time.sleep(10)
if os.environ.get('TOY_FAIL')==label:sys.exit(7)
(out/'state.json').write_text(json.dumps({'status':'PASS','label':label}))
'''
COMPARATOR=r'''
import json,os,pathlib,sys
assert sys.flags.isolated and sys.flags.no_site
with open(os.environ['TOY_TRACE'],'a') as f:f.write('compare\n')
a,b=[json.loads(pathlib.Path(x).read_text()) for x in sys.argv[1:]]
assert a=={'status':'PASS','label':'author'} and b=={'status':'PASS','label':'peer'}
if os.environ.get('TOY_BAD_COMPARE'):sys.exit(3)
print(json.dumps({'status':'MATCHED_PASS','rows':2}))
'''
STUCK_MONITOR=r'''
import json,os,pathlib,signal,subprocess,sys,time
assert sys.flags.isolated and sys.flags.no_site
signal.signal(signal.SIGTERM,signal.SIG_IGN)
args=sys.argv[1:];run=pathlib.Path(args[args.index('--run-dir')+1]);run.mkdir()
tmp=run/'tmp';tmp.mkdir();out=run/'child-output';env=os.environ.copy();env['MONITOR_OUTPUT']=str(out);env['TMPDIR']=str(tmp)
f=(run/'child.log').open('wb');p=subprocess.Popen(args[args.index('--')+1:],env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
start=int(pathlib.Path(f'/proc/{p.pid}/stat').read_text().rsplit(') ',1)[1].split()[19])
if os.environ.get('TOY_BAD_ID'):start=0
(run/'terminal.json').write_text(json.dumps({'status':'RUNNING','outer_exit_code':None,'pid':p.pid,'pid_start_ticks':start}))
while True:time.sleep(.1)
'''

def run_case(root,name,extra,budget=1000000,interrupt=False,stuck_monitor=False,unconfirmed=False):
    case=root/name;case.mkdir();snapshot=case/'snap';snapshot.mkdir();(snapshot/'manifest.json').write_text('{}')
    provider_dir=case/'provider';provider_dir.mkdir();overlay=provider_dir/'package';overlay.mkdir()
    provider=provider_dir/'provider.json';provider.write_text(json.dumps({'root':str(provider_dir),'overlay':str(overlay)}));foundation=case/'foundation.json';foundation.write_text('{}')
    builder=case/'builder.py';builder.write_text(BUILDER);comp=case/'comparator.py';comp.write_text(COMPARATOR);trace=case/'trace'
    out=case/'run';env=os.environ.copy();env.update(extra);env['TOY_TRACE']=str(trace)
    cmd=isolated(HERE/'paired.py')+['--output',str(out),'--snapshot',str(snapshot),'--snapshot-sha256',H(snapshot/'manifest.json'),
         '--provider-receipt',str(provider),'--provider-sha256',H(provider),'--foundation-input',str(foundation),'--expected-axiom-reports','0',
         '--builder',str(builder),'--comparator',str(comp),'--reserve-bytes','0','--budget-bytes',str(budget),'--interval','.02','--grace','.1']
    if stuck_monitor:
        stuck=case/'stuck_monitor.py';stuck.write_text(STUCK_MONITOR);cmd.extend(['--monitor',str(stuck)])
    if interrupt:
        import signal,time
        p=subprocess.Popen(cmd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        ready=out/'author/child-output/descendant';deadline=time.monotonic()+10
        while not ready.exists() and time.monotonic()<deadline:time.sleep(.02)
        assert ready.exists(); child=int(ready.read_text());p.send_signal(signal.SIGTERM)
        stdout,stderr=p.communicate(timeout=10)
        if unconfirmed:
            # Coordinator deliberately did not signal an unverified group;
            # the toy harness owns and explicitly cleans up this test group.
            terminal=json.loads((out/'author/terminal.json').read_text())
            os.killpg(terminal['pid'],signal.SIGKILL)
        for _ in range(100):
            stat=Path(f'/proc/{child}/stat')
            try:
                if stat.read_text().split(') ',1)[1].split()[0]=='Z':break
            except (FileNotFoundError, ProcessLookupError):
                # Reaping can surface as ENOENT or ESRCH while reading procfs.
                break
            time.sleep(.02)
        else:raise AssertionError('descendant still live after coordinator interruption')
        p.stdout=stdout;p.stderr=stderr
    else:
        p=subprocess.run(cmd,env=env,text=True,capture_output=True,timeout=20)
    return p,json.loads((out/'pair-state.json').read_text()),trace.read_text().splitlines(),out


def main():
    with tempfile.TemporaryDirectory(prefix='ipra-paired-tests-') as tmp:
        root=Path(tmp)
        import paired
        guard=root/'guards';guard.mkdir();snapshot=guard/'snap';snapshot.mkdir();(snapshot/'manifest.json').write_text('{}')
        provider_dir=guard/'provider';provider_dir.mkdir();(provider_dir/'package').mkdir();provider=provider_dir/'provider.json'
        provider.write_text(json.dumps({'root':str(provider_dir),'overlay':str(provider_dir/'package')}))
        foundation=guard/'foundation.json';foundation.write_text('{}')
        builder=guard/'builder.py';builder.write_text(BUILDER);comp=guard/'comparator.py';comp.write_text(COMPARATOR)
        base=isolated(HERE/'paired.py')+['--snapshot',str(snapshot),'--snapshot-sha256',H(snapshot/'manifest.json'),
              '--provider-receipt',str(provider),'--provider-sha256',H(provider),'--foundation-input',str(foundation),
              '--expected-axiom-reports','0','--builder',str(builder),'--comparator',str(comp)]
        link=guard/'link';link.symlink_to(snapshot,target_is_directory=True)
        for destination in (snapshot/'new',provider_dir/'new',link/'new'):
            r=subprocess.run(base+['--output',str(destination)],capture_output=True,text=True)
            assert r.returncode!=0 and not destination.exists()
        bad_out=guard/'bad-pin';bad=base.copy();bad[bad.index('--snapshot-sha256')+1]='0'*64
        r=subprocess.run(bad+['--output',str(bad_out)],capture_output=True,text=True)
        assert r.returncode!=0 and not bad_out.exists() and 'pin mismatch' in r.stderr
        missing=guard/'missing-provider-fields.json';missing.write_text('{}')
        bad=base.copy();bad[bad.index('--provider-receipt')+1]=str(missing);bad[bad.index('--provider-sha256')+1]=H(missing)
        missing_out=guard/'missing-fields-output'
        r=subprocess.run(bad+['--output',str(missing_out)],capture_output=True,text=True)
        assert r.returncode!=0 and not missing_out.exists() and 'invalid or missing provider root' in r.stderr
        optimized=guard/'optimized';env=os.environ.copy();env['PYTHONOPTIMIZE']='1'
        r=subprocess.run(base+['--output',str(optimized)],env=env,capture_output=True,text=True)
        assert r.returncode!=0 and not optimized.exists() and 'rejects optimized' in r.stderr
        print('PASS protected outputs, input pins and optimized launcher rejected before writes',flush=True)
        bogus=root/'bogus-terminal.json';bogus.write_text(json.dumps({'pid':os.getpid(),'pid_start_ticks':0}))
        assert paired.checked_builder_kill(bogus)['status']=='unconfirmed'
        assert paired.checked_builder_kill(root/'missing-terminal.json')['status']=='unconfirmed'
        print('PASS missing or mismatched builder identity remains unconfirmed',flush=True)
        p,s,t,out=run_case(root,'pass',{})
        assert p.returncode==0 and s['status']=='MATCHED_PASS' and t==['builder:author','builder:peer','compare']
        assert [(r['monitor_exit'],r['monitor_status'],r['builder_exit'],r['builder_status']) for r in s['runs']]==[(0,'EXITED',0,'PASS')]*2
        assert s['comparison']['exit']==0 and s['comparison']['result']=={'status':'MATCHED_PASS','rows':2}
        assert p.stdout.strip()=='MATCHED_PASS 2 rows' and not p.stderr
        assert all(Path(r['builder_log']).read_text().startswith('BUILDER') for r in s['runs'])
        print('PASS pair, actual exits and logs',flush=True)
        site=root/'site';site.mkdir();marker=root/'site-marker'
        (site/'sitecustomize.py').write_text('import os,pathlib\npathlib.Path(os.environ["CANARY_MARK"]).write_text("ran")\n')
        env=os.environ.copy();env['PYTHONPATH']=str(site);env['CANARY_MARK']=str(marker)
        control=subprocess.run([sys.executable,'-c','pass'],env=env,capture_output=True,text=True)
        assert control.returncode==0 and marker.read_text()=='ran';marker.unlink()
        p,s,t,out=run_case(root,'site_canary',{'PYTHONPATH':str(site),'CANARY_MARK':str(marker)})
        assert p.returncode==0 and s['status']=='MATCHED_PASS' and not marker.exists()
        assert t==['builder:author','builder:peer','compare']
        print('PASS actual full-chain PYTHONPATH sitecustomize canary blocked',flush=True)
        p,s,t,out=run_case(root,'author_fail',{'TOY_FAIL':'author'})
        assert p.returncode==1 and s['status']=='FAILED' and t==['builder:author'] and len(s['runs'])==1
        assert s['runs'][0]['builder_exit']==7 and s['runs'][0]['monitor_exit']==1 and 'comparison' not in s
        print('PASS author failure prevents peer and comparison',flush=True)
        p,s,t,out=run_case(root,'author_stop',{'TOY_BLOAT':'author'},budget=50000)
        assert p.returncode==1 and s['status']=='FAILED' and t==['builder:author'] and len(s['runs'])==1
        assert s['runs'][0]['monitor_status']=='STOPPED' and 'comparison' not in s
        record=json.loads((out/'author/terminal.json').read_text());assert record['violation']=='logical_size_above_sampled_budget'
        print('PASS sampled stop prevents peer and comparison',flush=True)
        p,s,t,out=run_case(root,'peer_fail',{'TOY_FAIL':'peer'})
        assert p.returncode==1 and s['status']=='FAILED' and t==['builder:author','builder:peer'] and len(s['runs'])==2
        assert s['runs'][1]['builder_exit']==7 and 'comparison' not in s
        print('PASS peer failure prevents comparison',flush=True)
        p,s,t,out=run_case(root,'compare_fail',{'TOY_BAD_COMPARE':'1'})
        assert p.returncode==1 and s['status']=='FAILED' and t==['builder:author','builder:peer','compare'] and s['comparison']['exit']==3
        print('PASS comparator failure retained',flush=True)
        p,s,t,out=run_case(root,'interrupt',{'TOY_HANG':'author'},interrupt=True)
        assert p.returncode==1 and s['status']=='INTERRUPTED' and t==['builder:author'] and 'comparison' not in s
        assert s['runs'][0]['monitor_status']=='STOPPED' and s['runs'][0]['builder_exit'] is not None
        assert json.loads((out/'author/terminal.json').read_text())['violation']=='interrupt_signal_15'
        print('PASS coordinator interruption terminates monitored descendant',flush=True)
        p,s,t,out=run_case(root,'stuck_monitor',{'TOY_HANG':'author'},interrupt=True,stuck_monitor=True)
        assert p.returncode==1 and s['status']=='INTERRUPTED' and t==['builder:author'] and 'comparison' not in s
        assert s['runs'][0]['monitor_exit']==-9 and s['runs'][0]['builder_exit'] is None
        assert s['runs'][0]['monitor_escalation']['status']=='sigkill_sent_to_verified_group'
        print('PASS stalled monitor escalates verified builder group and reports unobserved builder exit',flush=True)
        p,s,t,out=run_case(root,'unconfirmed_monitor',{'TOY_HANG':'author','TOY_BAD_ID':'1'},interrupt=True,stuck_monitor=True,unconfirmed=True)
        assert p.returncode==1 and s['status']=='INTERRUPTED' and s['runs'][0]['monitor_exit']==-9
        assert s['runs'][0]['builder_exit'] is None and s['runs'][0]['monitor_escalation']['status']=='unconfirmed'
        print('PASS unverified builder remains unconfirmed and toy harness cleans up',flush=True)
    print('PASS_PAIRED_TOY_CONTROLS',flush=True)
if __name__=='__main__':main()
