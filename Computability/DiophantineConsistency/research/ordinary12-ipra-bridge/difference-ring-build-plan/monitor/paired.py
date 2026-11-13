#!/usr/bin/env python3
"""Sequential monitored sibling coordinator; does not itself validate Lean artifacts."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
from path_guard import fresh_output

if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('sampled replay rejects optimized Python and PYTHONOPTIMIZE')

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[2] / 'fresh-project-closure'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()


def checked_builder_kill(terminal_path):
    """Best-effort SIGKILL only when Linux PID, start time, PGID and SID match."""
    try:
        terminal = json.loads(terminal_path.read_text())
        pid, recorded = terminal['pid'], terminal['pid_start_ticks']
        if not isinstance(pid, int) or isinstance(pid, bool) or pid <= 1 or not isinstance(recorded, int) or isinstance(recorded, bool):
            return {'status':'unconfirmed', 'reason':'invalid or absent builder identity'}
        stat = Path(f'/proc/{pid}/stat').read_text().rsplit(') ',1)[1].split()
        if int(stat[19]) != recorded or os.getpgid(pid) != pid or os.getsid(pid) != pid:
            return {'status':'unconfirmed', 'reason':'builder identity or group changed', 'pid':pid}
        os.killpg(pid,signal.SIGKILL)
        return {'status':'sigkill_sent_to_verified_group', 'pid':pid, 'pid_start_ticks':recorded}
    except (OSError,ValueError,IndexError,KeyError,TypeError,json.JSONDecodeError) as exc:
        return {'status':'unconfirmed', 'reason':repr(exc)}


def main():
    if not sys.flags.isolated or not sys.flags.no_site:
        raise RuntimeError('coordinator requires isolated Python startup (-I -S)')
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--snapshot', type=Path, required=True)
    ap.add_argument('--snapshot-sha256', required=True)
    ap.add_argument('--provider-receipt', type=Path, required=True)
    ap.add_argument('--provider-sha256', required=True)
    ap.add_argument('--foundation-input', type=Path, required=True)
    ap.add_argument('--expected-axiom-reports', type=int, required=True)
    ap.add_argument('--builder', type=Path, default=PROJECT / 'rebuild.py')
    ap.add_argument('--comparator', type=Path, default=PROJECT / 'compare.py')
    ap.add_argument('--monitor', type=Path, default=HERE / 'monitor.py')
    ap.add_argument('--reserve-bytes', type=int, default=4*1024**3)
    ap.add_argument('--budget-bytes', type=int, default=512*1024**2)
    ap.add_argument('--interval', type=float, default=1.0)
    ap.add_argument('--grace', type=float, default=2.0)
    a = ap.parse_args()
    if a.expected_axiom_reports < 0:
        raise ValueError('negative axiom report count')
    # Validate input pins and derive protected roots before any output creation.
    snapshot=a.snapshot.resolve(strict=True); provider=a.provider_receipt.resolve(strict=True)
    foundation_input=a.foundation_input.resolve(strict=True)
    builder, comparator, monitor = (p.resolve(strict=True) for p in (a.builder,a.comparator,a.monitor))
    if H(snapshot/'manifest.json')!=a.snapshot_sha256 or H(provider)!=a.provider_sha256:
        raise ValueError('snapshot or provider pin mismatch')
    provider_data=json.loads(provider.read_text())
    protected=[snapshot,provider,foundation_input,builder,comparator,monitor]
    for key in ('root','overlay'):
        value=provider_data.get(key)
        if not isinstance(value,str) or not Path(value).is_absolute() or not Path(value).is_dir():
            raise ValueError(('invalid or missing provider root',key))
        protected.append(Path(value))
    fixed = {str(p):H(p) for p in (builder,comparator,monitor,HERE/'path_guard.py',Path(__file__).resolve(),foundation_input)}
    out=fresh_output(a.output,protected)
    out=fresh_output(out,protected)
    out.mkdir(parents=False, exist_ok=False)
    if out.is_symlink() or out.resolve(strict=True)!=out:raise ValueError('output changed during creation')
    state = {'status':'RUNNING','runs':[], 'fixed_inputs_sha256':fixed,
             'snapshot_sha256':a.snapshot_sha256, 'provider_sha256':a.provider_sha256,
             'scope':'Two sequential sampled monitors and existing comparator; sampled resources are not quotas or continuous guarantees. Comparator and builder determine their own artifact/provenance scope.'}
    state_path = out/'pair-state.json'
    def save():
        temp=out/'pair-state.tmp'
        temp.write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
        os.replace(temp,state_path)
    pending=[]
    previous={}
    def on_signal(signum,_frame):
        pending.append(signum)
    for sig in (signal.SIGINT,signal.SIGTERM):
        previous[sig]=signal.getsignal(sig);signal.signal(sig,on_signal)
    def launch(cmd,log, *, monitor_terminal=None):
        with log.open('xb') as stream:
            proc=subprocess.Popen(cmd,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
            forwarded=False
            comparator_deadline=None
            monitor_deadline=None
            kill_deadline=None
            escalation=None
            while proc.poll() is None:
                if pending and not forwarded:
                    if monitor_terminal is not None:
                        # The monitor forwards its own SIGTERM to the builder's separate group.
                        try:proc.send_signal(signal.SIGTERM)
                        except ProcessLookupError:pass
                        monitor_deadline=time.monotonic()+max(2.0,a.grace+2.0)
                    else:
                        try:os.killpg(proc.pid,signal.SIGTERM)
                        except ProcessLookupError:pass
                        comparator_deadline=time.monotonic()+a.grace
                    forwarded=True
                if monitor_deadline is not None and time.monotonic()>=monitor_deadline:
                    escalation=checked_builder_kill(monitor_terminal)
                    try:os.killpg(proc.pid,signal.SIGKILL)
                    except ProcessLookupError:pass
                    monitor_deadline=None
                    kill_deadline=time.monotonic()+2.0
                if comparator_deadline is not None and time.monotonic()>=comparator_deadline:
                    try:os.killpg(proc.pid,signal.SIGKILL)
                    except ProcessLookupError:pass
                    comparator_deadline=None
                    kill_deadline=time.monotonic()+2.0
                if kill_deadline is not None and time.monotonic()>=kill_deadline:
                    # A task stuck in an uninterruptible kernel wait may not reap;
                    # do not turn a deadline into a false observed exit.
                    if escalation is None:escalation={}
                    escalation['monitor_or_comparator_exit_unobserved']=True
                    break
                time.sleep(.05)
            return proc.returncode,escalation
    save()
    try:
        if H(a.snapshot/'manifest.json')!=a.snapshot_sha256 or H(a.provider_receipt)!=a.provider_sha256:
            raise ValueError('snapshot or provider pin mismatch')
        for label in ('author','peer'):
            if pending:raise InterruptedError(('coordinator signal',pending[0]))
            run_dir=out/label; child=run_dir/'child-output'; monitor_log=out/(label+'-monitor.log')
            builder_cmd=[sys.executable,'-I','-S',str(builder),'--snapshot',str(a.snapshot),'--output',str(child),
                         '--provider-receipt',str(a.provider_receipt),'--snapshot-sha256',a.snapshot_sha256,
                         '--provider-sha256',a.provider_sha256,'--foundation-input',str(a.foundation_input),
                         '--expected-axiom-reports',str(a.expected_axiom_reports)]
            bootstrap="import runpy,sys; from pathlib import Path; p=Path(sys.argv[1]).resolve(strict=True); sys.path.insert(0,str(p.parent)); sys.argv=sys.argv[1:]; runpy.run_path(str(p),run_name='__main__')"
            cmd=[sys.executable,'-I','-S','-c',bootstrap,str(monitor),'--run-dir',str(run_dir),'--reserve-bytes',str(a.reserve_bytes),
                 '--budget-bytes',str(a.budget_bytes),'--interval',str(a.interval),'--grace',str(a.grace)]
            for path in protected:cmd.extend(['--protect',str(path)])
            cmd+=['--']+builder_cmd
            exit_code,escalation=launch(cmd,monitor_log,monitor_terminal=run_dir/'terminal.json')
            terminal_path=run_dir/'terminal.json'; builder_state=child/'state.json'; builder_log=run_dir/'child.log'
            terminal=json.loads(terminal_path.read_text()) if terminal_path.is_file() else None
            built=json.loads(builder_state.read_text()) if builder_state.is_file() else None
            item={'label':label,'monitor_exit':exit_code,'monitor_log':str(monitor_log),'monitor_log_sha256':H(monitor_log),
                  'monitor_terminal':str(terminal_path),'monitor_terminal_sha256':H(terminal_path) if terminal else None,
                  'monitor_status':terminal['status'] if terminal else None,'builder_exit':terminal['outer_exit_code'] if terminal else None,
                  'monitor_escalation':escalation,
                  'builder_state':str(builder_state),'builder_state_sha256':H(builder_state) if built else None,
                  'builder_status':built.get('status') if built else None,
                  'builder_log':str(builder_log),'builder_log_sha256':H(builder_log) if builder_log.is_file() else None}
            state['runs'].append(item);save()
            if pending:raise InterruptedError(('coordinator signal',pending[0]))
            if exit_code!=0 or not terminal or terminal['status']!='EXITED' or terminal['outer_exit_code']!=0 or not built or built.get('status')!='PASS':
                raise RuntimeError(('sibling failed or stopped',label,exit_code,item['monitor_status'],item['builder_exit'],item['builder_status']))
        if pending:raise InterruptedError(('coordinator signal',pending[0]))
        comp_log=out/'comparator.log'
        comp_cmd=[sys.executable,'-I','-S',str(comparator),str(out/'author/child-output/state.json'),str(out/'peer/child-output/state.json')]
        comp_exit,_=launch(comp_cmd,comp_log)
        state['comparison']={'exit':comp_exit,'log':str(comp_log),'log_sha256':H(comp_log)};save()
        if pending:raise InterruptedError(('coordinator signal',pending[0]))
        if comp_exit:raise RuntimeError(('comparator exit',comp_exit))
        comparison=json.loads(comp_log.read_text())
        if comparison.get('status')!='MATCHED_PASS':raise ValueError('comparator did not report matched pass')
        for item in state['runs']:
            for key in ('monitor_log','monitor_terminal','builder_state','builder_log'):
                if H(item[key])!=item[key+'_sha256']:raise ValueError(('recorded artifact changed',item['label'],key))
        if {p:H(p) for p in fixed}!=fixed:raise ValueError('fixed input changed')
        if H(a.snapshot/'manifest.json')!=a.snapshot_sha256 or H(a.provider_receipt)!=a.provider_sha256:raise ValueError('snapshot or provider changed')
        state.update(status='MATCHED_PASS',comparison={**state['comparison'],'result':comparison});save()
        print('MATCHED_PASS',comparison.get('rows'), 'rows',flush=True)
        return 0
    except Exception as exc:
        state.update(status='INTERRUPTED' if pending else 'FAILED',failure=repr(exc));save()
        print(state['status'],repr(exc),flush=True)
        return 1
    finally:
        for sig,old in previous.items():signal.signal(sig,old)


if __name__=='__main__':
    raise SystemExit(main())
