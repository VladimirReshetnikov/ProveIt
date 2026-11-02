#!/usr/bin/env python3
"""Sequential bounded suffix rebuild over the audited matched current parent."""
import argparse
import ctypes
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('optimized Python rejected')
HERE = Path(__file__).resolve().parent
BASE = HERE.parent
PARENT_SCRIPT = BASE/'free-j-signed-transport-prototype/replay.py'
PARENT_SCRIPT_SHA = '7623f0a2029094648d3454bcd8bc358ca37dffd2719f0156bb1a813ed7116bca'
AUDIT = HERE.parents[2]/'reviews/ordinary12-coexistence-pair-independent-audit/CHECK.json'
AUDIT_SHA = '5f1fc7a6f519088588ed568e3266da6d109490d556d459a7949d257cbb1bc11d'
SOURCES = [
 ('free-j-first-divisibility-prototype/FreeJRootBinding.lean','5d826d8f1cf5ce4a11c45f4a6762ba0729a5e282a1356bce0aeb02f49c58083b',7),
 ('free-j-first-transport-prototype/FreeJFirstTransport.lean','4093c3e18c6a6b40d6c0af0149fa4c0c16a03fa57b1566f17402eb286176bec8',1),
 ('free-j-main-rank-congruence-prototype/FreeJMainOrientation.lean','638cc292fc131768a3f25168e5733eebe0048174f3635bb8056985a196de42b1',8),
 ('free-j-pell-indices-prototype/FreeJPellIndices.lean','8d222d5302d22c914694dbe36478870af9358b0a26046a8135a0b26c1ac4bf72',1),
 ('free-j-early-window-prototype/FreeJEarlyWindow.lean','d94fc03938028ece937495de5b376bc13c71330b9502ddc235fb96fa4c4048bb',1),
 ('free-j-early-index-prototype/FreeJEarlyIndex.lean','4f78abd78a895cc3d4e672e618d343b5e4c053a6489aba09bc5c9a20c7741adc',2),
 ('free-j-index-comparison-prototype/FreeJIndexComparison.lean','2b00bc90f94de730da50d856a5af7052918081992988464dc4d30a664d8683e4',2),
 ('free-j-early-size-prototype/FreeJEarlySize.lean','0e670e6d0cd8431893b5ccf3267d9857eb8d7301af0acb49acb04433e07c44fb',1),
 ('free-j-graph-vbound-prototype/FreeJGraphVBound.lean','1737e236991405073c78079c4b529ca67296ec7f72dd74006592ad98b7354795',5),
 ('free-j-denominator-prototype/FreeJDenominator.lean','898b9fa159ba784cc32b71e639a159d785d14e67096aee18a8df07740e23b8a3',7),
 ('free-j-signed-transport-prototype/FreeJSignedTransport.lean','dd2608fd773126ebe37cb0bd921fcb4cc06467e36e4be61aff050fa40dc2a116',3),
 ('free-j-current-denominator-composition/FreeJCurrentDenominator.lean','ce8188f5a19a58415cbe84cda4e15947cef0b054faa54710439542a832d302db',3),
]
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

def check_sources():
    if H(PARENT_SCRIPT)!=PARENT_SCRIPT_SHA or H(AUDIT)!=AUDIT_SHA:
        raise ValueError('parent script/audit drift')
    audit=json.loads(AUDIT.read_text())
    if audit.get('status') != 'PASS_INDEPENDENT_70_SOURCE_COEXISTENCE_ARTIFACT_AUDIT':
        raise ValueError(('independent parent audit status',audit.get('status')))
    for rel,sha,_ in SOURCES:
        if H(BASE/rel)!=sha: raise ValueError(('source drift',rel))

def overlay(base,dest):
    for root,dirs,files in os.walk(base,followlinks=False):
        root=Path(root); out=dest/root.relative_to(base);out.mkdir(parents=True,exist_ok=True)
        for name in list(dirs):
            if (root/name).is_symlink():
                (out/name).symlink_to(root/name);dirs.remove(name)
        for name in files:(out/name).symlink_to(root/name)

def rss_bytes(pid):
    try:
        for line in Path(f'/proc/{pid}/status').read_text().splitlines():
            if line.startswith('VmRSS:'): return int(line.split()[1])*1024
    except (FileNotFoundError, ProcessLookupError):
        return None
    return None


def ensure_subreaper():
    # Linux PR_SET_CHILD_SUBREAPER: descendants orphaned by a terminated
    # compiler are reparented to this wrapper and can be reaped here.
    libc=ctypes.CDLL(None,use_errno=True)
    if libc.prctl(36,1,0,0,0) != 0:
        raise OSError(ctypes.get_errno(),'cannot establish child subreaper')


def terminate_verified_group(proc, identity_verified, grace=0.5):
    """TERM/KILL the verified child session and wait for its leader.

    PID/process-group identity checks are not atomic pidfds; descendants that
    deliberately escape the group are outside this control.
    """
    if not identity_verified:
        raise RuntimeError('cannot safely signal an unverified process group')
    try: os.killpg(proc.pid,signal.SIGTERM)
    except ProcessLookupError: pass
    deadline=time.monotonic()+grace
    while time.monotonic()<deadline:
        proc.poll()
        try: os.killpg(proc.pid,0)
        except ProcessLookupError: break
        time.sleep(0.02)
    try: os.killpg(proc.pid,signal.SIGKILL)
    except ProcessLookupError: pass
    result=proc.wait(timeout=5)
    deadline=time.monotonic()+5
    while True:
        try:
            child,_=os.waitpid(-proc.pid,os.WNOHANG)
        except ChildProcessError:
            break
        if child == 0:
            if time.monotonic()>=deadline:
                raise RuntimeError('verified group descendants not reaped')
            time.sleep(0.02)
    return result


def monitored(cmd,env,log,timeout=180,rss_reader=rss_bytes):
    start=time.monotonic(); peak=0; reason=None; samples=0
    ensure_subreaper()
    with log.open('x') as f:
        proc=subprocess.Popen(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
        verified=False
        try:
            # start_new_session makes the PID both session and group leader;
            # verify this immediately while it is still our unreaped child.
            try:
                verified=(os.getpgid(proc.pid)==proc.pid and os.getsid(proc.pid)==proc.pid)
            except ProcessLookupError:
                verified=False
            if not verified:
                if proc.poll() is None:
                    # Without a verified group identity we cannot claim cleanup.
                    proc.kill();proc.wait(timeout=5)
                else: proc.wait()
                raise RuntimeError('compiler process-group identity unconfirmed')
            while proc.poll() is None:
                sample=rss_reader(proc.pid)
                if sample is None:
                    # A process may become a zombie between poll and reading
                    # status. Accept only an observed exit after at least one
                    # successful RSS sample; otherwise stop fail-closed.
                    if proc.poll() is not None and samples:
                        break
                    reason='rss_unavailable_while_unreaped'
                    terminate_verified_group(proc,verified)
                    break
                samples+=1;peak=max(peak,sample)
                if peak>int(3.5*1024**3):reason='sampled_rss_above_3.5GiB'
                if shutil.disk_usage('/tmp').free<4*1024**3:reason='sampled_free_below_4GiB'
                if time.monotonic()-start>timeout:reason='timeout'
                if reason:
                    terminate_verified_group(proc,verified)
                    break
                time.sleep(1)
            if samples==0 and reason is None:
                reason='no_rss_observation'
            code=proc.wait(timeout=5)
            # A successful leader leaving a live process group is not a pass.
            if reason is None:
                try:os.killpg(proc.pid,0)
                except ProcessLookupError:pass
                else:
                    reason='lingering_process_group'
                    terminate_verified_group(proc,verified)
        except BaseException:
            if verified:
                terminate_verified_group(proc,verified)
            elif proc.poll() is None:
                proc.kill();proc.wait(timeout=5)
            raise
    return code,peak,reason

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True,type=Path);args=ap.parse_args()
    out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-freej-current-denominator-'):
        raise ValueError('output must be a fresh direct /tmp/ipra-freej-current-denominator-* path')
    if out.exists() or out.is_symlink():raise ValueError('output already exists')
    check_sources()
    spec=importlib.util.spec_from_file_location('matched_parent',PARENT_SCRIPT);parent=importlib.util.module_from_spec(spec);spec.loader.exec_module(parent)
    parent.check_pins();before=parent.compare_parent()
    manifest=json.loads((BASE/'difference-ring-build-plan/coherent-replay/source-freeze-evidence-03/manifest.json').read_text())
    available=set(manifest['order'])
    imports={}
    for rel,_,_ in SOURCES:
        path=BASE/rel; mod='DiophantineConsistency.'+path.stem
        parsed=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',path.read_text(),re.M)
        if not parsed or any(x.startswith(('DiophantineConsistency.','BusyBeaver.')) and x not in available for x in parsed):
            raise ValueError(('missing or out-of-order declared project import',rel,parsed))
        imports[mod]=parsed;available.add(mod)
    out.mkdir();rows=[]
    for label in ('author','peer'):
        run=out/label;lib=run/'lib';srcroot=run/'src';srcroot.mkdir(parents=True)
        overlay(parent.PAIR/label/'child-output/lib',lib)
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(parent.PACKAGE)
        for rel,sha,count in SOURCES:
            orig=BASE/rel;mod='DiophantineConsistency.'+orig.stem
            src=srcroot/'DiophantineConsistency'/orig.name;src.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(orig,src)
            obj=lib/'DiophantineConsistency'/(orig.stem+'.olean')
            if obj.exists() or obj.is_symlink():raise ValueError(('suffix object already exists',str(obj)))
            cmd=[str(parent.LEAN),'-M3000','-j1','-DElab.async=false',f'--root={srcroot}',str(src),'-o',str(obj)]
            log=run/(orig.stem+'.log');exitcode,peak,reason=monitored(cmd,env,log)
            output=log.read_text();reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",output,re.M)
            row={'label':label,'module':mod,'source_sha256':H(src),'command':cmd,'exit':exitcode,'peak_sampled_rss_bytes':peak,'stop_reason':reason,'log':str(log),'log_sha256':H(log),'axiom_reports':reports}
            rows.append(row);(out/'progress.json').write_text(json.dumps(rows,indent=2)+'\n')
            if exitcode or reason or 'warning:' in output or 'sorryAx' in output or len(reports)!=count:
                raise ValueError(('compiler failure',label,mod,exitcode,reason,output[-12000:]))
            if any({x.strip() for x in r.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for r in reports):raise ValueError(('unexpected axioms',label,mod,reports))
            deps=subprocess.run([str(parent.LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
            expected={str(parent.PACKAGE/'Init.olean')}
            expected.update(str(lib/(x.replace('.','/')+'.olean')) for x in imports[mod])
            if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('dependency mismatch',label,mod,deps.returncode,deps.stdout,deps.stderr,sorted(expected)))
            row.update({'object_sha256':H(obj),'deps_exit':deps.returncode,'deps_stdout':deps.stdout})
            print(label,mod,'exit',exitcode,'peak_RSS',peak,flush=True)
    for i in range(len(SOURCES)):
        a,b=rows[i],rows[i+len(SOURCES)]
        if a['source_sha256']!=b['source_sha256'] or a['object_sha256']!=b['object_sha256'] or a['axiom_reports']!=b['axiom_reports']:
            raise ValueError(('suffix siblings differ',a['module']))
    check_sources();parent.check_pins();after=parent.compare_parent()
    if before!=after:raise ValueError('parent pair changed')
    receipt={'status':'PASS_PAIRED_CURRENT_DENOMINATOR_COMPOSITION','runs':rows,'parent_comparison':after,
             'scope':'Paired suffix source rebuild over audited matched 70-source project parent. Sampled RSS and disk checks are not quotas; package-transitive and dynamic ancestry inherited. No denominator integrality, compact44 checker calibration, or object-level iPRA proof.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_CURRENT_DENOMINATOR_COMPOSITION',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
