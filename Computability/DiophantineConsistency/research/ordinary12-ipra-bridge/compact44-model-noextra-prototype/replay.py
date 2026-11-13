#!/usr/bin/env python3
"""Replay bounded compact exclusion over coherent matching and exact-source forbidden audits."""
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('requires nonoptimized python3 -I -S')
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[2]
AUDIT=BASE/'reviews/compact44-row-match-independent-audit'
FORBID=BASE/'reviews/compact44-forbidden-independent-audit'
FORBID_SOURCE=BASE/'research/ordinary12-ipra-bridge/compact44-color-relabel/CompactForbidden.lean'
PARENT=Path('/tmp/ipra-compact-row-transport-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
MONITOR=BASE/'research/ordinary12-ipra-bridge/free-j-current-denominator-composition/replay.py'
PINS={AUDIT/'CHECK.json':'db7690d62441f036f8275f5270416b015c8e0b2cc858de8b48ea19a703755df7',
 AUDIT/'audit.py':'132d62eb41c5876d1612e7d7702993ce28f67f837e942758e45b6e5ee5993d06',
 AUDIT/'terminal-observation.json':'572354c51682ffffc13aa4361f9acb783cefe15f3d9c878bc0f7bf0802b34cb6',
 PARENT/'receipt.json':'a10ab9ecc787aa4ba3ff0f88a38b12eb68bbd2722a693e490b61ac14f762cdc9',
 HERE/'CompactNoExtra.lean':'fcf37774ceef70180a36d6779394367f6ad9c73fa04d0fe87e910bc1b372dfa5',
 FORBID_SOURCE:'27786b8ec2cf08ccd81f3cdb8f0585adf76fbfacc8e993be310d4697ac01e020',
 FORBID/'CHECK.json':'07115dceeaa8a5c320399c9232a20f230c5b8320ebb450df934256d0449c5879',
 FORBID/'audit.py':'58b8c081d6c6103bfb51a374916a48a550e82f491d3ba5fe3ba4aedfaa7852e7',
 FORBID/'terminal-observation.json':'609f6a9419854d74f769c113cfa2cd2bd985e06354690526df6fe15229aa8ffa',
 LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8'}
REPORTS={'CompactForbidden':[('CompactForbidden.no_east_five_all',set()),('CompactForbidden.west_five_extra_all',set()),('CompactForbidden.no_east_five',{'propext','Quot.sound'}),('CompactForbidden.west_five_extra',{'propext','Quot.sound'}),('CompactForbidden.five_cannot_have_left',{'propext','Quot.sound'})],
 'CompactNoExtra':[(n,{'propext','Classical.choice','Quot.sound'}) for n in ('CompactNoExtra.extra_forbidden_with_left','CompactNoExtra.cyclic_excludes_extra')]}
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def valid_parent_observation(x,obs):
    return (x.get('status')=='PASS_INDEPENDENT_COMPACT_ROW_MATCH_AUDIT'
        and type(obs.get('independent_parent_rerun_exit')) is int and obs['independent_parent_rerun_exit']==0
        and type(obs.get('independent_review_exit')) is int and obs['independent_review_exit']==0
        and obs.get('check_sha256')==PINS[AUDIT/'CHECK.json']
        and obs.get('lean_launched') is False)
def pins():
    for p,h in PINS.items():
        if digest(p)!=h:raise ValueError(('fixed input drift',str(p)))
    x=json.loads((AUDIT/'CHECK.json').read_text()); obs=json.loads((AUDIT/'terminal-observation.json').read_text())
    if not valid_parent_observation(x,obs):raise ValueError('parent audit observation')
    y=json.loads((FORBID/'CHECK.json').read_text());fo=json.loads((FORBID/'terminal-observation.json').read_text())
    if y.get('status')!='PASS_INDEPENDENT_COMPACT44_FORBIDDEN_AUDIT' or type(fo.get('observed_exit')) is not int or fo['observed_exit']!=0 or fo.get('receipt_sha256')!=PINS[FORBID/'CHECK.json'] or type(fo.get('lean_compilations_started')) is not int or fo['lean_compilations_started']!=0:raise ValueError('forbidden audit observation')
def audit():
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,text=True,timeout=1200)
    if p.returncode or p.stderr:raise ValueError(('parent audit failed',p.returncode,p.stdout,p.stderr))
    x=json.loads(p.stdout)
    if x!=json.loads((AUDIT/'CHECK.json').read_text()):raise ValueError(('parent audit receipt mismatch',x))
    q=subprocess.run([sys.executable,'-I','-S','-B',str(FORBID/'audit.py')],capture_output=True,text=True,timeout=1200)
    if q.returncode or q.stderr:raise ValueError(('forbidden parent audit failed',q.returncode,q.stdout,q.stderr))
    y=json.loads(q.stdout)
    if y!=json.loads((FORBID/'CHECK.json').read_text()):raise ValueError(('forbidden parent audit receipt mismatch',y))
    return [x,y]
def overlay(base,dest):
    for current,dirs,files in os.walk(base,followlinks=False):
        current=Path(current);out=dest/current.relative_to(base);out.mkdir(parents=True,exist_ok=True)
        for d in list(dirs):
            p=current/d
            if p.is_symlink():(out/d).symlink_to(p);dirs.remove(d)
        for f in files:(out/f).symlink_to(current/f)
def require_objects(expected,side,name):
    for item in expected:
        if not Path(item).is_file():raise ValueError(('missing required object',side,name,item))
def guard(stem):
    out={}
    for suffix in SUFFIXES:
        p=Path(str(stem)+suffix)
        if os.path.lexists(p):
            if not p.is_file():raise ValueError(('invalid companion',str(p)))
            out[str(p)]={'realpath':str(p.resolve()),'sha256':digest(p)}
        else:out[str(p)]=None
    return out
def checkguards(guards):
    for k,v in guards.items():
        p=Path(k)
        if v is None:
            if os.path.lexists(p):raise ValueError(('unexpected companion',k))
        elif not p.is_file() or str(p.resolve())!=v['realpath'] or digest(p)!=v['sha256']:
            raise ValueError(('companion drift',k))
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact-model-noextra-pair-'):raise ValueError('invalid output')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    driver=digest(__file__);pins();before=audit()
    if shutil.disk_usage('/tmp').free<4*1024**3:raise ValueError('sampled free space below reserve')
    spec=importlib.util.spec_from_file_location('monitor',MONITOR);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
    out.mkdir();srcroot=out/'src';srcdir=srcroot/'DiophantineConsistency';srcdir.mkdir(parents=True)
    sources={'CompactForbidden':FORBID_SOURCE,'CompactNoExtra':HERE/'CompactNoExtra.lean'}
    for name,original in sources.items():
        src=srcdir/(name+'.lean');src.write_bytes(original.read_bytes())
        if digest(src)!=PINS[original]:raise ValueError(('source copy drift',name))
    rows=[];allguards={}
    for side in ('author','peer'):
        run=out/side;run.mkdir();lib=run/'lib';overlay(PARENT/side/'lib',lib)
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(PACKAGE)
        for name,original in sources.items():
            src=srcdir/(name+'.lean');deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=120)
            expected={str(PACKAGE/'Init.olean')}
            if name=='CompactForbidden':expected.add(str(lib/'DiophantineConsistency/Compact943Data.olean'))
            else:expected.update({str(lib/'DiophantineConsistency/CompactRowComplete.olean'),str(lib/'DiophantineConsistency/CompactForbidden.olean')})
            if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('dependency mismatch',side,name,deps.returncode,deps.stdout,deps.stderr))
            require_objects(expected,side,name)
            guards={}
            for item in expected:guards.update(guard(item[:-6]))
            checkguards(guards);obj=lib/'DiophantineConsistency'/(name+'.olean');log=run/(name+'.log')
            if os.path.lexists(obj):raise ValueError(('object collision',side,name))
            cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={srcroot}',str(src),'-o',str(obj)]
            code,peak,reason=monitor.monitored(cmd,env,log,timeout=600);output=log.read_text()
            pattern=r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$"
            reports=re.findall(pattern,output,re.M)
            row={'side':side,'module':name,'command':cmd,'source_sha256':digest(src),'exit':code,'stop_reason':reason,'sampled_peak_rss_bytes':peak,'log_sha256':digest(log),'deps_exit':deps.returncode,'deps_stdout':deps.stdout,'axiom_reports':reports}
            rows.append(row);(out/'progress.json').write_text(json.dumps(rows,indent=2)+'\n')
            if code or reason or not obj.is_file() or obj.is_symlink() or re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',output):raise ValueError(('compiler failure',side,name,code,reason,output[-12000:]))
            expectedreports=REPORTS[name]
            if [n for n,_ in reports]!=[n for n,_ in expectedreports] or any({x.strip() for x in ax.split(',') if x.strip()}!=wanted for (_,ax),(_,wanted) in zip(reports,expectedreports)):raise ValueError(('axiom report mismatch',side,name,reports))
            pins();checkguards(guards)
            if digest(src)!=PINS[original]:raise ValueError(('source drift',name))
            for k,v in guards.items():
                if k in allguards and allguards[k]!=v:raise ValueError(('guard drift',k))
                allguards[k]=v
            row['object_sha256']=digest(obj);(out/'progress.json').write_text(json.dumps(rows,indent=2)+'\n')
    for a,b in zip(rows[:2],rows[2:]):
        if a['module']!=b['module'] or a['object_sha256']!=b['object_sha256'] or a['log_sha256']!=b['log_sha256']:raise ValueError('paired outputs differ')
    pins();checkguards(allguards);after=audit()
    if before!=after:raise ValueError('parent audit reruns differ')
    if digest(__file__)!=driver:raise ValueError('driver drift')
    receipt={'status':'PASS_COMPACT_MODEL_NOEXTRA_PAIR','driver_sha256':driver,'source_sha256':{name:digest(srcdir/(name+'.lean')) for name in sources},'parent_audit_before':[x['status'] for x in before],'parent_audit_after':[x['status'] for x in after],'direct_guards':allguards,'rows':rows,'scope':'Local and cyclic compact row-1 exclusion assuming a supplied bounded matching neighbor or positive-period cyclic matching; no construction of a word, matching premises, tiling equivalence, calibration or iPRA endpoint. Sampled resource checks and package/transitive/dynamic boundaries apply; lean --deps has leader timeout only.'}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':receipt['status'],'output':str(out),'receipt_sha256':digest(out/'receipt.json')}))
if __name__=='__main__':main()
