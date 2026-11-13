#!/usr/bin/env python3
"""Replay bounded inverse row lookup over the audited matching pair."""
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('requires nonoptimized python3 -I -S')
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[2]
AUDIT=BASE/'reviews/compact44-row-match-independent-audit'
CONTEXT=BASE/'reviews/historical-row-contextual-audit'
CONTEXT_REVIEW=BASE/'reviews/historical-row-contextual-independent-audit'
REPOSITORY=BASE.parents[1]
PARENT=Path('/tmp/ipra-compact-row-transport-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
MONITOR=BASE/'research/ordinary12-ipra-bridge/free-j-current-denominator-composition/replay.py'
PINS={AUDIT/'CHECK.json':'db7690d62441f036f8275f5270416b015c8e0b2cc858de8b48ea19a703755df7',
 AUDIT/'audit.py':'132d62eb41c5876d1612e7d7702993ce28f67f837e942758e45b6e5ee5993d06',
 AUDIT/'terminal-observation.json':'572354c51682ffffc13aa4361f9acb783cefe15f3d9c878bc0f7bf0802b34cb6',
 PARENT/'receipt.json':'a10ab9ecc787aa4ba3ff0f88a38b12eb68bbd2722a693e490b61ac14f762cdc9',
 HERE/'CompactInverseInventory.lean':'b895139b27408838294f99cc14b8d7fd3cf9e37afef4d667f85a3baace8a9fc8',
 CONTEXT/'contextual-chain.py':'470eb6dcbb05e66f303c7ee05350f46d884cd2f93eca3b1ff54bbfb588dcf163',
 CONTEXT/'CHECK.json':'455f39ce03635df8100786097b4ede5307fa35a4f61a101dbf5d7318c0184101',
 CONTEXT/'terminal-observation.json':'b863edb0860e23efd971dab9e068bc3e4020bc1681494a9f2dca859a6876e886',
 CONTEXT_REVIEW/'audit.py':'15782d47afa7f465c84fd25bff78a7bca5b1b3214fb90a6788980c88c83d3316',
 CONTEXT_REVIEW/'CHECK.json':'1cb82422b2e530094324f7e86e2577ddd5718216816c70c9d1c97abb3d840578',
 CONTEXT_REVIEW/'terminal-observation.json':'2cff6a5149ea719af967cd0fd4a5eef2fba4b11368b83470560cb5a4db995520',
 LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8'}
NAMES=['CompactInverseDraft.inverse_forward','CompactInverseDraft.inverse_image','CompactInverseDraft.inverseLookup_defined']
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
def audit(view):
    review=json.loads((CONTEXT_REVIEW/'CHECK.json').read_bytes());obs=json.loads((CONTEXT_REVIEW/'terminal-observation.json').read_bytes())
    if review.get('status')!='PASS_INDEPENDENT_CONTEXTUAL_ROW_EVIDENCE' or obs.get('check_sha256')!=PINS[CONTEXT_REVIEW/'CHECK.json'] or obs.get('lean_launched') is not False or any(type(obs.get(k)) is not int or obs[k]!=0 for k in ('independent_view_preparation_exit','independent_contextual_exit','independent_controls_exit','static_check_observed_exit')):raise ValueError('context review observation')
    c=subprocess.run([sys.executable,'-I','-S','-B',str(CONTEXT_REVIEW/'audit.py')],cwd=REPOSITORY,capture_output=True,text=True,timeout=120)
    if c.returncode or c.stderr or json.loads(c.stdout)!=review:raise ValueError(('context review audit failed',c.returncode,c.stderr))
    p=subprocess.run([sys.executable,'-I','-S','-B',str(CONTEXT/'contextual-chain.py'),'row',str(view)],cwd=REPOSITORY,capture_output=True,text=True,timeout=1200)
    if p.returncode or p.stderr:raise ValueError(('parent audit failed',p.returncode,p.stdout,p.stderr))
    x=json.loads(p.stdout)
    if x!=json.loads((AUDIT/'CHECK.json').read_text()):raise ValueError(('parent audit receipt mismatch',x))
    return x
def overlay(base,dest):
    for current,dirs,files in os.walk(base,followlinks=False):
        current=Path(current);out=dest/current.relative_to(base);out.mkdir(parents=True,exist_ok=True)
        for d in list(dirs):
            p=current/d
            if p.is_symlink():(out/d).symlink_to(p);dirs.remove(d)
        for f in files:(out/f).symlink_to(current/f)
def check_frozen(p,original):
    if not p.is_file() or p.is_symlink() or digest(p)!=PINS[original]:raise ValueError(('frozen source drift',str(p)))
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
def output_guards(obj, *, before):
    stem = str(obj)[:-len('.olean')]
    observed = guard(stem)
    for suffix in SUFFIXES:
        value = observed[stem + suffix]
        if suffix == '.olean' and not before:
            if value is None or obj.is_symlink():raise ValueError(('missing or symlink output',str(obj)))
        elif value is not None:
            raise ValueError(('unexpected output companion',stem + suffix))
    return observed

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--historical-view',type=Path,required=True);ap.add_argument('--expected-head',required=True);args=ap.parse_args();out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact-inverse-contextual-pair-'):raise ValueError('invalid output')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    head=lambda:subprocess.run(['git','rev-parse','HEAD'],cwd=REPOSITORY,capture_output=True,text=True,check=True,timeout=10).stdout.strip()
    if head()!=args.expected_head:raise ValueError('unexpected launch HEAD')
    driver=digest(__file__);pins();before=audit(args.historical_view)
    if shutil.disk_usage('/tmp').free<4*1024**3:raise ValueError('sampled free space below reserve')
    spec=importlib.util.spec_from_file_location('monitor',MONITOR);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
    out.mkdir();srcroot=out/'src';srcdir=srcroot/'DiophantineConsistency';srcdir.mkdir(parents=True)
    src=srcdir/'CompactInverseInventory.lean';src.write_bytes((HERE/'CompactInverseInventory.lean').read_bytes())
    check_frozen(src,HERE/'CompactInverseInventory.lean')
    rows=[];allguards={}
    for side in ('author','peer'):
        check_frozen(src,HERE/'CompactInverseInventory.lean')
        run=out/side;run.mkdir();lib=run/'lib';overlay(PARENT/side/'lib',lib)
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(PACKAGE)
        deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=120)
        expected={str(PACKAGE/'Init.olean'),str(lib/'DiophantineConsistency/CompactRowComplete.olean')}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('dependency mismatch',side,deps.returncode,deps.stdout,deps.stderr))
        require_objects(expected,side,'CompactInverseInventory')
        guards={}
        for item in expected:guards.update(guard(item[:-6]))
        checkguards(guards);obj=lib/'DiophantineConsistency/CompactInverseInventory.olean';log=run/'CompactInverseInventory.log'
        output_guards(obj,before=True)
        cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={srcroot}',str(src),'-o',str(obj)]
        code,peak,reason=monitor.monitored(cmd,env,log,timeout=600);output=log.read_text()
        reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",output,re.M)
        row={'side':side,'command':cmd,'source_sha256':digest(src),'exit':code,'stop_reason':reason,'sampled_peak_rss_bytes':peak,'log_sha256':digest(log),'deps_exit':deps.returncode,'deps_stdout':deps.stdout,'axiom_reports':reports}
        rows.append(row);(out/'progress.json').write_text(json.dumps(rows,indent=2)+'\n')
        if code or reason or not obj.is_file() or obj.is_symlink() or re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',output):raise ValueError(('compiler failure',side,code,reason,output[-12000:]))
        if [n for n,_ in reports]!=NAMES or any({x.strip() for x in ax.split(',') if x.strip()}!={'propext','Classical.choice','Quot.sound'} for _,ax in reports):raise ValueError(('axiom report mismatch',side,reports))
        guards.update(output_guards(obj,before=False))
        pins();checkguards(guards)
        if head()!=args.expected_head:raise ValueError('HEAD drift')
        check_frozen(src,HERE/'CompactInverseInventory.lean')
        for k,v in guards.items():
            if k in allguards and allguards[k]!=v:raise ValueError(('guard drift',k))
            allguards[k]=v
        row['object_sha256']=digest(obj);(out/'progress.json').write_text(json.dumps(rows,indent=2)+'\n')
    if rows[0]['object_sha256']!=rows[1]['object_sha256'] or rows[0]['log_sha256']!=rows[1]['log_sha256']:raise ValueError('paired outputs differ')
    pins();check_frozen(src,HERE/'CompactInverseInventory.lean');checkguards(allguards);after=audit(args.historical_view);check_frozen(src,HERE/'CompactInverseInventory.lean')
    pins();checkguards(allguards)
    for row in rows:
        obj=Path(row['command'][-1]);log=out/row['side']/'CompactInverseInventory.log'
        if not obj.is_file() or obj.is_symlink() or digest(obj)!=row['object_sha256'] or digest(log)!=row['log_sha256']:raise ValueError(('final object or log drift',row['side']))
    if before!=after:raise ValueError('parent audit reruns differ')
    if digest(__file__)!=driver or head()!=args.expected_head:raise ValueError('driver or HEAD drift')
    receipt={'status':'PASS_CONTEXTUAL_COMPACT_INVERSE_LOOKUP_PAIR','driver_sha256':driver,'source_sha256':digest(src),'parent_audit_before':before['status'],'parent_audit_after':after['status'],'direct_guards':allguards,'rows':rows,'contextual_historical_view':str(args.historical_view),'scope':'Contextual historical parent; exact bounded inverse row lookup and Sigma0 lookup definability; excludes row 1 as an explicit assumption; no word transport, row-1 exclusion, calibration or iPRA endpoint. Sampled resource checks and package/transitive/dynamic boundaries apply; lean --deps has leader timeout only.'}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':receipt['status'],'output':str(out),'receipt_sha256':digest(out/'receipt.json')}))
if __name__=='__main__':main()
