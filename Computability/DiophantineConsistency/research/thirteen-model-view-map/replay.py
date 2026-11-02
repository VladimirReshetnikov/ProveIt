#!/usr/bin/env python3
"""Paired bounded model/graph subtraction mapping over audited window and graph-cut parents."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('replay rejects optimized Python')
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=HERE/'Model69ViewMap.lean'
PREFIXAUDIT=ROOT/'reviews/thirteen-model-parent-window-pair-independent-audit'
OUTERAUDIT=ROOT/'reviews/thirteen-model-graph-cut-independent-audit'
PREFIX=Path('/tmp/ipra-thirteen-parent-window-pair-01')
OUTER=Path('/tmp/ipra-thirteen-graph-cut-pair-01')
DAG=Path('/tmp/ipra-thirteen69-dag-pair-01')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PINS={SOURCE:'ec0bd93b29f098008db3f501d77da258b3a9e6cd20a977516e740dc2f28b4479',
      PREFIXAUDIT/'audit.py':'679a7680a3e4fbc3a7555bc1ba3a43b543d749311f08760a91ab24433539f4c1',
      PREFIXAUDIT/'CHECK.json':'4a358f8fd09fa3be38d32aa2314ad063406ea2d363f74d1a13f41dedcc3e0ec9',
      PREFIXAUDIT/'terminal-observation.json':'516750a20bddd6d87dc5ecd0bdcd904c6d74deb505b5b8b3c6f4ba111f7a2549',
      OUTERAUDIT/'audit.py':'ab733f8f50398567741aa2c2ade30cba5017283b58d52624c452c7f696764614',
      OUTERAUDIT/'CHECK.json':'b7feb6dd43d9edc42fdbc703fa99bcb14fcd9c011872ab9781d7d53f4388c404',
      OUTERAUDIT/'terminal-observation.json':'4c919791e186e067f556aead40bbc7b819e01ceadc0c65e2d269e3a7b375323a',
      LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()


def check_pins():
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    for audit,status in ((PREFIXAUDIT,'PASS_INDEPENDENT_24_MODULE_WINDOW_PAIR_AUDIT'),
                         (OUTERAUDIT,'PASS_INDEPENDENT_THIRTEEN_GRAPH_CUT_AUDIT')):
        obs=json.loads((audit/'terminal-observation.json').read_text());check=json.loads((audit/'CHECK.json').read_text())
        if obs.get('audit_observed_exit_code')!=0 or obs.get('receipt_sha256')!=PINS[audit/'CHECK.json'] or check.get('status')!=status:
            raise ValueError(('invalid parent audit',str(audit)))


def verify_parents():
    records=[]
    for audit,status in ((PREFIXAUDIT,'PASS_INDEPENDENT_24_MODULE_WINDOW_PAIR_AUDIT'),
                         (OUTERAUDIT,'PASS_INDEPENDENT_THIRTEEN_GRAPH_CUT_AUDIT')):
        p=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'audit.py')],text=True,capture_output=True,timeout=180)
        if p.returncode or p.stderr:raise ValueError(('parent audit failed',str(audit),p.returncode,p.stdout,p.stderr))
        data=json.loads(p.stdout)
        if data.get('status')!=status:raise ValueError(('unexpected parent audit output',str(audit),data))
        records.append(data)
    return records


def merged_overlay(base,dag,lib):
    # Keep the complete audited window overlay; merge the four graph modules
    # only after checking every overlapping project object by bytes.
    for current,dirs,files in os.walk(base,followlinks=False):
        current=Path(current);out=lib/current.relative_to(base);out.mkdir(parents=True,exist_ok=True)
        for d in list(dirs):
            p=current/d
            if p.is_symlink():(out/d).symlink_to(p);dirs.remove(d)
        for f in files:(out/f).symlink_to(current/f)
    matched={};added={}
    for p in (dag/'DiophantineConsistency').glob('*.olean'):
        q=lib/'DiophantineConsistency'/p.name
        if os.path.lexists(q):
            if not q.is_file() or H(q)!=H(p):raise ValueError(('project collision',str(p)))
            matched[p.name]=H(p)
        else:
            q.symlink_to(p);added[p.name]=H(p)
    if len(matched)!=64 or set(added)!={'ShortEquation.olean','ThirteenCarrier.olean','Thirteen69Nodes.olean','Thirteen69Cuts.olean'}:
        raise ValueError(('unexpected overlay coverage',matched.keys(),added.keys()))
    return matched,added


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-thirteen-model-view-pair-'):
        raise ValueError('output must be a fresh /tmp/ipra-thirteen-model-view-pair-* directory')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    check_pins();before=verify_parents();out.mkdir();runs=[]
    for label in ('author','peer'):
        root=out/label/'src';root.mkdir(parents=True);src=root/'Model69ViewMap.lean';obj=out/label/'Model69ViewMap.olean'
        shutil.copyfile(SOURCE,src)
        outer=OUTER/label;lib=out/label/'lib'
        matched,added=merged_overlay(PREFIX/label/'lib',DAG/label/'lib',lib)
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):
                env.pop(key,None)
        env['LEAN_PATH']=':'.join(map(str,(outer,lib,PACKAGE)))
        cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        p=subprocess.run(cmd,env=env,text=True,capture_output=True,timeout=180);output=p.stdout+p.stderr
        reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",output,re.M)
        if p.returncode or p.stderr or 'warning:' in output or 'error:' in output or 'sorryAx' in output or len(reports)!=3:
            raise ValueError(('unexpected Lean result',label,p.returncode,output))
        if any({x.strip() for x in report.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for report in reports):
            raise ValueError(('unexpected axioms',label,reports))
        deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(PACKAGE/'Init.olean'),str(outer/'Model69GraphCut.olean'),str(lib/'DiophantineConsistency/ModelDifferenceRing.olean'),str(lib/'DiophantineConsistency/ArithmeticCarrierRadix2011.olean')}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:
            raise ValueError(('unexpected direct imports',label,deps.returncode,deps.stdout,deps.stderr))
        if H(src)!=PINS[SOURCE]:raise ValueError(('source drift',label))
        runs.append({'label':label,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'command':cmd,
                     'source_sha256':H(src),'object_sha256':H(obj),'axiom_reports':reports,
                     'deps_exit':deps.returncode,'deps_stdout':deps.stdout,'matched_project_objects':matched,'added_graph_objects':added})
    if runs[0]['object_sha256']!=runs[1]['object_sha256'] or runs[0]['stdout']!=runs[1]['stdout']:
        raise ValueError('sibling outputs differ')
    check_pins();after=verify_parents()
    if before!=after:raise ValueError('parent audit output changed')
    receipt={'status':'PASS_PAIRED_THIRTEEN_MODEL_VIEW','runs':runs,'parent_audits':after,
             'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},
             'scope':'Three bounded conditional subtraction/rank/gap embedding lemmas over an explicitly joined window/graph provider. The window and prefix audits have no complete axiom inventory. No actual-zero norm extraction, full 69-operation converse, iPRA proof, phase-split2471 calibration, Foundation outer-wrapper exit, or complete package-transitive/dynamic audit is claimed.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_THIRTEEN_MODEL_VIEW',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
