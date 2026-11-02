#!/usr/bin/env python3
"""Paired fresh-private suffix replay over two independently audited parents."""
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
CARRIER=HERE/'ModelBPositiveCarrier.lean'
PRIVATE=HERE/'ModelBFreshPrivate.lean'
AUXAUDIT=ROOT/'reviews/thirteen-model-auxiliary-seed-independent-audit'
NEGAUDIT=ROOT/'reviews/thirteen-model-negative-residue-independent-audit'
AUX=Path('/tmp/ipra-thirteen-aux-seed-pair-01')
NEG=Path('/tmp/ipra-thirteen-negative-residue-pair-01')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PINS={CARRIER:'d4074ccea3c55d66c6844d9f8b55b86de83745a10fec3f746bf75c11f6a8cd4c',
      PRIVATE:'c5aa5f1fd8090e59b2b2727944624cb7f68c48684be54bfb0329b2c11a0bc83c',
      AUXAUDIT/'audit.py':'3b8fade16240ffb001074714e459053cd42eb1b4933e1b700f97bd636e51d4ef',
      AUXAUDIT/'CHECK.json':'795223c9125a4df837af0390dbd557024d63658e665474dae282d21c88f9308d',
      AUXAUDIT/'terminal-observation.json':'d2fbe87f2fbe73f7083c0bcfc492145359ced90cf3ece2f646ed506648807f2b',
      NEGAUDIT/'audit.py':'d4dfb864908521dc3bf72eb5b27028f94ccda6af6b94195c81f22648fdad4385',
      NEGAUDIT/'CHECK.json':'9811fa9f3254c35268accfba801002856880fe208eb75c991a76bc97cd8447a5',
      NEGAUDIT/'terminal-observation.json':'e13cc88c5707aa1caa24b40b3f6778cb0ce5c7899cdec3c73f9b680c68e02c63',
      LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
NEGATIVE_MODULES=('DiscreteOrderedRingFacts','ArithmeticNegativeNorms','ModelArithmetic',
                  'ArithmeticOddOrdinateResidue','ModelBNegativeResidue')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()


def check_pins():
    for p,digest in PINS.items():
        if H(p)!=digest:raise ValueError(('fixed input drift',str(p)))
    for audit,status in ((AUXAUDIT,'PASS_INDEPENDENT_THIRTEEN_MODEL_AUXILIARY_AUDIT'),
                         (NEGAUDIT,'PASS_INDEPENDENT_THIRTEEN_NEGATIVE_RESIDUE_AUDIT')):
        observation=json.loads((audit/'terminal-observation.json').read_text())
        check=json.loads((audit/'CHECK.json').read_text())
        if observation.get('audit_observed_exit_code')!=0 or observation.get('receipt_sha256')!=PINS[audit/'CHECK.json']:
            raise ValueError(('missing observed independent audit exit',str(audit)))
        if check.get('status')!=status:raise ValueError(('unexpected parent audit status',str(audit)))


def verify_parents():
    records=[]
    for audit,status in ((AUXAUDIT,'PASS_INDEPENDENT_THIRTEEN_MODEL_AUXILIARY_AUDIT'),
                         (NEGAUDIT,'PASS_INDEPENDENT_THIRTEEN_NEGATIVE_RESIDUE_AUDIT')):
        p=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'audit.py')],text=True,capture_output=True,timeout=180)
        if p.returncode or p.stderr:raise ValueError(('parent audit failed',str(audit),p.returncode,p.stdout,p.stderr))
        data=json.loads(p.stdout)
        if data.get('status')!=status:raise ValueError(('unexpected audit output',str(audit),data))
        records.append(data)
    return records


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-thirteen-fresh-private-pair-'):
        raise ValueError('output must be a fresh /tmp/ipra-thirteen-fresh-private-pair-* directory')
    if out.exists() or out.is_symlink():raise ValueError('output already exists')
    check_pins();before=verify_parents();out.mkdir();runs=[]
    for label in ('author','peer'):
        run=out/label;root=run/'src';srcdir=root/'DiophantineConsistency';project=run/'lib/DiophantineConsistency'
        auxlib=AUX/label/'lib';neglib=NEG/label/'lib'
        srcdir.mkdir(parents=True);project.mkdir(parents=True)
        (run/'lib/BusyBeaver').symlink_to(auxlib/'BusyBeaver',target_is_directory=True)
        links={}
        for source in (auxlib/'DiophantineConsistency').glob('*.olean'):
            link=project/source.name;link.symlink_to(source);links[str(link)]={'target':str(source),'sha256':H(source)}
        if len(links)!=69:raise ValueError(('unexpected auxiliary parent link count',label,len(links)))
        for name in NEGATIVE_MODULES:
            source=neglib/'DiophantineConsistency'/(name+'.olean');link=project/source.name
            if link.exists() or link.is_symlink():raise ValueError(('parent module collision',label,name))
            link.symlink_to(source);links[str(link)]={'target':str(source),'sha256':H(source)}
        if len(links)!=74:raise ValueError(('unexpected combined parent link count',label,len(links)))
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):
                env.pop(key,None)
        env['LEAN_PATH']=str(run/'lib')+':'+str(PACKAGE)
        row={'label':label,'modules':[]}
        for source in (CARRIER,PRIVATE):
            src=srcdir/source.name;obj=project/(source.stem+'.olean')
            if obj.exists() or obj.is_symlink():raise ValueError(('unintended inherited object',str(obj)))
            shutil.copyfile(source,src)
            cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
            result=subprocess.run(cmd,env=env,text=True,capture_output=True,timeout=240)
            output=result.stdout+result.stderr
            if result.returncode or result.stderr or 'error:' in output or 'sorryAx' in output or 'admit' in output:
                raise ValueError(('Lean failed',label,source.name,result.returncode,output))
            reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",output,re.M)
            if len(reports)!=1 or {x.strip() for x in reports[0].split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}:
                raise ValueError(('unexpected axiom report',label,source.name,reports,output))
            warning_lines=[line.split('warning:',1)[1].strip() for line in output.splitlines() if 'warning:' in line]
            if source==CARRIER:
                if len(warning_lines)!=3 or any(not line.startswith('`push_neg` has been deprecated.') for line in warning_lines):
                    raise ValueError(('unexpected carrier warnings',label,warning_lines))
            elif warning_lines:raise ValueError(('unexpected private warnings',label,warning_lines))
            deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
            expected=({str(PACKAGE/'Init.olean'),str(project/'ModelArithmetic.olean')} if source==CARRIER else
                      {str(PACKAGE/'Init.olean'),str(project/'ModelBAuxiliary.olean'),
                       str(project/'ModelBNegativeResidue.olean'),str(project/'ModelBPositiveCarrier.olean')})
            if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:
                raise ValueError(('unexpected direct imports',label,source.name,deps.returncode,deps.stdout,deps.stderr))
            if H(src)!=PINS[source]:raise ValueError(('copied source drift',label,source.name))
            row['modules'].append({'name':source.stem,'exit':result.returncode,'stdout':result.stdout,'stderr':result.stderr,
                                   'source_sha256':H(src),'object_sha256':H(obj),'axiom_reports':reports,
                                   'warning_lines':warning_lines,'command':cmd,'deps_exit':deps.returncode,'deps_stdout':deps.stdout})
        for link,info in links.items():
            q=Path(link)
            if not q.is_symlink() or q.resolve()!=Path(info['target']).resolve() or H(q)!=info['sha256']:
                raise ValueError(('parent link drift',link))
        row['parent_links']=links;runs.append(row)
    if [m['object_sha256'] for m in runs[0]['modules']]!=[m['object_sha256'] for m in runs[1]['modules']]:
        raise ValueError('suffix objects do not match')
    if runs[0]['modules'][1]['stdout']!=runs[1]['modules'][1]['stdout']:
        raise ValueError('fresh-private axiom reports do not match')
    check_pins();after=verify_parents()
    if before!=after:raise ValueError('parent audit output changed')
    receipt={'status':'PASS_PAIRED_THIRTEEN_FRESH_PRIVATE','runs':runs,'parent_audits':after,
             'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},
             'scope':'Two bounded model-level suffix compilations over separately audited matched auxiliary-seed and negative-residue parents. No 13-variable converse, graph transport, iPRA proof, fixed-port calibration, Foundation outer-wrapper exit, or complete package-transitive/dynamic audit is claimed.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_THIRTEEN_FRESH_PRIVATE',H(out/'receipt.json'),flush=True)

if __name__=='__main__':main()
