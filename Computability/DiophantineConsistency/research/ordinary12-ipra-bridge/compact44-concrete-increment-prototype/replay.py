#!/usr/bin/env python3
"""Rebuild mixed-mask sources on both successor providers, then join the concrete mask."""
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'): raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent;BASE=HERE.parent;ROOT=HERE.parents[2]
PREFIX=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01'); AUDIT=ROOT/'reviews/thirteen-model-endpoint-successor-pair-independent-audit'
MONITOR=BASE/'free-j-current-denominator-composition/replay.py';LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SEEDS=(('CompactListMask','compact44-list-mask-prototype','ipra-compact-list-mask-pair-01','compact44-list-mask-independent-audit','PASS_PAIRED_COMPACT_LIST_MASK','PASS_INDEPENDENT_COMPACT44_LIST_MASK_AUDIT'),('CompactConcreteMask','compact44-concrete-mask-prototype','ipra-compact-concrete-mask-pair-01','compact44-concrete-mask-independent-audit','PASS_PAIRED_COMPACT_CONCRETE_MASK','PASS_INDEPENDENT_COMPACT44_CONCRETE_MASK_AUDIT'))
REBUILT_AUDITS=(('compact44-dummy-bound-prototype','compact44-dummy-bound-independent-audit','PASS_INDEPENDENT_COMPACT44_DUMMY_BOUND_AUDIT'),('compact44-mask-slot-prototype','compact44-mask-slot-independent-audit','PASS_INDEPENDENT_COMPACT44_MASK_SLOT_AUDIT'),('compact44-mixed-increment-prototype','compact44-mixed-increment-independent-audit','PASS_INDEPENDENT_COMPACT44_MIXED_INCREMENT_AUDIT'))
STEPS=(('CompactDummyBound',BASE/'compact44-dummy-bound-prototype/CompactDummyBound.lean',('ArithmeticWindowDigits',),3),('CompactMaskSlot',BASE/'compact44-mask-slot-prototype/CompactMaskSlot.lean',('CompactDummyBound',),3),('CompactMixedIncrement',BASE/'compact44-mixed-increment-prototype/CompactMixedIncrement.lean',('CompactMaskSlot','ArithmeticWindowBits'),1),('CompactConcreteIncrement',HERE/'CompactConcreteIncrement.lean',('CompactConcreteMask','CompactMixedIncrement'),2))
PINS = {MONITOR: '2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 LEAN: 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 AUDIT/'audit.py': 'ec4892d88e69a9f53d3d93d48ce9e43cc8a5f9631ed4a885af17a40011858681',
 AUDIT/'CHECK.json': '50c18ab38d6393cf784e658b5626bb6ec3cb490dc1652f5b5dcfa2b1adca1cce',
 AUDIT/'terminal-observation.json': '9f65d29fd39bab15653d0f35ebf78dea2d590618502ffe56fed8fa863c9082ba',
 HERE/'CompactConcreteIncrement.lean': '91744fb88bf1f88da6c58d9311ae674ff28c2c9201e415d953a318cafe8976ac',
 BASE/'compact44-dummy-bound-prototype'/'CompactDummyBound.lean': '6acfd50bd3e4903d3cc9bbcff4f7fcbe699dd6961b5340be216352c2a52cf69e',
 BASE/'compact44-dummy-bound-prototype'/'evidence/receipt.json': '7332c7a3e4fc13cfaa87308b25349d740ca8fb1c1864b6859640d13a4a294b15',
 ROOT/'reviews'/'compact44-dummy-bound-independent-audit'/'CHECK.json': 'a2a144c733e6a1fee23e07025f95755168000c4b4f538e3911e9d29f5f26052e',
 BASE/'compact44-mask-slot-prototype'/'CompactMaskSlot.lean': 'c06708e41c210927dd3b5aba1be721b3e48c84d1a56394f1a26ea9d23cc09ea1',
 BASE/'compact44-mask-slot-prototype'/'evidence/receipt.json': 'ddef69b4310caef263591491dafe50cc9e9d01542fcaecfb7479c9fa7a0704d9',
 ROOT/'reviews'/'compact44-mask-slot-independent-audit'/'CHECK.json': '7ee25fa5ad3fc966b78491325b2ad2f30c2e0b7a205ddd0e33e23a39d2d68168',
 BASE/'compact44-mixed-increment-prototype'/'CompactMixedIncrement.lean': '056b203e0b207fb9f88893828df4d721a4aff3106fd85c503285470de9cd713d',
 BASE/'compact44-mixed-increment-prototype'/'evidence/receipt.json': '64e8b41aed059ed22bb836e4fc3456aa1f05fedb9191c4062784b9c31eb3e7de',
 ROOT/'reviews'/'compact44-mixed-increment-independent-audit'/'CHECK.json': '0bdab077abec274d75720c626ec8aa48068e8f40ad0bf68a1f32011a88e73e44',
 BASE/'compact44-list-mask-prototype'/'replay.py': 'ad54969e25f8fc2439790ebbfa830bbe360b93fdfbc4ef480359d94c4db01f94',
 BASE/'compact44-list-mask-prototype'/'evidence/receipt.json': '20d453580cda1086d586996de8be284e498098a7396c4f72741c94c1fecba8ef',
 ROOT/'reviews'/'compact44-list-mask-independent-audit'/'CHECK.json': '02c279e26f75784eaa5ccf8e66c392bfbc6d3a4ef144220512cea534fb2bff61',
 BASE/'compact44-concrete-mask-prototype'/'replay.py': '26c5cf26f3d8480930e4f5eaa9c642f75667965fdae080729218721b318138c9',
 BASE/'compact44-concrete-mask-prototype'/'evidence/receipt.json': '65a893c524bff130c16e63687a9e0aa896f2246ac5a1e57fdca149096de59fbd',
 ROOT/'reviews'/'compact44-concrete-mask-independent-audit'/'CHECK.json': '38e176a41a83b029d0cf7a9c4f2406ea162b40528b56b3036343a9137b962fb8'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(path):
    spec=importlib.util.spec_from_file_location('monitor',path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def checked_receipt_digest(checked,module):
    expected_key={'CompactListMask':'author_receipt_sha256','CompactConcreteMask':'receipt_sha256'}[module]
    other_key={'author_receipt_sha256':'receipt_sha256','receipt_sha256':'author_receipt_sha256'}[expected_key]
    if expected_key not in checked or (other_key in checked and checked[other_key]!=checked[expected_key]):raise ValueError(('invalid or conflicting receipt keys',module))
    return checked[expected_key]

def verify():
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    obs=json.loads((AUDIT/'terminal-observation.json').read_text());check=json.loads((AUDIT/'CHECK.json').read_text())
    if obs.get('observed_exit')!=0 or obs.get('receipt_sha256')!=PINS[AUDIT/'CHECK.json'] or check.get('status')!='PASS_INDEPENDENT_THIRTEEN_ENDPOINT_SUCCESSOR_PAIR_AUDIT':raise ValueError('invalid endpoint audit')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],text=True,capture_output=True,timeout=900)
    if p.returncode or p.stderr:raise ValueError(('endpoint audit failed',p.returncode,p.stdout,p.stderr))
    before=json.loads(p.stdout)
    if before!=check:raise ValueError('endpoint audit differs from receipt')
    for index,(directory,review,status) in enumerate(REBUILT_AUDITS):
        receipt=BASE/directory/'evidence/receipt.json';checked=json.loads((ROOT/'reviews'/review/'CHECK.json').read_text());meta=json.loads(receipt.read_text())
        source=STEPS[index][1]
        if checked.get('status')!=status or checked.get('recorded_outer_exit')!=0 or checked.get('author_receipt_sha256')!=PINS[receipt] or meta.get('fixed_inputs_sha256',{}).get(str(source))!=PINS[source]:raise ValueError(('invalid audited source',directory))
    metas={}
    for module,directory,run,review,status,reviewstatus in SEEDS:
        receipt=BASE/directory/'evidence/receipt.json';audit=ROOT/'reviews'/review/'CHECK.json';meta=json.loads(receipt.read_text());checked=json.loads(audit.read_text())
        digest=checked_receipt_digest(checked,module)
        if meta.get('status')!=status or len(meta['runs'])!=2 or checked.get('status')!=reviewstatus or checked.get('recorded_outer_exit')!=0 or digest!=PINS[receipt] or meta['parent_audit']!=before:raise ValueError(('invalid parent',module))
        for row in meta['runs']:
            if row['compiler_exit'] or row['deps_exit'] or H(Path('/tmp')/run/row['label']/(module+'.olean'))!=row['object_sha256']:raise ValueError(('seed drift',module,row['label']))
        metas[module]=meta
    for label in ('author','peer'):
        row=lambda module:next(r for r in metas[module]['runs'] if r['label']==label)
        if row('CompactConcreteMask')['seed_sha256']!=row('CompactListMask')['object_sha256']:raise ValueError(('seed dependency drift',label))
    return before,metas

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);out=ap.parse_args().output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact-concrete-increment-pair-') or out.exists() or out.is_symlink():raise ValueError('use a fresh direct /tmp/ipra-compact-concrete-increment-pair-* path')
    before,metas=verify();monitor=load(MONITOR);out.mkdir();runs=[]
    for label in ('author','peer'):
        run=out/label;root=run/'src';(root/'DiophantineConsistency').mkdir(parents=True);lib=run/'lib';monitor.overlay(PREFIX/label/'lib',lib);seeds={}
        for module,_,parent_run,_,_,_ in SEEDS:
            dst=lib/'DiophantineConsistency'/(module+'.olean')
            if dst.exists() or dst.is_symlink():raise ValueError(('seed path occupied',module))
            shutil.copyfile(Path('/tmp')/parent_run/label/(module+'.olean'),dst)
            row=next(r for r in metas[module]['runs'] if r['label']==label)
            if H(dst)!=row['object_sha256']:raise ValueError(('seed copy drift',module,label))
            seeds[module]=H(dst)
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(PACKAGE); steps=[]
        for module,source,imports,count in STEPS:
            src=root/'DiophantineConsistency'/(module+'.lean');obj=lib/'DiophantineConsistency'/(module+'.olean');log=run/(module+'.log')
            if obj.exists() or obj.is_symlink():raise ValueError(('module output occupied',module))
            shutil.copyfile(source,src)
            cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
            code,peak,reason=monitor.monitored(cmd,env,log);text=log.read_text();reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M)
            if code or reason or 'warning:' in text or 'error:' in text or 'sorryAx' in text or len(reports)!=count:raise ValueError(('compiler failure',label,module,code,reason,text[-8000:]))
            if any({x.strip() for x in ax.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for _,ax in reports):raise ValueError(('unexpected axioms',label,module,reports))
            deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
            expected={str(PACKAGE/'Init.olean')}|{str(lib/'DiophantineConsistency'/(name+'.olean')) for name in imports}
            if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('direct import drift',label,module,deps.returncode,deps.stdout,deps.stderr))
            if H(src)!=PINS[source]:raise ValueError(('source drift',label,module))
            steps.append({'module':module,'compiler_exit':code,'deps_exit':deps.returncode,'deps_stdout':deps.stdout,'command':cmd,'source_sha256':H(src),'object_sha256':H(obj),'log_sha256':H(log),'stdout':text,'axiom_reports':reports,'sampled_peak_rss_bytes':peak,'stop_reason':reason})
            print(label,module,'exit',code,'peak_RSS',peak,flush=True)
        runs.append({'label':label,'seed_sha256':seeds,'steps':steps})
    if [{k:v for k,v in r.items() if k not in ('command','deps_stdout','sampled_peak_rss_bytes')} for r in runs[0]['steps']]!=[{k:v for k,v in r.items() if k not in ('command','deps_stdout','sampled_peak_rss_bytes')} for r in runs[1]['steps']]:raise ValueError('paired step outputs differ')
    after,metas2=verify()
    if before!=after or metas!=metas2:raise ValueError('parent drift')
    receipt={'status':'PASS_PAIRED_COMPACT_CONCRETE_INCREMENT','runs':runs,'parent_audit':after,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'scope':'Conditional IΣ₁ model decoder for symbolic compact mask with explicit NoCarry; no retained MC/graph port binding, machine, checker or PRA proof; no full package-transitive/dynamic ancestry audit.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_COMPACT_CONCRETE_INCREMENT',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
