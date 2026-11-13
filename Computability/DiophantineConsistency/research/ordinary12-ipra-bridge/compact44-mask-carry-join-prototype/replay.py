#!/usr/bin/env python3
"""Pair a conditional repeated-mask/carry join over four audited parents."""
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent; BASE=HERE.parent; ROOT=HERE.parents[2]
SOURCE=HERE/'CompactMaskToCarry.lean'
PREFIX=Path('/tmp/ipra-thirteen-parent-window-pair-01')
WINDOW=ROOT/'reviews/thirteen-model-parent-window-pair-independent-audit'
MONITOR=BASE/'free-j-current-denominator-composition/replay.py'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PARENTS=(
 ('CompactDummyBound','compact44-dummy-bound-prototype','ipra-compact-dummy-bound-pair-01','compact44-dummy-bound-independent-audit','PASS_PAIRED_COMPACT_DUMMY_BOUND','PASS_INDEPENDENT_COMPACT44_DUMMY_BOUND_AUDIT'),
 ('CompactMaskSlot','compact44-mask-slot-prototype','ipra-compact-mask-slot-pair-01','compact44-mask-slot-independent-audit','PASS_PAIRED_COMPACT_MASK_SLOT','PASS_INDEPENDENT_COMPACT44_MASK_SLOT_AUDIT'),
 ('CompactDigitBound','compact44-scaled-carry-prototype','ipra-compact-scaled-carry-pair-01','compact44-scaled-carry-independent-audit','PASS_PAIRED_COMPACT_SCALED_CARRY','PASS_INDEPENDENT_COMPACT44_SCALED_CARRY_AUDIT'),
 ('CompactScaledCarry','compact44-scaled-end-around-prototype','ipra-compact-scaled-end-around-pair-01','compact44-scaled-end-around-independent-audit','PASS_PAIRED_COMPACT_SCALED_END_AROUND','PASS_INDEPENDENT_COMPACT44_SCALED_END_AROUND_AUDIT'))
PINS = {SOURCE: '738a38a25b0afc76aa0f02fa24040068d4964ea431ec0a88060056c79abef212',
 MONITOR: '2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 LEAN: 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 WINDOW/'audit.py': '679a7680a3e4fbc3a7555bc1ba3a43b543d749311f08760a91ab24433539f4c1',
 WINDOW/'CHECK.json': '4a358f8fd09fa3be38d32aa2314ad063406ea2d363f74d1a13f41dedcc3e0ec9',
 WINDOW/'terminal-observation.json': '516750a20bddd6d87dc5ecd0bdcd904c6d74deb505b5b8b3c6f4ba111f7a2549',
 BASE/'compact44-dummy-bound-prototype'/'replay.py': '70efa8660b0d8f12ed85f5bfc9dc239a168a37517e5a7dd91484b44d76f64e57',
 BASE/'compact44-dummy-bound-prototype'/'evidence/receipt.json': '7332c7a3e4fc13cfaa87308b25349d740ca8fb1c1864b6859640d13a4a294b15',
 ROOT/'reviews'/'compact44-dummy-bound-independent-audit'/'CHECK.json': 'a2a144c733e6a1fee23e07025f95755168000c4b4f538e3911e9d29f5f26052e',
 BASE/'compact44-mask-slot-prototype'/'replay.py': '46c26304a43550ac1a0bd2cadb8c29457a6023dee3d730db29ded74cc909ef59',
 BASE/'compact44-mask-slot-prototype'/'evidence/receipt.json': 'ddef69b4310caef263591491dafe50cc9e9d01542fcaecfb7479c9fa7a0704d9',
 ROOT/'reviews'/'compact44-mask-slot-independent-audit'/'CHECK.json': '7ee25fa5ad3fc966b78491325b2ad2f30c2e0b7a205ddd0e33e23a39d2d68168',
 BASE/'compact44-scaled-carry-prototype'/'replay.py': '2f6288cd4e5fa30b1f9d2f2a4c5a51bc806efe74bf1c24708f8f007cc86dbfc4',
 BASE/'compact44-scaled-carry-prototype'/'evidence/receipt.json': '12adfaa6a0969de59893ce59b6f26ac04d11b87ae03db963e67904a7f06943df',
 ROOT/'reviews'/'compact44-scaled-carry-independent-audit'/'CHECK.json': 'd2352465b3c539902040aea3f9ef189f0930cd10b1ddf3b8306444720c5a03bc',
 BASE/'compact44-scaled-end-around-prototype'/'replay.py': '6aa6b33e51713233cb8d32babe1e9d97c3cfb1059a66e7934f54218e70766f17',
 BASE/'compact44-scaled-end-around-prototype'/'evidence/receipt.json': '03206eda5a10a098f57a2a5a5365ed2a565e1411eb805b4dbff122d0010268e3',
 ROOT/'reviews'/'compact44-scaled-end-around-independent-audit'/'CHECK.json': '6799ed6fc3574187c21854a73e38c52af03708eb41bb103d8f9af6c79200f4ef'}
H=lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(path):
    spec=importlib.util.spec_from_file_location('monitor',path); obj=importlib.util.module_from_spec(spec); spec.loader.exec_module(obj); return obj

def verify():
    for path,digest in PINS.items():
        if H(path)!=digest: raise ValueError(('fixed input drift',str(path)))
    p=subprocess.run([sys.executable,'-I','-S','-B',str(WINDOW/'audit.py')],text=True,capture_output=True,timeout=180)
    if p.returncode or p.stderr: raise ValueError(('window audit failed',p.returncode,p.stdout,p.stderr))
    window=json.loads(p.stdout)
    if window.get('status')!='PASS_INDEPENDENT_24_MODULE_WINDOW_PAIR_AUDIT': raise ValueError('bad window audit')
    metas={}
    for module,directory,run,audit,status,audit_status in PARENTS:
        receipt=BASE/directory/'evidence/receipt.json'; review=ROOT/'reviews'/audit/'CHECK.json'
        meta=json.loads(receipt.read_text()); checked=json.loads(review.read_text())
        if (meta.get('status')!=status or len(meta['runs'])!=2 or checked.get('status')!=audit_status or
            checked.get('recorded_outer_exit')!=0 or checked.get('author_receipt_sha256')!=PINS[receipt]):
            raise ValueError(('invalid parent receipt or audit',module))
        if meta['parent_audit']!=window: raise ValueError(('different window provider',module))
        for row in meta['runs']:
            if row['compiler_exit'] or row['deps_exit'] or H(Path('/tmp')/run/row['label']/(module+'.olean'))!=row['object_sha256']:
                raise ValueError(('parent object drift',module,row['label']))
        metas[module]=meta
    for label in ('author','peer'):
        row=lambda name: next(r for r in metas[name]['runs'] if r['label']==label)
        if row('CompactMaskSlot')['seed_sha256']!=row('CompactDummyBound')['object_sha256'] or row('CompactScaledCarry')['seed_sha256']!=row('CompactDigitBound')['object_sha256']:
            raise ValueError(('parent dependency drift',label))
    return window,metas

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);out=ap.parse_args().output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact-mask-carry-join-pair-') or out.exists() or out.is_symlink():
        raise ValueError('use a fresh direct /tmp/ipra-compact-mask-carry-join-pair-* path')
    before,metas=verify(); monitor=load(MONITOR);out.mkdir();runs=[]
    for label in ('author','peer'):
        run=out/label;root=run/'src';root.mkdir(parents=True);src=root/'DiophantineConsistency/CompactMaskToCarry.lean';src.parent.mkdir(parents=True);obj=run/'CompactMaskToCarry.olean';log=run/'compiler.log'
        shutil.copyfile(SOURCE,src);lib=run/'lib';monitor.overlay(PREFIX/label/'lib',lib);seed_hashes={}
        for module,_,parent_run,_,_,_ in PARENTS:
            target=lib/'DiophantineConsistency'/(module+'.olean')
            if target.exists() or target.is_symlink(): raise ValueError(('occupied seed path',module))
            shutil.copyfile(Path('/tmp')/parent_run/label/(module+'.olean'),target)
            row=next(r for r in metas[module]['runs'] if r['label']==label)
            if H(target)!=row['object_sha256']: raise ValueError(('copied seed drift',module,label))
            seed_hashes[module]=H(target)
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'): env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(PACKAGE)
        cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        code,peak,reason=monitor.monitored(cmd,env,log); output=log.read_text()
        reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",output,re.M)
        names={'CompactMaskToCarry.repeated_mask_class','CompactMaskToCarry.repeated_mask_digit_le_three','CompactMaskToCarry.digit_le_three_of_mask','CompactMaskToCarry.carry_input_of_mask'}
        if code or reason or 'warning:' in output or 'error:' in output or 'sorryAx' in output or {n for n,_ in reports}!=names or len(reports)!=4:
            raise ValueError(('compiler failure',label,code,reason,output[-8000:]))
        if any({x.strip() for x in ax.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for _,ax in reports): raise ValueError(('unexpected axiom',label,reports))
        deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(PACKAGE/'Init.olean'),str(lib/'DiophantineConsistency/CompactScaledCarry.olean'),str(lib/'DiophantineConsistency/CompactMaskSlot.olean')}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected: raise ValueError(('direct import drift',label,deps.returncode,deps.stdout,deps.stderr))
        if H(src)!=PINS[SOURCE]: raise ValueError(('source drift',label))
        runs.append({'label':label,'compiler_exit':code,'command':cmd,'object_sha256':H(obj),'source_sha256':H(src),'seed_sha256':seed_hashes,'log_sha256':H(log),'stdout':output,'axiom_reports':reports,'sampled_peak_rss_bytes':peak,'stop_reason':reason,'deps_exit':deps.returncode,'deps_stdout':deps.stdout})
        print(label,'exit',code,'peak_RSS',peak,flush=True)
    if runs[0]['object_sha256']!=runs[1]['object_sha256'] or runs[0]['axiom_reports']!=runs[1]['axiom_reports']: raise ValueError('paired outputs differ')
    after,metas2=verify()
    if before!=after or metas!=metas2: raise ValueError('parents changed')
    receipt={'status':'PASS_PAIRED_COMPACT_MASK_CARRY_JOIN','runs':runs,'parent_audit':after,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'scope':'Conditional arbitrary-model repetition and D=3 carry-input join; no concrete compact mask classification, graph, machine, checker, PRA proof, complete provider axiom inventory, or full package/dynamic ancestry audit.'}
    with (out/'receipt.json').open('x') as f: json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_COMPACT_MASK_CARRY_JOIN',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
