#!/usr/bin/env python3
"""Owned fixture-only tests for Report58 build and release guards.
No author or scientific checker is run. All writes are in a new temporary tree.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent.parent

def need(ok,msg):
    if not ok:raise RuntimeError(msg)

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    need(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and sys.flags.optimize==0,'Use python3 -I -S -B without optimization')
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',required=True);args=ap.parse_args()
    need(args.receipt.startswith('/') and not args.receipt.startswith('//'),'Receipt must be canonical absolute path')
    receipt=Path(args.receipt)
    need(str(receipt)==args.receipt and all(x not in ('.','..') for x in args.receipt.split('/')),'Receipt must have no dot components or path aliases')
    need(not os.path.lexists(receipt) and receipt.parent.is_dir(),'Receipt must be new with existing parent')
    for p in (receipt,*receipt.parents):need(not p.is_symlink(),'Receipt path may not contain symlinks')
    need(ROOT not in receipt.parents,'Receipt must be external to release')
    workspace=Path(tempfile.mkdtemp(prefix='report58-tool-tests-'))
    before={str(p.relative_to(ROOT)):sha(p) for p in ROOT.rglob('*') if p.is_file()}
    template=workspace/'template';(template/'tools').mkdir(parents=True);(template/'verification').mkdir()
    for name in ('release.py','build_report.py'):
        shutil.copyfile(ROOT/'tools'/name,template/'tools'/name)
    shutil.copyfile(ROOT/'Report58.tex',template/'Report58.tex')
    shutil.copyfile(ROOT/'Report58.pdf',template/'Report58.pdf')
    for name in ('README.md','verification/REPLAY_RECEIPT.json','verification/RENDER_REVIEW.json'):
        (template/name).write_text('fixture only\n')
    (template/'empty-directory').mkdir()
    tests=[]
    def clone(name):
        dest=workspace/name;shutil.copytree(template,dest);return dest
    def invoke(root,action,extra=(),ok=False,flags=('-I','-S','-B'),tool='release.py'):
        r=subprocess.run([sys.executable,*flags,str(root/'tools'/tool),*action,*map(str,extra)],
             cwd=workspace,env={'PATH':'/usr/bin:/bin','LANG':'C.UTF-8'},capture_output=True,text=True,timeout=120)
        need((r.returncode==0)==ok,'Unexpected outcome: '+str(action)+' '+r.stdout+r.stderr)
        return r
    def record(name,root,action,extra=(),ok=False,flags=('-I','-S','-B'),tool='release.py'):
        r=invoke(root,action,extra,ok,flags,tool);tests.append({'case':name,'expected_success':ok,'returncode':r.returncode})
    base=clone('base')
    record('seal_once',base,['seal'],ok=True)
    record('verify_clean',base,['verify'],ok=True)
    record('release_nonisolated_refused',base,['verify'],flags=('-B',))
    record('release_optimization_refused',base,['verify'],flags=('-I','-S','-B','-O'))
    record('seal_reuse_refused',base,['seal'])
    missing=clone('directory-prerequisite');(missing/'Report58.pdf').unlink();(missing/'Report58.pdf').mkdir()
    record('directory_prerequisite_refused',missing,['seal'])
    z1=workspace/'a.zip';z2=workspace/'b.zip'
    record('first_zip',base,['zip'],['--output',z1],True)
    record('second_zip',base,['zip'],['--output',z2],True)
    need(z1.read_bytes()==z2.read_bytes(),'ZIP nondeterminism')
    tests.append({'case':'zip_byte_identity','expected_success':True,'returncode':0})
    import zipfile
    extracted=workspace/'extracted';extracted.mkdir()
    with zipfile.ZipFile(z1) as archive:archive.extractall(extracted)
    record('zip_extracted_full_inventory',extracted,['verify'],ok=True)
    record('zip_reuse_refused',base,['zip'],['--output',z1])
    record('zip_inside_release_refused',base,['zip'],['--output',base/'bad.zip'])
    record('zip_relative_refused',base,['zip'],['--output','bad.zip'])
    record('zip_parent_dot_refused',base,['zip'],['--output',str(workspace)+'/../bad.zip'])
    record('zip_double_slash_refused',base,['zip'],['--output','/'+str(workspace/'bad.zip')])
    record('zip_missing_parent_refused',base,['zip'],['--output',workspace/'missing'/'bad.zip'])
    link=workspace/'parent-link';link.symlink_to(workspace,target_is_directory=True)
    record('zip_symlink_ancestor_refused',base,['zip'],['--output',link/'bad.zip'])
    broken=workspace/'broken.zip';broken.symlink_to(workspace/'absent.zip')
    record('zip_dangling_output_refused',base,['zip'],['--output',broken])
    # Mutations use copies of the sealed fixture, never the release.
    for kind in ('file_add','file_change','file_remove','directory_add','directory_remove','symlink_live','symlink_dead','fifo','hardlink','manifest_symlink','cache_add'):
        p=workspace/('mutation-'+kind);shutil.copytree(base,p)
        if kind=='file_add':(p/'extra.txt').write_text('x')
        elif kind=='file_change':(p/'README.md').write_text('changed')
        elif kind=='file_remove':(p/'README.md').unlink()
        elif kind=='directory_add':(p/'unexpected').mkdir()
        elif kind=='directory_remove':(p/'empty-directory').rmdir()
        elif kind=='symlink_live':(p/'link').symlink_to(p/'README.md')
        elif kind=='symlink_dead':(p/'link').symlink_to(p/'absent')
        elif kind=='fifo':os.mkfifo(p/'pipe')
        elif kind=='hardlink':os.link(p/'README.md',p/'linked')
        elif kind=='manifest_symlink':
            (p/'MANIFEST.json').unlink();(p/'MANIFEST.json').symlink_to(base/'MANIFEST.json')
        elif kind=='cache_add':(p/'__pycache__').mkdir()
        record('verify_'+kind+'_refused',p,['verify'])
    # Build guards operate before the installed TeX commands start.
    b=clone('build-guards');build='build_report.py'
    for name,out in [('existing',workspace),('inside',b/'bad'),('relative',Path('bad')),('double_slash','/'+str(workspace/'bad')),('missing_parent',workspace/'missing'/'bad'),('symlink_parent',link/'bad')]:
        record('build_'+name+'_refused',b,['--output-dir',str(out)],tool=build)
    record('build_optimization_refused',b,['--output-dir',str(workspace/'opt')],flags=('-I','-S','-B','-O'),tool=build)
    record('build_nonisolated_refused',b,['--output-dir',str(workspace/'nonisolated')],flags=('-B',),tool=build)
    (b/'Report58.tex').write_text('tampered')
    record('build_source_tamper_refused',b,['--output-dir',str(workspace/'tampered')],tool=build)
    after={str(p.relative_to(ROOT)):sha(p) for p in ROOT.rglob('*') if p.is_file()}
    need(before==after,'Original release bytes changed')
    result={'status':'PASS','workspace':str(workspace),'cases':tests,'case_count':len(tests),
      'deterministic_zip_sha256':sha(z1),'original_release_files_preserved':True,
      'scope':'Fixture-only filesystem/manifest/archive/build-input guard tests; no scientific programs executed.',
      'tools_sha256':{n:sha(ROOT/'tools'/n) for n in ('release.py','build_report.py','test_release.py')}}
    with receipt.open('x') as f:f.write(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS','cases':len(tests),'receipt':str(receipt)},sort_keys=True))

if __name__=='__main__':main()
