#!/usr/bin/env python3
"""Focused regression of inspected revised release tools; scratch copies only."""
import hashlib,json,os,runpy,shutil,stat,subprocess,sys,zipfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
BASE=HERE/'revised'
SOURCE=Path('/workspace/shared/five-signal-rotation-family59-release-20261004')
REFERENCE=Path('/workspace/shared/report59-draft7-build-20261004')
RESULTS=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def save():
    (BASE/'REGRESSION_RESULTS.json').write_text(json.dumps(RESULTS,sort_keys=True,indent=2)+'\n')
def check(name,ok,**detail):
    RESULTS.append({'name':name,'pass':bool(ok),**detail});save();print(('PASS ' if ok else 'FAIL ')+name,flush=True)
def inventory(root):return {p.relative_to(root).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in sorted(root.rglob('*')) if p.is_file()}
def copy(name):
    r=BASE/name;shutil.copytree(BASE/'pristine',r,symlinks=True);return r
def call(name,root,tool,args,expected=0,env=None):
    p=subprocess.run(['/usr/bin/python3','-I','-S','-B',str(root/'tools'/tool),*map(str,args)],env=env,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=240)
    (BASE/(name+'.log')).write_text(p.stdout)
    check(name,p.returncode==expected,returncode=p.returncode,expected_returncode=expected,output_tail=p.stdout[-2000:]);return p
def main():
    BASE.mkdir();shutil.copytree(SOURCE,BASE/'pristine',symlinks=True);r=BASE/'pristine'
    snapshot=inventory(r)
    (BASE/'SOURCE_SNAPSHOT.json').write_text(json.dumps(snapshot,sort_keys=True,indent=2)+'\n')
    call('clean_input_check',r,'release59.py',['check-inputs'])
    for case in ('missing-frozen-directory','symlink-frozen-directory','symlink-manuscript-directory','unexpected-fifo'):
        root=copy(case);directory='manuscript' if case=='symlink-manuscript-directory' else 'real-input'
        if case=='unexpected-fifo':os.mkfifo(root/directory/'UNEXPECTED_FIFO')
        else:
            shutil.rmtree(root/directory)
            if case.startswith('symlink'):(root/directory).symlink_to(r/directory,target_is_directory=True)
        m=runpy.run_path(str(root/'tools/build_report59.py'),run_name='revised_snapshot_probe')
        try:m['snapshot']();refused=False;error=None
        except Exception as e:refused=True;error=str(e)
        check(case,refused,error=error)
        call(case+'_cli',root,'build_report59.py',['--output-dir',BASE/(case+'-output')],expected=2)
        check(case+'_no_output',not (BASE/(case+'-output')).exists())
        shutil.rmtree(root)
    root=copy('repinned-manuscript');p=root/'manuscript/report59.tex';p.write_bytes(p.read_bytes()+b'\n% CHANGED AFTER REVIEW\n')
    p=root/'manuscript/MANUSCRIPT_PINS.json';pins=json.loads(p.read_text());pins['report59.tex']=sha((root/'manuscript/report59.tex').read_bytes());p.write_text(json.dumps(pins,sort_keys=True,indent=2)+'\n')
    call('repinned_build_refused',root,'build_report59.py',['--output-dir',BASE/'repinned-output'],expected=2)
    call('repinned_release_refused',root,'release59.py',['check-inputs'],expected=2)
    check('repinned_no_output',not (BASE/'repinned-output').exists());shutil.rmtree(root)
    # Give this scratch release its own externally produced, independently verified manifest.
    p=BASE/'manifest.json';call('manifest_clean',r,'release59.py',['manifest','--output',p]);shutil.copyfile(p,r/'MANIFEST.json');pin=sha(p.read_bytes())
    call('verify_clean',r,'release59.py',['verify','--manifest-sha256',pin])
    for case in ('manifest-output-race','archive-output-race','archive-input-race','archive-write-failure'):
        root=copy(case);out=BASE/(case+'.output');m=runpy.run_path(str(root/'tools/release59.py'),run_name='revised_release_probe');g=m['main'].__globals__;original=m['fresh_file']
        def hook(raw):
            p=original(raw)
            if case=='archive-input-race':
                target=root/'qa/PRESENTATION_RECEIPT.json';target.write_bytes(target.read_bytes()+b'\nRACED-IN CHANGE\n')
            elif case!='archive-write-failure':p.write_bytes(b'EXTERNAL CONCURRENT WRITER\n')
            return p
        g['fresh_file']=hook
        oldzip=zipfile.ZipFile
        if case=='archive-write-failure':
            def fail(*args,**kwargs):raise OSError('Injected failure after exclusive destination creation')
            zipfile.ZipFile=fail
        sys.argv=['release59.py',*(['manifest','--output',str(out)] if case.startswith('manifest') else ['archive','--manifest-sha256',pin,'--output',str(out)])]
        try:m['main']();refused=False;error=None
        except Exception as e:refused=True;error=str(e)
        finally:zipfile.ZipFile=oldzip
        check(case+'_refused',refused,error=error)
        if case in ('manifest-output-race','archive-output-race'):check(case+'_foreign_output_preserved',out.exists() and out.read_bytes()==b'EXTERNAL CONCURRENT WRITER\n')
        elif case=='archive-input-race':check(case+'_no_output',not out.exists())
        else:check(case+'_new_failed_output_retained',out.exists() and out.read_bytes()==b'')
        shutil.rmtree(root)
    for i in (1,2):call('archive_'+str(i),r,'release59.py',['archive','--manifest-sha256',pin,'--output',BASE/f'release-{i}.zip'])
    check('deterministic_archives',(BASE/'release-1.zip').read_bytes()==(BASE/'release-2.zip').read_bytes())
    inv=inventory(r)
    with zipfile.ZipFile(BASE/'release-1.zip') as z:
        check('exact_zip_inventory',z.namelist()==sorted(inv),files=len(inv))
        check('exact_zip_bytes',all(sha(z.read(n))==inv[n]['sha256'] for n in z.namelist()))
        check('zip_matches_embedded_manifest',json.loads(z.read('MANIFEST.json'))['files']=={n:v for n,v in inv.items() if n!='MANIFEST.json'})
    # One fresh isolated hostile-environment post-fix build at the final manuscript pin.
    reference_receipt=json.loads((REFERENCE/'BUILD_RECEIPT.json').read_text())
    check('reference_build_same_pins',reference_receipt['manuscript_pins']==json.loads((r/'manuscript/MANUSCRIPT_PINS.json').read_text()))
    (BASE/'REFERENCE_BUILD_RECEIPT.json').write_bytes((REFERENCE/'BUILD_RECEIPT.json').read_bytes())
    shutil.copyfile(REFERENCE/'Report59.pdf',r/'Report59.pdf')
    poison=HERE/'outputs/poison'
    hostile={**os.environ,'PATH':str(poison),'PYTHONPATH':str(poison),'PYTHONHOME':'/does/not/exist','PYTHONOPTIMIZE':'2','PYTHONDONTWRITEBYTECODE':'','HOME':str(poison),'TMPDIR':str(poison/'scratch'),'TEXINPUTS':str(poison)+'//:','TEXFORMATS':str(poison),'TEXMF':str(poison),'TEXMFCNF':str(poison),'TEXFONTMAPS':str(poison),'SOURCE_DATE_EPOCH':'1','FORCE_SOURCE_DATE':'0','TZ':'Pacific/Honolulu','LANG':'invalid_locale','LC_ALL':'invalid_locale','openin_any':'a','openout_any':'a','shell_escape':'t'}
    call('post_fix_build',r,'build_report59.py',['--output-dir',BASE/'build','--require-packaged-match'],env=hostile)
    if (BASE/'build/BUILD_RECEIPT.json').exists():
        names=['Report59.pdf','Report59.txt',*sorted(p.relative_to(REFERENCE).as_posix() for p in (REFERENCE/'pages').glob('*.png'))]
        check('post_fix_pdf_text_all_pages_identical',all((BASE/'build'/n).read_bytes()==(REFERENCE/n).read_bytes() for n in names),files=len(names),pdf_sha256=sha((BASE/'build/Report59.pdf').read_bytes()))
    frozen=('science','independent-audit','dependencies','real-input','real-input-audit','real-input-dependencies')
    for d in frozen:check('frozen_'+d+'_preserved',inventory(r/d)==inventory(SOURCE/d)=={n[len(d)+1:]:v for n,v in snapshot.items() if n.startswith(d+'/')})
    check('no_bytecode_generated',not any(BASE.rglob('*.pyc')) and not any(BASE.rglob('__pycache__')))
    (BASE/'SUMMARY.json').write_text(json.dumps({'tests':len(RESULTS),'passed':sum(v['pass'] for v in RESULTS),'failed':[v['name'] for v in RESULTS if not v['pass']],'tools':{n:v for n,v in snapshot.items() if n.startswith('tools/')},'manuscript_pins':json.loads((r/'manuscript/MANUSCRIPT_PINS.json').read_text()),'scope':'Post-hardening tool regression, not scientific audit'},sort_keys=True,indent=2)+'\n')
if __name__=='__main__':main()
