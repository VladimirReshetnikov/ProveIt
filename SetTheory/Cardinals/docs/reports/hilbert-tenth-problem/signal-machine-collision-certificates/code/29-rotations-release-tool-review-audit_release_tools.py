#!/usr/bin/env python3
"""Independent packaging/tool checks. Never imports or executes science code."""
import hashlib, json, os, shutil, stat, subprocess, sys, time, zipfile
from pathlib import Path

SOURCE=Path('/workspace/shared/five-signal-rotation-family59-release-20261004')
HERE=Path(__file__).resolve().parent
WORK=HERE/'scratch'
OUT=HERE/'outputs'
LOG=HERE/'command-logs'
PY='/usr/bin/python3'
FROZEN=('science','independent-audit','dependencies','real-input','real-input-audit','real-input-dependencies')
RESULTS=[]
def sha(b): return hashlib.sha256(b).hexdigest()
def write_json(p,x): p.write_text(json.dumps(x,sort_keys=True,indent=2)+'\n')
def inventory(root):
    rows={}
    for p in sorted(root.rglob('*')):
        s=p.lstat()
        if stat.S_ISREG(s.st_mode): rows[p.relative_to(root).as_posix()]={'bytes':s.st_size,'sha256':sha(p.read_bytes())}
        elif not stat.S_ISDIR(s.st_mode): rows[p.relative_to(root).as_posix()]={'type':stat.S_IFMT(s.st_mode)}
    return rows
def frozen(root): return {d:inventory(root/d) for d in FROZEN}
def record(name,ok,**detail):
    RESULTS.append({'name':name,'pass':bool(ok),**detail})
    write_json(HERE/'TEST_RESULTS.json',RESULTS)
    print(('PASS ' if ok else 'FAIL ')+name,flush=True)
def call(name,root,tool,args,expect=0,flags=('-I','-S','-B'),env=None):
    argv=[PY,*flags,str(root/'tools'/tool),*map(str,args)]
    start=time.monotonic()
    p=subprocess.run(argv,cwd=OUT,env=env,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=240)
    (LOG/(name+'.log')).write_text(p.stdout)
    record(name,p.returncode==expect,returncode=p.returncode,expected_returncode=expect,seconds=round(time.monotonic()-start,3),argv=argv,output_tail=p.stdout[-1600:])
    return p
def copy(name):
    p=WORK/name;shutil.copytree(WORK/'pristine',p,symlinks=True);return p

def main():
    if WORK.exists() or OUT.exists(): raise ValueError('Use fresh audit directory')
    for p in (WORK,OUT,LOG):p.mkdir()
    before=frozen(SOURCE)
    shutil.copytree(SOURCE,WORK/'pristine',symlinks=True)
    root=WORK/'pristine'
    pins=json.loads((root/'manuscript/MANUSCRIPT_PINS.json').read_text())
    snap=inventory(root)
    write_json(HERE/'SOURCE_SNAPSHOT.json',{'source':str(SOURCE),'files':snap,'manuscript_pins':pins,'frozen_before':before})
    record('snapshot_source_preserved',before==frozen(SOURCE))
    call('release_check_inputs_clean',root,'release59.py',['check-inputs'])
    for tool,action in [('build_report59.py',['--output-dir',OUT/'flags-build']),('derive_presentation.py',['--output-dir',OUT/'flags-derive']),('release59.py',['check-inputs'])]:
        for label,flags in [('ordinary',()),('optimized',('-I','-S','-B','-O')),('no_site_missing',('-I','-B')),('bytecode_missing',('-I','-S'))]:
            call(tool[:-3]+'_'+label,root,tool,action,expect=2 if tool!='derive_presentation.py' else 1,flags=flags)
    (OUT/'existing-file').write_text('KEEP EXACTLY\n');(OUT/'existing-dir').mkdir();(OUT/'existing-dir/marker').write_text('KEEP EXACTLY\n')
    (OUT/'real-parent').mkdir();(OUT/'link-parent').symlink_to(OUT/'real-parent',target_is_directory=True)
    (OUT/'link-output').symlink_to(OUT/'existing-file')
    bad={'relative':'relative','double-slash':'/'+str(OUT/'double'),'dot':str(OUT)+'/./dot','dotdot':str(OUT)+'/real-parent/../dotdot','trailing':str(OUT/'trailing')+'/', 'inside':str(root/'new-output'),'ancestor':str(root.parent), 'missing-parent':str(OUT/'absent/leaf'),'existing-file':str(OUT/'existing-file'),'existing-dir':str(OUT/'existing-dir'),'symlink-leaf':str(OUT/'link-output'),'symlink-parent':str(OUT/'link-parent/new')}
    for tool in ('build_report59.py','derive_presentation.py','release59.py'):
        for label,dest in bad.items():
            args=['manifest','--output',dest] if tool=='release59.py' else ['--output-dir',dest]
            call(tool[:-3]+'_path_'+label,root,tool,args,expect=1 if tool=='derive_presentation.py' else 2)
    record('existing_destinations_preserved',(OUT/'existing-file').read_text()=='KEEP EXACTLY\n' and (OUT/'existing-dir/marker').read_text()=='KEEP EXACTLY\n' and (OUT/'link-output').is_symlink())
    # Every frozen subdirectory is subjected to the same five modifications.
    for d in FROZEN+('manuscript',):
        leaf=next(p.relative_to(root) for p in sorted((root/d).rglob('*')) if p.is_file())
        for kind in ('extra','missing','tampered','symlink','hardlink','directory-symlink'):
            r=copy(d+'-'+kind);p=r/leaf
            if kind=='extra':(r/d/'UNEXPECTED.txt').write_text('unexpected\n')
            elif kind=='missing':p.unlink()
            elif kind=='tampered':p.write_bytes(p.read_bytes()+b'\nTAMPER\n')
            elif kind=='symlink':p.unlink();p.symlink_to(root/leaf)
            elif kind=='hardlink':p.unlink();os.link(root/leaf,p)
            else:
                shutil.rmtree(r/d);(r/d).symlink_to(root/d,target_is_directory=True)
            call('release_'+d+'_'+kind,r,'release59.py',['check-inputs'],expect=2)
            # Remove each copy before the next case; avoids leaving source hard links.
            shutil.rmtree(r)
    for kind in ('extra','missing','tampered','symlink','hardlink'):
        r=copy('build-'+kind);p=r/'manuscript/report59.tex'
        if kind=='extra':(r/'manuscript/UNEXPECTED.txt').write_text('unexpected\n')
        elif kind=='missing':p.unlink()
        elif kind=='tampered':p.write_bytes(p.read_bytes()+b'\nTAMPER\n')
        elif kind=='symlink':p.unlink();p.symlink_to(root/'manuscript/report59.tex')
        else:p.unlink();os.link(root/'manuscript/report59.tex',p)
        call('build_manuscript_'+kind,r,'build_report59.py',['--output-dir',OUT/('build-bad-'+kind)],expect=2)
        shutil.rmtree(r)
    for kind in ('missing','tampered','symlink','hardlink','directory-symlink'):
        r=copy('derive-'+kind);p=r/'science/evidence/STATIC_RECEIPT.json'
        if kind=='missing':p.unlink()
        elif kind=='tampered':p.write_bytes(p.read_bytes()+b'\nTAMPER\n')
        elif kind=='symlink':p.unlink();p.symlink_to(root/'science/evidence/STATIC_RECEIPT.json')
        elif kind=='hardlink':p.unlink();os.link(root/'science/evidence/STATIC_RECEIPT.json',p)
        else:shutil.rmtree(r/'science');(r/'science').symlink_to(root/'science',target_is_directory=True)
        call('derive_evidence_'+kind,r,'derive_presentation.py',['--output-dir',OUT/('derive-bad-'+kind)],expect=1)
        shutil.rmtree(r)
    call('derive_clean',root,'derive_presentation.py',['--output-dir',OUT/'derived'])
    record('derived_sources_match_pinned_manuscript',all((OUT/'derived'/n).read_bytes()==(root/'manuscript'/n).read_bytes() for n in ('fixture-table.tex','geometry-figure.tex')))
    # Only two full builds are planned. Their complete logs and receipts are retained.
    p=call('build_clean',root,'build_report59.py',['--output-dir',OUT/'build-clean'])
    if p.returncode==0:
        relocated=copy('relocated release with spaces')
        shutil.copyfile(OUT/'build-clean/Report59.pdf',relocated/'Report59.pdf')
        poison=OUT/'poison';poison.mkdir();(poison/'scratch').mkdir()
        (poison/'sitecustomize.py').write_text("raise RuntimeError('PYTHONPATH poison loaded')\n")
        (poison/'usercustomize.py').write_text("raise RuntimeError('PYTHONPATH poison loaded')\n")
        (poison/'article.cls').write_text("\\errmessage{HOSTILE TEXINPUTS LOADED}\n")
        for name in ('pdftex','pdflatex','kpsewhich','pdftotext','pdftoppm','pdfinfo'):
            p=poison/name;p.write_text('#!/bin/sh\necho HOSTILE-PATH-EXECUTED\nexit 73\n');p.chmod(0o755)
        hostile={**os.environ,'PATH':str(poison),'PYTHONPATH':str(poison),'PYTHONHOME':'/does/not/exist','PYTHONOPTIMIZE':'2','PYTHONDONTWRITEBYTECODE':'','HOME':str(poison),'TMPDIR':str(poison/'scratch'),'TEXINPUTS':str(poison)+'//:','TEXFORMATS':str(poison),'TEXMF':str(poison),'TEXMFCNF':str(poison),'TEXFONTMAPS':str(poison),'SOURCE_DATE_EPOCH':'1','FORCE_SOURCE_DATE':'0','TZ':'Pacific/Honolulu','LANG':'invalid_locale','LC_ALL':'invalid_locale','openin_any':'a','openout_any':'a','shell_escape':'t'}
        call('build_relocated_hostile',relocated,'build_report59.py',['--output-dir',OUT/'build-hostile','--require-packaged-match'],env=hostile)
        if (OUT/'build-hostile/BUILD_RECEIPT.json').exists():
            for label,names in [('pdf',['Report59.pdf']),('text',['Report59.txt']),('pages',sorted(p.relative_to(OUT/'build-clean').as_posix() for p in (OUT/'build-clean/pages').glob('*.png')))]:
                record('deterministic_'+label,all((OUT/'build-clean'/n).read_bytes()==(OUT/'build-hostile'/n).read_bytes() for n in names),files=names)
            c=json.loads((OUT/'build-clean/BUILD_RECEIPT.json').read_text());h=json.loads((OUT/'build-hostile/BUILD_RECEIPT.json').read_text())
            record('exact_pins_used',c['manuscript_pins']==pins==h['manuscript_pins'],pins=pins)
            record('render_inventory_complete',len(list((OUT/'build-clean/pages').glob('*.png')))==c['render_pages'] and c['render_pages']>0,pages=c['render_pages'])
    # Pin the scratch release; this is a packaging exercise, not publication.
    m=OUT/'MANIFEST.json';call('manifest_clean',root,'release59.py',['manifest','--output',m])
    shutil.copyfile(m,root/'MANIFEST.json');pin=sha(m.read_bytes())
    call('verify_clean',root,'release59.py',['verify','--manifest-sha256',pin])
    call('verify_wrong_pin',root,'release59.py',['verify','--manifest-sha256','0'*64],expect=2)
    for kind in ('extra','missing','tampered','symlink','hardlink'):
        r=copy('manifest-'+kind);p=r/'qa/PRESENTATION_RECEIPT.json'
        if kind=='extra':(r/'EXTRA.txt').write_text('extra\n')
        elif kind=='missing':p.unlink()
        elif kind=='tampered':p.write_bytes(p.read_bytes()+b'\nTAMPER\n')
        elif kind=='symlink':p.unlink();p.symlink_to(root/'qa/PRESENTATION_RECEIPT.json')
        else:p.unlink();os.link(root/'qa/PRESENTATION_RECEIPT.json',p)
        call('verify_'+kind,r,'release59.py',['verify','--manifest-sha256',pin],expect=2);shutil.rmtree(r)
    for n in (1,2):call('archive_'+str(n),root,'release59.py',['archive','--manifest-sha256',pin,'--output',OUT/f'release-{n}.zip'])
    for label,dest in bad.items():call('archive_path_'+label,root,'release59.py',['archive','--manifest-sha256',pin,'--output',dest],expect=2)
    record('deterministic_zip',(OUT/'release-1.zip').read_bytes()==(OUT/'release-2.zip').read_bytes(),sha256=sha((OUT/'release-1.zip').read_bytes()))
    release_inventory=inventory(root)
    manifest=json.loads(m.read_text())
    record('manifest_exact_file_inventory',manifest['files']=={n:r for n,r in release_inventory.items() if n!='MANIFEST.json'},files=len(manifest['files']))
    with zipfile.ZipFile(OUT/'release-1.zip') as z:
        record('zip_exact_file_inventory',z.namelist()==sorted(release_inventory),files=len(z.namelist()))
        record('zip_exact_bytes',all(sha(z.read(n))==release_inventory[n]['sha256'] for n in z.namelist()))
        record('zip_safe_metadata',all(i.date_time==(2026,10,4,0,0,0) and i.create_system==3 and i.external_attr>>16==(stat.S_IFREG|0o444) and i.compress_type==zipfile.ZIP_DEFLATED for i in z.infolist()))
    record('frozen_scratch_preserved',before==frozen(root))
    record('frozen_production_preserved',before==frozen(SOURCE))
    record('no_bytecode_generated',not any(WORK.rglob('*.pyc')) and not any(WORK.rglob('__pycache__')))
    write_json(HERE/'SUMMARY.json',{'tests':len(RESULTS),'passed':sum(r['pass'] for r in RESULTS),'failed':[r['name'] for r in RESULTS if not r['pass']],'source_manuscript_pins':pins,'manifest_sha256':pin,'final_frozen_source':frozen(SOURCE),'scope':'Independent release-tool and packaging checks; no scientific program executed'})
if __name__=='__main__':main()
