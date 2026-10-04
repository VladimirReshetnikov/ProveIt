#!/usr/bin/env python3
"""Independent Report64 release-only contract tests. Never runs scientific code.
Inputs: --release PATH --accepted-json PATH --work PATH --dossier PATH.
Mutations occur only in new external fixtures. Run with python3 -I -S -B.
"""
import argparse, hashlib, json, os, re, runpy, shutil, stat, struct, subprocess, sys, time, zlib, zipfile
from pathlib import Path


def digest(data): return hashlib.sha256(data).hexdigest()
def dump(p, obj): p.write_text(json.dumps(obj, sort_keys=True, indent=2)+'\n')
def check(value, label):
    if not value: raise AssertionError(label)
def inventory(root):
    result = {}
    for p in [root, *sorted(root.rglob('*'))]:
        s=p.lstat(); row={'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns,'kind':stat.S_IFMT(s.st_mode),'nlink':s.st_nlink}
        if stat.S_ISREG(s.st_mode):
            data=p.read_bytes(); row.update(bytes=len(data),sha256=digest(data))
        elif stat.S_ISLNK(s.st_mode): row['target']=os.readlink(p)
        result['.' if p==root else p.relative_to(root).as_posix()]=row
    return result

def independent_png(data):
    check(data[:8]==b'\x89PNG\r\n\x1a\n','independent PNG signature')
    pos=8; ids=[]; compressed=b''; w=h=0
    while pos<len(data):
        check(pos+12<=len(data),'independent PNG framing')
        n=struct.unpack('>I',data[pos:pos+4])[0]; tag=data[pos+4:pos+8]; payload=data[pos+8:pos+8+n]
        end=pos+n+12; check(end<=len(data),'independent PNG payload')
        check(struct.unpack('>I',data[end-4:end])[0]==(zlib.crc32(tag+payload)&0xffffffff),'independent PNG CRC')
        if tag==b'IHDR':
            check(not ids and n==13,'independent PNG IHDR')
            w,h,d,c,z,f,i=struct.unpack('>IIBBBBB',payload); check(0<w<=10000 and 0<h<=10000 and (d,c,z,f,i)==(8,2,0,0,0),'independent PNG format')
        elif tag==b'pHYs': check(ids==[b'IHDR'] and n==9,'independent PNG pHYs')
        elif tag==b'IDAT': compressed+=payload
        elif tag==b'IEND': check(n==0 and end==len(data),'independent PNG terminator')
        else: raise AssertionError('unknown PNG chunk')
        ids.append(tag); pos=end
    check(ids[0]==b'IHDR' and ids[-1]==b'IEND' and compressed,'independent PNG chunks')
    dec=zlib.decompressobj(); raw=dec.decompress(compressed,h*(1+3*w)+1)
    check(dec.eof and not dec.unused_data and not dec.unconsumed_tail and len(raw)==h*(1+3*w),'independent PNG raster')
    check(all(raw[i*(1+3*w)]<=4 for i in range(h)),'independent PNG filters')
    return {'width':w,'height':h,'sha256':digest(data),'bytes':len(data)}

def main():
    check(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode,'isolated execution')
    ap=argparse.ArgumentParser(); ap.add_argument('--release',required=True); ap.add_argument('--accepted-json',required=True); ap.add_argument('--work',required=True); ap.add_argument('--dossier',required=True); a=ap.parse_args()
    source=Path(a.release); out=Path(a.work); dossier=Path(a.dossier); accepted=json.loads(Path(a.accepted_json).read_bytes())
    check(not out.exists() and source not in out.parents,'fresh external independent work root'); out.mkdir(mode=0o700)
    hashes={n:digest((source/n).read_bytes()) for n in accepted['sha256']}
    check(hashes==accepted['sha256'],'exact externally accepted source and pin bytes')
    release_before=inventory(source)
    original_roots=[Path(p) for p in accepted['preserved_source_roots']]
    original_before={str(p):inventory(p) for p in original_roots}
    dump(out/'ORIGINAL_SOURCE_BEFORE.json',original_before); dump(out/'RELEASE_BEFORE.json',release_before)
    fixture=out/'release-fixture'; shutil.copytree(source,fixture,copy_function=shutil.copy2)
    check(inventory(fixture)==release_before,'exact fixture bytes/modes/nanosecond mtimes')
    results=[]
    def passed(name,**details):
        results.append({'name':name,'status':'PASS',**details}); dump(dossier/'INDEPENDENT_TEST_PROGRESS.json',results)
    passed('external-authentication-and-exact-fixture-copy',sha256=hashes)
    def command(name,tool,args,root=fixture,success=True,absent=None,contains=None,env=None):
        before=inventory(root)
        cmd=[sys.executable,'-I','-S','-B',str(root/'tools'/tool),*args]
        run=subprocess.run(cmd,cwd=out,env=env,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=360)
        (out/(name+'.stdout')).write_bytes(run.stdout)
        check((run.returncode==0)==success,name+' outcome: '+run.stdout.decode(errors='replace')[-3000:])
        if absent is not None: check(not os.path.lexists(absent),name+' must not create output')
        if contains is not None: check(contains.encode() in run.stdout,name+' expected refusal')
        check(inventory(root)==before,name+' source preservation')
        passed(name,exit_status=run.returncode,source_preserved=True)
        return run
    def clone(name):
        p=out/('mutant-'+name); shutil.copytree(fixture,p,copy_function=shutil.copy2); return p
    command('input-authentication','release64.py',['check-inputs'])
    pins=json.loads((fixture/'INPUT_PINS.json').read_bytes())
    actual_files={}; actual_dirs={}
    for scope in ('science','audits','dependencies'):
        for rel,row in inventory(fixture/scope).items():
            if rel=='.': continue
            item={'mode':row['mode'],'mtime_ns':row['mtime_ns']}
            if row['kind']==stat.S_IFREG:
                item.update(bytes=row['bytes'],sha256=row['sha256']); actual_files[scope+'/'+rel]=item
            elif row['kind']==stat.S_IFDIR: actual_dirs[scope+'/'+rel]=item
            else: raise AssertionError('nonregular frozen scope')
    check(pins['files']==actual_files and pins['directories']==actual_dirs,'independent input inventory')
    passed('independent-frozen-input-inventory',files=len(actual_files),directories=len(actual_dirs))
    module_pins=json.loads((fixture/'manuscript/MANUSCRIPT_PINS.json').read_bytes())
    check({n:digest((fixture/'manuscript'/n).read_bytes()) for n in module_pins}==module_pins,'independent module authentication')
    flat=(fixture/'manuscript/Report64.tex').read_bytes()
    for name in module_pins:
        if name=='Report64.tex': continue
        token=('\\input{'+name+'}\n').encode(); check(flat.count(token)==1,'single manuscript expansion '+name); flat=flat.replace(token,(fixture/'manuscript'/name).read_bytes())
    check(flat==(fixture/'Report64.tex').read_bytes(),'independent standalone flatten')
    passed('independent-manuscript-flatten',sha256=digest(flat),modules=len(module_pins))
    prep=out/'prepare-a'; command('prepare-a','release64.py',['prepare','--output-dir',str(prep)])
    command('prepare-b','release64.py',['prepare','--output-dir',str(out/'prepare-b')])
    check((prep/'Report64.tex').read_bytes()==flat and (prep/'MANUSCRIPT_PINS.json').read_bytes()==(fixture/'manuscript/MANUSCRIPT_PINS.json').read_bytes(),'prepare exact results')
    check(all((prep/n).read_bytes()==(out/'prepare-b'/n).read_bytes() for n in ('Report64.tex','MANUSCRIPT_PINS.json')),'repeat prepare equality')
    passed('prepare-repeat-byte-identity')
    msha=accepted['sha256']['manuscript/MANUSCRIPT_PINS.json']; lsha=accepted['sha256']['tools/BUILD_DEPENDENCIES_LOCK.json']
    common=['--pins-sha',msha,'--dependency-lock-sha',lsha,'--require-packaged-match']
    build=out/'actual-locked-build'; command('actual-locked-build','build_report64.py',[*common,'--output-dir',str(build)])
    receipt=json.loads((build/'BUILD_RECEIPT.json').read_bytes()); check(receipt['status']=='PASS' and receipt['dependency_lock_verified'] and receipt['packaged_pdf_match'],'locked build receipt')
    check((build/'Report64.pdf').read_bytes()==(fixture/'Report64.pdf').read_bytes(),'actual PDF equality')
    lock=json.loads((fixture/'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes()); union=json.loads((build/'RECORDER_INPUT_UNION.json').read_bytes())
    check(len(union['passes'])==4 and [p['pass'] for p in union['passes']]==['format','compile-1','compile-2','compile-3'],'all four passes')
    seen=set()
    for row in union['passes']:
        raw=(build/(row['pass']+'.fls')).read_bytes(); check(digest(raw)==row['fls_sha256'],'recorder hash')
        found=set()
        for line in raw.decode().splitlines():
            if line.startswith('INPUT /'):
                p=Path(line[6:]).resolve()
                if str(p).startswith(('/usr/share/texlive/','/usr/share/texmf/','/etc/texmf/','/var/lib/texmf/')): found.add(str(p))
        check(found==set(row['system_inputs']),'independent recorder system set '+row['pass']); seen.update(found)
    for name in ('lm.map','cm.map','cmextra.map','symbols.map','latxfont.map'):
        seen.add(str(Path((build/('map-'+name+'.stdout')).read_text().strip()).resolve()))
    check(seen==set(union['union'])==set(lock['system_inputs']),'independent all-pass plus selected map union')
    check((build/'BUILD_DEPENDENCIES.json').read_bytes()==(fixture/'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes(),'dependency exact bytes')
    for p,row in lock['system_inputs'].items():
        data=Path(p).read_bytes(); check(row=={'bytes':len(data),'sha256':digest(data)},'independent system dependency bytes')
    pages={p.name:independent_png(p.read_bytes()) for p in sorted((build/'pages').iterdir())}
    check(pages==json.loads((build/'PAGE_INVENTORY.json').read_bytes()) and len(pages)==receipt['page_count'],'independent rendered PNG inventory')
    passed('independent-actual-build-recorder-union-and-PNG-validation',page_count=len(pages),system_inputs=len(seen),pdf_sha256=digest((build/'Report64.pdf').read_bytes()))
    dump(dossier/'ACTUAL_RELEASE_BUILD_RECEIPT.json',receipt); dump(dossier/'INDEPENDENT_PAGE_INVENTORY.json',pages)
    # An independently authored synthetic manuscript forces a dependency used only
    # on the first document pass. No scientific executable is used.
    synthetic=clone('independent-first-pass')
    for name in module_pins:
        if name!='Report64.tex': (synthetic/'manuscript'/name).write_text('% Independent synthetic module: '+name+'\n')
    text='\\documentclass{article}\n\\IfFileExists{Report64.aux}{}{\\usepackage{xspace}}\n\\pdftrailerid{}\n\\begin{document}\nIndependent first-pass recorder test.\n'+''.join('\\input{'+n+'}\n' for n in module_pins if n!='Report64.tex')+'\\end{document}\n'
    (synthetic/'manuscript/Report64.tex').write_text(text)
    syntprep=out/'synthetic-prepared'; command('independent-first-pass-prepare','release64.py',['prepare','--output-dir',str(syntprep)],root=synthetic)
    shutil.copy2(syntprep/'Report64.tex',synthetic/'Report64.tex'); shutil.copy2(syntprep/'MANUSCRIPT_PINS.json',synthetic/'manuscript/MANUSCRIPT_PINS.json')
    syntpin=digest((syntprep/'MANUSCRIPT_PINS.json').read_bytes()); syntbuild=out/'synthetic-bootstrap'
    command('independent-first-pass-bootstrap','build_report64.py',['--pins-sha',syntpin,'--bootstrap','--output-dir',str(syntbuild)],root=synthetic)
    su=json.loads((syntbuild/'RECORDER_INPUT_UNION.json').read_bytes()); first=set(su['passes'][1]['system_inputs']); last=set(su['passes'][-1]['system_inputs'])
    early=[p for p in first-last if p.endswith('/xspace.sty')]; check(len(early)==1 and early[0] in su['union'],'independently forced early-only dependency')
    sl=json.loads((syntbuild/'BUILD_DEPENDENCIES.json').read_bytes()); del sl['system_inputs'][early[0]]
    raw=(json.dumps(sl,sort_keys=True,indent=2)+'\n').encode(); (synthetic/'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(raw)
    command('reject-independent-omitted-first-pass-dependency','build_report64.py',['--pins-sha',syntpin,'--dependency-lock-sha',digest(raw),'--output-dir',str(out/'synthetic-missing-early')],root=synthetic,success=False,contains='Unpinned or changed executed TeX input')
    failed=json.loads((out/'synthetic-missing-early/BUILD_FAILURE.json').read_bytes()); check(failed['release_preserved'],'early-only omission source preserved')
    passed('independent-first-pass-only-union-and-omission-check',path=early[0],bootstrap_status=json.loads((syntbuild/'BUILD_RECEIPT.json').read_bytes())['status'])
    # Freshness and canonical/alias boundary: every failure leaves the fixture intact.
    rejects=[('existing-output',str(prep),'Output must be fresh'),('relative-output','relative','Canonical absolute output'),('dot-output',str(out)+'/./dot-child','Canonical absolute output'),('dotdot-output',str(out)+'/../dotdot-child','Output path alias'),('double-slash-output','/'+str(out)+'/double-child','Canonical absolute output'),('trailing-slash-output',str(out/'trailing')+'/','Canonical absolute output'),('release-overlap',str(fixture/'inside'),'Output overlaps protected input')]
    for name,path,reason in rejects: command('reject-'+name,'release64.py',['prepare','--output-dir',path],success=False,contains=reason)
    (out/'output-ancestor-symlink').symlink_to(out,target_is_directory=True)
    command('reject-output-symlink-ancestor','release64.py',['prepare','--output-dir',str(out/'output-ancestor-symlink/child')],success=False,contains='Symlink path component')
    (out/'output-leaf-symlink').symlink_to(out/'nonexistent')
    command('reject-output-dangling-symlink','release64.py',['prepare','--output-dir',str(out/'output-leaf-symlink')],success=False,contains='Output must be fresh')
    for i,p in enumerate(original_roots): command('reject-original-source-overlap-'+str(i),'release64.py',['prepare','--output-dir',str(p/'independent-review-must-not-exist')],success=False,contains='Output overlaps protected input',absent=p/'independent-review-must-not-exist')
    (out/'source-alias').symlink_to(fixture,target_is_directory=True)
    command('reject-source-symlink-ancestor','release64.py',['check-inputs'],root=out/'source-alias',success=False,contains='Symlink path component')
    mutation_file=next(n for n in pins['files'] if n.startswith('science/frozen-proof/') and n.endswith('PROOF.md'))
    for name in ('bytes','mode','mtime','extra','empty','hardlink','symlink'):
        root=clone(name); p=root/mutation_file
        if name=='bytes': p.write_bytes(p.read_bytes()+b'\nchanged\n')
        if name=='mode': p.chmod(stat.S_IMODE(p.stat().st_mode)^0o100)
        if name=='mtime': os.utime(p,ns=(p.stat().st_mtime_ns+1,p.stat().st_mtime_ns+1))
        if name=='extra': (root/'science/frozen-proof/extra-file').write_bytes(b'extra')
        if name=='empty': (root/'science/frozen-proof/empty-directory').mkdir()
        if name=='hardlink': os.link(p,root/'hardlinked-proof')
        if name=='symlink': (root/'symbolic-proof').symlink_to(p)
        command('reject-input-'+name,'release64.py',['check-inputs'],root=root,success=False)
    root=clone('input-pin-bytes'); p=root/'INPUT_PINS.json'; p.write_bytes(p.read_bytes()+b' ')
    command('reject-input-pin-map-tamper','release64.py',['check-inputs'],root=root,success=False,contains='Frozen input-pin map differs')
    root=clone('helper-tamper'); p=root/'tools/release64.py'; p.write_bytes(p.read_bytes()+b'\n# changed\n')
    command('reject-helper-tamper','build_report64.py',[*common,'--output-dir',str(out/'helper-rejected')],root=root,success=False,contains='Release helper differs',absent=out/'helper-rejected')
    for name,args in [('manuscript',['--pins-sha','0'*64,'--bootstrap']),('dependency-lock',['--pins-sha',msha,'--dependency-lock-sha','0'*64])]:
        dest=out/(name+'-rejected'); command('reject-'+name+'-external-pin','build_report64.py',[*args,'--output-dir',str(dest)],success=False,absent=dest)
    for name,section in [('stale-system','system_inputs'),('stale-binary','executables')]:
        root=clone(name); altered=json.loads(json.dumps(lock)); key=sorted(altered[section])[0]; altered[section][key]['sha256']='0'*64
        raw=(json.dumps(altered,sort_keys=True,indent=2)+'\n').encode(); (root/'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(raw); dest=out/(name+'-rejected')
        command('reject-'+name+'-before-output','build_report64.py',['--pins-sha',msha,'--dependency-lock-sha',digest(raw),'--output-dir',str(dest)],root=root,success=False,absent=dest,contains='preflight mismatch')
    # Public PNG validator tested directly after authenticating exact source bytes.
    api=runpy.run_path(str(fixture/'tools/build_report64.py'),run_name='independent_png_test'); validate=api['validate_png']
    def require(ok,message): check(ok,message)
    def chunk(tag,payload): return struct.pack('>I',len(payload))+tag+payload+struct.pack('>I',zlib.crc32(tag+payload)&0xffffffff)
    def png(raw=b'\x00\x00\x00\x00',w=1,h=1,d=8,c=2,extra=b'',zextra=b''):
        return b'\x89PNG\r\n\x1a\n'+chunk(b'IHDR',struct.pack('>IIBBBBB',w,h,d,c,0,0,0))+extra+chunk(b'IDAT',zlib.compress(raw)+zextra)+chunk(b'IEND',b'')
    valid=png(); check(validate(valid,require)=={'width':1,'height':1},'valid PNG accepted'); passed('valid-synthetic-PNG')
    bads={'signature':b'bad'+valid[3:],'truncated':valid[:-1],'trailing':valid+b'x','crc':valid[:45]+bytes([valid[45]^1])+valid[46:],'zero-width':png(w=0),'width-limit':png(w=10001),'bit-depth':png(d=16),'color-type':png(c=6),'short-raster':png(raw=b'\x00\x00'),'long-raster':png(raw=b'\x00'*5),'row-filter':png(raw=b'\x05\x00\x00\x00'),'trailing-zlib-stream':png(zextra=zlib.compress(b'x')),'unknown-chunk':png(extra=chunk(b'tEXt',b'test')),'duplicate-IHDR':png(extra=chunk(b'IHDR',struct.pack('>IIBBBBB',1,1,8,2,0,0,0))),'invalid-density':png(extra=chunk(b'pHYs',struct.pack('>IIB',0,1,1)))}
    for name,data in bads.items():
        try: validate(data,require)
        except (AssertionError,ValueError,zlib.error): passed('reject-PNG-'+name)
        else: raise AssertionError('invalid PNG accepted: '+name)
    # Strict pin/JSON/manifest parsing and path validation use the reviewed helper.
    helper=runpy.run_path(str(fixture/'tools/release64.py'),run_name='independent_manifest_test')
    val=helper['validate_manifest']; base={'format':helper['FORMAT'],'files':{'ok':{'mode':0o644,'mtime_ns':1,'bytes':0,'sha256':digest(b'')}},'directories':{}}
    check(val(base)==base,'valid manifest'); passed('valid-minimal-manifest')
    manifest_cases=[]
    for name in ('../escape','/absolute','a//b','a/./b','a/../b','a\\b','line\nfeed'):
        m=json.loads(json.dumps(base)); m['files'][name]=m['files'].pop('ok'); manifest_cases.append(('path-'+repr(name),m))
    for label,field,value in [('unsafe-mode','mode',0o4777),('boolean-mode','mode',True),('negative-mtime','mtime_ns',-1),('negative-size','bytes',-1),('uppercase-sha','sha256','A'*64)]:
        m=json.loads(json.dumps(base)); m['files']['ok'][field]=value; manifest_cases.append((label,m))
    m=json.loads(json.dumps(base)); m['files']['RELEASE_MANIFEST.json']=m['files'].pop('ok'); manifest_cases.append(('self-reference',m))
    m=json.loads(json.dumps(base)); m['directories']['empty']={'mode':0o755,'mtime_ns':1}; manifest_cases.append(('empty-directory',m))
    m=json.loads(json.dumps(base)); m['files']['RELEASE_MANIFEST.json/child']=m['files'].pop('ok'); m['directories']['RELEASE_MANIFEST.json']={'mode':0o755,'mtime_ns':1}; manifest_cases.append(('manifest-directory-collision',m))
    for label,m in manifest_cases:
        try: val(m)
        except (ValueError,TypeError): passed('reject-manifest-'+label)
        else: raise AssertionError('invalid manifest accepted: '+label)
    try: helper['parse'](b'{"x":1,"x":2}')
    except ValueError: passed('reject-duplicate-JSON-keys')
    else: raise AssertionError('duplicate JSON keys accepted')
    # Manifest/ZIP contracts are exercised on a sealed expendable copy only.
    sealed=clone('sealed')
    if (sealed/'RELEASE_MANIFEST.json').exists(): (sealed/'RELEASE_MANIFEST.json').unlink()
    mf=out/'review-fixture-manifest.json'; command('manifest-generation','release64.py',['manifest','--output',str(mf)],root=sealed)
    shutil.copy2(mf,sealed/'RELEASE_MANIFEST.json'); manifest=json.loads(mf.read_bytes()); mfsha=digest(mf.read_bytes())
    command('manifest-verification','release64.py',['verify','--manifest-sha256',mfsha],root=sealed)
    for suffix in ('a','b'): command('deterministic-archive-'+suffix,'release64.py',['archive','--manifest-sha256',mfsha,'--output',str(out/('archive-'+suffix+'.zip'))],root=sealed)
    zipbytes=(out/'archive-a.zip').read_bytes(); check(zipbytes==(out/'archive-b.zip').read_bytes(),'deterministic archive exact bytes'); passed('archive-repeat-byte-identity',sha256=digest(zipbytes))
    extracted=out/'relocated-extracted'; command('metadata-preserving-extraction','release64.py',['extract','--manifest-sha256',mfsha,'--archive',str(out/'archive-a.zip'),'--output-dir',str(extracted)],root=sealed)
    observed=inventory(extracted)
    for section in ('files','directories'):
        for name,row in manifest[section].items():
            actual={k:observed[name][k] for k in row}; check(actual==row,'extraction exact metadata '+name)
    check((extracted/'RELEASE_MANIFEST.json').read_bytes()==mf.read_bytes(),'extracted manifest exact bytes')
    passed('independent-extracted-file-directory-modes-nanosecond-mtimes',files=len(manifest['files']),directories=len(manifest['directories']))
    command('relocated-manifest-verification','release64.py',['verify','--manifest-sha256',mfsha],root=extracted)
    command('relocated-exact-PDF-rebuild','build_report64.py',[*common,'--output-dir',str(out/'relocated-build')],root=extracted)
    check((out/'relocated-build/Report64.pdf').read_bytes()==(fixture/'Report64.pdf').read_bytes(),'relocated PDF independent byte check'); passed('relocated-PDF-byte-identity')
    for name,mutate in [('extra-entry',None),('duplicate-entry',None),('changed-bytes',None),('wrong-mode',None),('symlink-entry',None)]:
        badzip=out/(name+'.zip')
        with zipfile.ZipFile(out/'archive-a.zip') as z, zipfile.ZipFile(badzip,'w') as w:
            target='Report64/'+sorted(manifest['files'])[0]
            for info in z.infolist():
                data=z.read(info)
                if info.filename==target:
                    if name=='changed-bytes': data+=b'changed'
                    if name=='wrong-mode': info.external_attr=(stat.S_IFREG|0o777)<<16
                    if name=='symlink-entry': info.external_attr=(stat.S_IFLNK|0o777)<<16
                w.writestr(info,data)
            if name=='extra-entry': w.writestr('../escape.txt',b'escape')
            if name=='duplicate-entry': w.writestr(target,b'duplicate')
        dest=out/('reject-extract-'+name); command('reject-archive-'+name,'release64.py',['extract','--manifest-sha256',mfsha,'--archive',str(badzip),'--output-dir',str(dest)],root=sealed,success=False,absent=dest)
    command('reject-archive-manifest-pin','release64.py',['extract','--manifest-sha256','0'*64,'--archive',str(out/'archive-a.zip'),'--output-dir',str(out/'reject-pin-extract')],root=sealed,success=False,absent=out/'reject-pin-extract')
    # Run the inspected owned suite, retaining its distinct self-test identity.
    command('owned-selftest-suite','selftest64.py',['--output-dir',str(out/'owned-selftest')])
    owned=json.loads((out/'owned-selftest/SELFTEST_RECEIPT.json').read_bytes()); check(owned['status']=='PASS' and owned['frozen_inputs_preserved'],'owned selftest receipt')
    check(owned['tool_sources']=={Path(n).name:hashes[n] for n in hashes if n.startswith('tools/') and n.endswith('.py')},'owned suite exact helper bindings')
    dump(dossier/'OWNED_SELFTEST_RECEIPT.json',owned)
    original_after={str(p):inventory(p) for p in original_roots}; release_after=inventory(source)
    dump(out/'ORIGINAL_SOURCE_AFTER.json',original_after); dump(out/'RELEASE_AFTER.json',release_after)
    check(original_before==original_after,'original frozen sources preservation')
    # The release assembler may append unrelated QA while the independent review runs.
    # All originally observed files and all immutable scope metadata must remain identical.
    changed=[n for n,v in release_before.items() if n!='.' and n in release_after and v!=release_after[n]]
    missing=sorted(set(release_before)-set(release_after)); additions=sorted(set(release_after)-set(release_before))
    immutable_changes=[n for n in changed if n.startswith(('science/','audits/','dependencies/','tools/','manuscript/')) or n in hashes]
    check(not missing and not immutable_changes,'accepted release bytes and immutable scopes preservation')
    check({n:digest((source/n).read_bytes()) for n in hashes}==hashes,'final accepted byte binding')
    passed('independent-original-source-and-reviewed-byte-preservation',original_source_roots=len(original_roots),release_assembler_additions=additions,changed_nonimmutable_entries=changed)
    summary={'status':'PASS','scope':'Independent release-only authentication/typesetting/sealing/extraction review; no scientific program executed','tests':results,'test_count':len(results),'accepted_sha256':hashes,'owned_selftest_count':owned['test_count'],'fixture_manifest_sha256':mfsha,'fixture_archive_sha256':digest(zipbytes),'actual_pdf_sha256':receipt['pdf_sha256'],'page_count':receipt['page_count'],'sources_preserved':True,'release_snapshot_unchanged':release_before==release_after,'release_assembler_additions':additions,'changed_nonimmutable_entries':changed,'work_directory':str(out)}
    dump(dossier/'INDEPENDENT_TEST_RECEIPT.json',summary)
    dump(dossier/'PRESERVATION_SUMMARY.json',{'original_roots_unchanged':True,'accepted_bytes_unchanged':True,'release_snapshot_unchanged':release_before==release_after,'release_assembler_additions':additions,'changed_nonimmutable_entries':changed,'root_snapshot_sha256_before':digest((out/'ORIGINAL_SOURCE_BEFORE.json').read_bytes()),'root_snapshot_sha256_after':digest((out/'ORIGINAL_SOURCE_AFTER.json').read_bytes())})
    print(json.dumps({'status':'PASS','independent_tests':len(results),'owned_selftests':owned['test_count'],'pdf_sha256':receipt['pdf_sha256'],'page_count':receipt['page_count']},indent=2))

if __name__=='__main__': main()
