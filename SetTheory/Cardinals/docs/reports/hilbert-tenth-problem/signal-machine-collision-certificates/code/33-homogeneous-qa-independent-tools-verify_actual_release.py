#!/usr/bin/env python3
"""Source-bound actual Report63 locked builds and diagnostic release roundtrip."""
from pathlib import Path
import hashlib
import json
import os
import runpy
import shutil
import subprocess
import sys

A=Path(__file__).absolute().parent
R=A/'actual-release-fixture'
PIN='8dbeb0e7bdcbf949ebba9a699ab262dbb84b0111d9bb60d85c4c2a69aa10cbf1'
LOCK='c92b3fb240739cfbd8617e9e14407288c7e60c62fb41c433684c9e5f44541d74'
PDF='eb8d4d7c0cc0c98a7b706efe5e262d6b17699e21be7976957725f836420ad3ed'
def sha(b):return hashlib.sha256(b).hexdigest()
def enc(o):return (json.dumps(o,indent=2,sort_keys=True)+'\n').encode()
def check(v,m):
    if not v:raise AssertionError(m)

def main():
    check(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize,'isolated interpreter required')
    source=json.loads((A/'SOURCE_BINDINGS.json').read_bytes())
    for name in ('release63.py','build_report63.py','selftest63.py'):
        check(sha((R/'tools'/name).read_bytes())==source['tools/'+name],'tool source mismatch')
    h=runpy.run_path(str(R/'tools/release63.py'),run_name='actual_review_helpers')
    check(sha((R/'manuscript/MANUSCRIPT_PINS.json').read_bytes())==PIN,'manuscript pin')
    check(sha((R/'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes())==LOCK,'lock pin')
    check(sha((R/'Report63.pdf').read_bytes())==PDF,'packaged pdf pin')
    commands=[]
    def cmd(name,tool,args,root=R,env=None):
        before=h['snapshot'](root)
        argv=[sys.executable,'-I','-S','-B',str(root/'tools'/tool),*args]
        p=subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,stdin=subprocess.DEVNULL,timeout=600,env=env,cwd=A)
        (A/(name+'.stdout')).write_bytes(p.stdout)
        check(p.returncode==0,name+': '+p.stdout.decode(errors='replace')[-3000:])
        check(h['snapshot'](root)==before,'source changed during '+name)
        commands.append({'name':name,'argv':argv,'exit_status':p.returncode,'source_preserved':True})
        return json.loads(p.stdout)
    first=A/'actual-locked-build'
    hostile=os.environ.copy();hostile.update(TMPDIR=str(R/'science/frozen-proof'),TEMP=str(R/'audits/scientific'),TMP=str(R/'dependencies'))
    common=['--pins-sha',PIN,'--dependency-lock-sha',LOCK,'--require-packaged-match']
    receipt=cmd('ACTUAL_LOCKED_BUILD','build_report63.py',[*common,'--output-dir',str(first)],env=hostile)
    check(receipt['status']=='PASS' and receipt['pdf_sha256']==PDF and receipt['page_count']==18,'actual build receipt')
    check(not list(first.glob('report63-typeset-*')),'temporary directory cleanup')
    lock=json.loads((R/'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes())
    union=json.loads((first/'RECORDER_INPUT_UNION.json').read_bytes())
    check([x['pass'] for x in union['passes']]==['format','compile-1','compile-2','compile-3'],'all four recorder passes')
    independently_observed=set()
    for row in union['passes']:
        raw=(first/(row['pass']+'.fls')).read_bytes();check(sha(raw)==row['fls_sha256'],'recorder pin')
        observed=set()
        for line in raw.decode().splitlines():
            if line.startswith('INPUT '):
                p=Path(line[6:])
                if p.is_absolute() and str(p).startswith(('/usr/share/texlive/','/usr/share/texmf/','/etc/texmf/','/var/lib/texmf/')):
                    observed.add(str(p.resolve(strict=True)))
        check(observed==set(row['system_inputs']),'independent recorder extraction')
        independently_observed|=observed
    selected_maps={n for n in lock['system_inputs'] if Path(n).name in ('lm.map','cm.map','cmextra.map','symbols.map','latxfont.map')}
    check(independently_observed|selected_maps==set(lock['system_inputs']),'independent all-pass/map union')
    check(union['union']==lock['system_inputs'],'union equals preflight lock')
    check((first/'BUILD_DEPENDENCIES.json').read_bytes()==(R/'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes(),'byte-identical dependency receipt')
    inventory=json.loads((first/'PAGE_INVENTORY.json').read_bytes());check(len(inventory)==18,'PNG inventory count')
    for name,row in inventory.items():
        data=(first/'pages'/name).read_bytes();check(sha(data)==row['sha256'] and len(data)==row['bytes'],'PNG pin')
    manifest=A/'ACTUAL_TEST_MANIFEST.json'
    mr=cmd('ACTUAL_MANIFEST','release63.py',['manifest','--output',str(manifest)])
    manifest_pin=sha(manifest.read_bytes());check(mr['manifest_sha256']==manifest_pin,'manifest receipt pin')
    shutil.copy2(manifest,R/'RELEASE_MANIFEST.json')
    cmd('ACTUAL_VERIFY','release63.py',['verify','--manifest-sha256',manifest_pin])
    zip_receipts=[]
    for suffix in ('a','b'):
        zip_receipts.append(cmd('ACTUAL_ARCHIVE_'+suffix.upper(),'release63.py',['archive','--manifest-sha256',manifest_pin,'--output',str(A/('actual-release-'+suffix+'.zip'))]))
    check((A/'actual-release-a.zip').read_bytes()==(A/'actual-release-b.zip').read_bytes(),'deterministic archive equality')
    restored=A/'actual-relocated'
    extraction=cmd('ACTUAL_EXTRACT','release63.py',['extract','--archive',str(A/'actual-release-a.zip'),'--manifest-sha256',manifest_pin,'--output-dir',str(restored)])
    cmd('ACTUAL_RELOCATED_VERIFY','release63.py',['verify','--manifest-sha256',manifest_pin],root=restored)
    check(h['inventory'](R,exclude_manifest=True)==h['inventory'](restored,exclude_manifest=True),'all bytes modes nanoseconds restored')
    second=A/'actual-relocated-build'
    relocated=cmd('ACTUAL_RELOCATED_BUILD','build_report63.py',[*common,'--output-dir',str(second)],root=restored)
    check(relocated['pdf_sha256']==PDF and (second/'Report63.pdf').read_bytes()==(first/'Report63.pdf').read_bytes(),'relocated exact PDF')
    check((second/'PAGE_INVENTORY.json').read_bytes()==(first/'PAGE_INVENTORY.json').read_bytes(),'relocated exact PNG raster inventory')
    check((second/'BUILD_DEPENDENCIES.json').read_bytes()==(first/'BUILD_DEPENDENCIES.json').read_bytes(),'relocated dependency equality')
    report={'status':'PASS','source_bindings':source,'final_manuscript_pins_sha256':PIN,'pdf_sha256':PDF,'dependency_lock_sha256':LOCK,'page_count':18,'system_input_count':len(lock['system_inputs']),'executable_records':len(lock['executables']),'independent_all_pass_and_map_union':True,'hostile_all_temp_variables_safe':True,'temporary_workspace_removed':True,'deterministic_archives_identical':True,'diagnostic_archive_sha256':zip_receipts[0]['zip_sha256'],'diagnostic_manifest_sha256':manifest_pin,'diagnostic_manifest_file_count':mr['files'],'full_relocated_bytes_modes_mtimes_equal':True,'relocated_pdf_and_pngs_identical':True,'scientific_code_executed':False,'commands':commands,'scope':'Actual final manuscript on diagnostic release copies. This diagnostic archive is not the final published archive; final integration must seal again.'}
    (A/'ACTUAL_RELEASE_RECEIPT.json').write_bytes(enc(report));print(enc(report).decode())

if __name__=='__main__':main()
