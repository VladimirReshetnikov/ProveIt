#!/usr/bin/env python3
"""Release-only relocation and guard tests; scientific executables stay inert."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys

sys.dont_write_bytecode=True
LAYOUT={'physical_science':'science/physical','geometry_science':'science/geometry',
        'arithmetic_science':'science/arithmetic','quadratic_science':'science/quadratic',
        'physical_audit':'audits/physical',
        'geometry_audit':'audits/geometry','arithmetic_audit':'audits/arithmetic',
        'quadratic_audit':'audits/quadratic',
        'dependencies':'dependencies'}


def demand(value,message):
    if not value:raise RuntimeError(message)


def load_adapter(path):
    ns={'__name__':'__selftest_adapter__','__file__':str(path),'__package__':None}
    exec(compile(path.read_bytes(),str(path),'exec',dont_inherit=True,optimize=0),ns)
    return ns


def command(release,output,optimized=False):
    args=[sys.executable,'-B']+(['-O'] if optimized else [])
    args += [str(release/'tools/portable-replay/replay.py'),'--release-root',str(release)]
    for role,where in LAYOUT.items():
        args += ['--'+role.replace('_','-')+'-root',str(release/where)]
    return args+['--output',str(output)]


def writable_copy(root):
    root.chmod(0o755)
    for p in sorted(root.rglob('*'),key=lambda p:len(p.parts)):
        p.chmod(0o755 if p.is_dir() else 0o644)


def readonly(root):
    for p in sorted(root.rglob('*'),key=lambda p:len(p.parts),reverse=True):
        p.chmod(0o555 if p.is_dir() else 0o444)
    root.chmod(0o555)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--release-root',required=True)
    parser.add_argument('--output',required=True)
    args=parser.parse_args()
    adapter=Path(__file__).resolve().with_name('replay.py')
    ns=load_adapter(adapter)
    release=ns['canonical_path'](args.release_root,existing=True)
    output=ns['canonical_path'](args.output,existing=False)
    demand(not output.exists() and output.parent.is_dir(),'Selftest output must be fresh with an existing parent')
    demand(not ns['inside'](output,release) and not ns['inside'](release,output),'Selftest output must be external')
    demand(not ns['inside'](output,adapter.parent),'Selftest output must be external to adapter')
    before=ns['inventory'](release)
    demand(ns['content_inventory'](ns['inventory'](release/'tools/portable-replay')) ==
           ns['content_inventory'](ns['inventory'](adapter.parent)),
           'Release tool subtree differs from this inspected selftest and adapter')
    # Validate the canonical release roles before making any disposable copies.
    pins=json.loads((adapter.parent/'INPUT_PINS.json').read_text())
    demand(hashlib.sha256((adapter.parent/'INPUT_PINS.json').read_bytes()).hexdigest()==ns['PINS_SHA256'],'Input pins mismatch')
    for role,where in LAYOUT.items():ns['authenticate'](release/where,pins['trees'][role])
    output.mkdir()
    (output/'logs').mkdir()
    tests=[]
    def run(name,argv,success,diagnostic=None):
        done=subprocess.run(argv,cwd=output,capture_output=True,text=True,
                            env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
        (output/'logs'/f'{name}.stdout').write_text(done.stdout)
        (output/'logs'/f'{name}.stderr').write_text(done.stderr)
        ok=(done.returncode==0)==success
        if diagnostic is not None:ok=ok and diagnostic in done.stderr
        tests.append({'name':name,'command':argv,'exit_code':done.returncode,'expected_success':success,
                      'required_diagnostic':diagnostic,'passed':ok})
        demand(ok,'Regression failed: '+name+'\n'+done.stderr)
    writable=output/'writable-release'; shutil.copytree(release,writable,copy_function=shutil.copy2); writable_copy(writable)
    normal=output/'run-normal'
    run('normal_replay',command(writable,normal),True)
    relocated=output/'read-only-relocated'/'unrelated-name'
    relocated.parent.mkdir(); shutil.copytree(release,relocated,copy_function=shutil.copy2); readonly(relocated)
    run('read_only_relocated_optimized_replay',command(relocated,output/'run-readonly-optimized',True),True)
    # Early rejects use the authenticated disposable writable release.
    run('reuse_output',command(writable,normal),False,'Output must be fresh')
    run('output_inside_release',command(writable,writable/'forbidden-output'),False,'Output must be external')
    bad=command(writable,output/'relative-output'); bad[bad.index('--physical-science-root')+1]='relative/science'
    run('relative_input_root',bad,False,'explicit and absolute')
    bad=command(writable,output/'alias-output'); bad[bad.index('--physical-science-root')+1]=str(writable/'science')+'/./physical'
    run('noncanonical_input_alias',bad,False,'canonical')
    bad=command(writable,output/'overlap-output'); bad[bad.index('--geometry-science-root')+1]=str(writable/'science/physical')
    run('overlapping_input_roots',bad,False,'Input roots must be disjoint')
    bad=command(writable,output/'missing-flag-output'); i=bad.index('--arithmetic-audit-root'); del bad[i:i+2]
    run('missing_required_root',bad,False,'required')
    link=output/'output-alias'; link.symlink_to(output/'nonexistent-output')
    run('symlink_output',command(writable,link),False,'canonical')
    root_link=output/'root-alias'; root_link.symlink_to(writable/'science/physical',target_is_directory=True)
    bad=command(writable,output/'root-alias-output'); bad[bad.index('--physical-science-root')+1]=str(root_link)
    run('symlink_input_root',bad,False,'canonical')
    adapter_link=output/'adapter-alias'; adapter_link.symlink_to(writable/'tools/portable-replay',target_is_directory=True)
    bad=command(writable,output/'adapter-alias-output'); bad[2]=str(adapter_link/'replay.py')
    run('symlink_adapter_ancestor',bad,False,'Adapter source must be canonical')
    bad=command(writable,output/'outside-role-output'); bad[bad.index('--physical-science-root')+1]=str(release/'science/physical')
    run('role_outside_release',bad,False,'strict descendant')
    # Source-corruption/link tests alter only separate disposable copies.
    negatives=output/'negative-copies'; negatives.mkdir()
    cases=[('missing_source','science/physical/PROOF.md','missing'),
           ('tampered_source','science/arithmetic/PROOF.md','append'),
           ('tampered_inert_quadratic_science','science/quadratic/PROOF.md','append'),
           ('tampered_inert_quadratic_audit','audits/quadratic/REVIEW.md','append'),
           ('tampered_checker','audits/geometry/independent_exact_checks.py','append'),
           ('tampered_expected','audits/arithmetic/EXACT_RECEIPT.json','append'),
           ('extra_source_file','science/geometry/UNEXPECTED','extra'),
           ('symlink_source_file','science/physical/PROOF.md','symlink'),
           ('hardlinked_source_file','science/physical/PROOF.md','hardlink'),
           ('tampered_pins','tools/portable-replay/INPUT_PINS.json','append')]
    for name,relative,mutation in cases:
        root=negatives/name; shutil.copytree(release,root,copy_function=shutil.copy2); writable_copy(root)
        p=root/relative
        if mutation=='missing':p.unlink()
        elif mutation in ('append','extra'):
            with p.open('a') as f:f.write('\nUNAUTHENTICATED\n')
        elif mutation=='symlink':
            p.unlink();p.symlink_to(root/'science/geometry/PROOF.md')
        elif mutation=='hardlink':os.link(p,output/(name+'-alias'))
        diagnostic={'missing':'Authenticated tree mismatch','append':'Authenticated tree mismatch',
                    'extra':'Authenticated tree mismatch','symlink':'Symlink entry','hardlink':'Hardlinked file'}[mutation]
        if name=='tampered_pins':diagnostic='input-pins digest mismatch'
        run(name,command(root,output/(name+'-output')),False,diagnostic)
    # Demonstrate the actual audit hook, not merely its predicate. Forbidden
    # reads target the untouched original release, which remains present.
    probe=output/'probe.py'
    probe.write_text('''from pathlib import Path\nimport sys\np=Path(sys.argv[1]);ns={"__name__":"probe","__file__":str(p)}\nexec(compile(p.read_bytes(),str(p),"exec",optimize=0),ns)\nroot=Path(sys.argv[2]);out=Path(sys.argv[3]);target=Path(sys.argv[4]);mode=sys.argv[5]\ng=ns["ReadWriteGuard"]([root,out],[root],out);sys.addaudithook(g)\ntry:\n if mode=="read":target.read_bytes()\n else:target.write_text("forbidden")\nexcept PermissionError:\n print("PASS: forbidden "+mode+" blocked")\nelse:\n raise RuntimeError("I/O guard did not reject forbidden access")\n''')
    probe_root=output/'probe-input';probe_root.mkdir();sentinel=probe_root/'sentinel';sentinel.write_text('unchanged')
    probe_out=output/'probe-output';probe_out.mkdir()
    run('historical_read_fallback_blocked',[sys.executable,'-B',str(probe),str(adapter),str(probe_root),str(probe_out),
                                           str(release/'science/physical/PROOF.md'),'read'],True)
    run('protected_write_blocked',[sys.executable,'-B',str(probe),str(adapter),str(probe_root),str(probe_out),str(sentinel),'write'],True)
    demand(sentinel.read_text()=='unchanged','Protected write changed sentinel')
    # Direct comparator regression, with only disposable plain data.
    wrong=output/'different-bytes';wrong.write_bytes(b'different\n')
    try:ns['compare_file'](wrong,sentinel,[])
    except RuntimeError:tests.append({'name':'byte_comparator_rejects_difference','passed':True})
    else:raise RuntimeError('Byte comparator accepted nonidentical data')
    after=ns['inventory'](release)
    demand(after==before,'Original release changed during selftest')
    report={'status':'PASS','release_root':str(release),'original_release_unchanged':True,
            'normal_receipt_sha256':hashlib.sha256((normal/'REPLAY_RECEIPT.json').read_bytes()).hexdigest(),
            'readonly_optimized_receipt_sha256':hashlib.sha256((output/'run-readonly-optimized/REPLAY_RECEIPT.json').read_bytes()).hexdigest(),
            'test_count':len(tests),'tests':tests}
    (output/'ORIGINAL_RELEASE_BEFORE.json').write_text(json.dumps(before,indent=2)+'\n')
    (output/'ORIGINAL_RELEASE_AFTER.json').write_text(json.dumps(after,indent=2)+'\n')
    (output/'VALIDATION_REPORT.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','tests':len(tests),'output':str(output)},indent=2))


if __name__=='__main__':
    try:main()
    except Exception as error:
        print(type(error).__name__+': '+str(error),file=sys.stderr)
        raise SystemExit(1)
