#!/usr/bin/env python3
"""Fake six-child full-loop controls: never launches Lean or parent audits."""
import contextlib,hashlib,importlib.util,io,json,os,shutil,subprocess,sys,tempfile,types
from pathlib import Path
D=Path(__file__).resolve().with_name('replay.py')
WANT='b65108dad183079f7d51d8191d2742dd1376a33fd07d0d09717b6620ccd3c8cc'
assert hashlib.sha256(D.read_bytes()).hexdigest()==WANT
PLAN=Path.cwd()/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-rotation-windows-closure-plan/scan.json'
scan=json.loads(PLAN.read_bytes());HEAD='a'*40
modes=['verify_only','good','wrong_report','extra_report','noaxiom_report','wrong_axiom','warning','sorry','compiler_exit','stop_reason','wrong_deps','duplicate_deps','duplicate_init','missing_init','missing_external','missing_built','sibling_mismatch','parent_drift','frozen_symlink','frozen_directory_symlink','late_source','late_object','late_log','head_drift','output_companion','late_companion','preexisting_companion','output_companion_last','output_companion_peer','late_frozen_directory','output_directory_symlink','late_output_directory','boolean_exit','copy_directory_symlink','copy_directory_before','disk_below_initial','disk_below_mid','frozen_root_before_subdir','late_external_companion','late_source_same_symlink','output_symlink','late_output_symlink']
for mode in modes:
    spec=importlib.util.spec_from_file_location('driver',D);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    tmp=Path(tempfile.mkdtemp(prefix='ipra-sat-fake-fixture-',dir='/tmp'));out=Path(tempfile.mkdtemp(prefix='ipra-rotation-windows-pair-fake-',dir='/tmp'));out.rmdir()
    m.PACKAGE=tmp/'package';m.PACKAGE.mkdir();(m.PACKAGE/'Init.olean').write_bytes(b'init')
    m.PREFIX=tmp/'provider';ext=['ArithmeticWindowDigits','ArithmeticCyclicWord']
    for side in ('author','peer'):
        d=m.PREFIX/side/'lib/DiophantineConsistency';d.mkdir(parents=True)
        for name in ext:(d/(name+'.olean')).write_bytes(name.encode())
    calls=[];audits=[];heads=[]
    def git_head():
        heads.append(1);return 'b'*40 if mode=='head_drift' and len(heads)>1 else HEAD
    m.git_head=git_head
    m.validate_provider=lambda:None  # Fake fixtures deliberately use a temporary provider.
    def verify():
        audits.append(1)
        if len(audits)>1 and mode=='late_source':
            p=out/'frozen/DiophantineConsistency/RotationBoundedCases.lean';p.write_text(p.read_text()+'\n-- injected')
        if len(audits)>1 and mode=='late_companion':(out/'author/lib/DiophantineConsistency/RotationBoundedCases.olean.private').write_bytes(b'injected')
        if len(audits)>1 and mode=='late_frozen_directory':
            directory=out/'frozen/DiophantineConsistency';back=directory.parent/'late-backing';directory.rename(back);directory.symlink_to(back,target_is_directory=True)
        if len(audits)>1 and mode=='late_output_directory':
            directory=out/'author/lib/DiophantineConsistency';back=directory.parent/'late-backing';directory.rename(back);directory.symlink_to(back,target_is_directory=True)
        if len(audits)>1 and mode=='late_object':(out/'author/lib/DiophantineConsistency/RotationBoundedCases.olean').write_bytes(b'drift')
        if len(audits)>1 and mode=='late_log':(out/'author/DiophantineConsistency_RotationBoundedCases.log').write_text('drift')
        if len(audits)>1 and mode=='late_external_companion':Path(str(out/'author/lib/DiophantineConsistency/ArithmeticWindowDigits.olean')+'.private').write_bytes(b'injected')
        if len(audits)>1 and mode=='late_source_same_symlink':
            p=out/'frozen/DiophantineConsistency/RotationBoundedCases.lean';data=p.read_bytes();p.unlink();b=p.with_suffix('.backing');b.write_bytes(data);p.symlink_to(b)
        if len(audits)>1 and mode=='late_output_symlink':
            p=out/'author/lib/DiophantineConsistency/RotationBoundedCases.olean';data=p.read_bytes();p.unlink();b=p.with_suffix('.backing');b.write_bytes(data);p.symlink_to(b)
        return scan,{'status':'drift' if mode=='parent_drift' and len(audits)>1 else 'parent'}
    m.verify=verify
    def overlay(base,lib):
        d=lib/'DiophantineConsistency';d.mkdir(parents=True)
        for name in ext:(d/(name+'.olean')).symlink_to(base/'DiophantineConsistency'/(name+'.olean'))
        if mode=='preexisting_companion':(d/'FractionalDigits.olean.private').write_bytes(b'injected')
    def monitored(cmd,env,log,timeout):
        obj=Path(cmd[-1]);src=Path(cmd[-3]);name='DiophantineConsistency.'+obj.stem
        if mode=='frozen_symlink':
            data=src.read_bytes();src.unlink();back=src.with_suffix('.backing');back.write_bytes(data);src.symlink_to(back)
        if mode=='frozen_directory_symlink':
            directory=src.parent;back=directory.parent/'backing';directory.rename(back);directory.symlink_to(back,target_is_directory=True)
        obj.write_bytes(b'peer' if mode=='sibling_mismatch' and 'peer' in str(obj) else name.encode())
        if mode=='output_symlink':
            data=obj.read_bytes();obj.unlink();b=obj.with_suffix('.backing');b.write_bytes(data);obj.symlink_to(b)
        if mode=='output_directory_symlink':
            directory=obj.parent;back=directory.parent/'backing';directory.rename(back);directory.symlink_to(back,target_is_directory=True)
        if mode=='output_companion' or (mode=='output_companion_last' and obj.stem=='RotationBoundedCases') or (mode=='output_companion_peer' and 'peer' in str(obj)):Path(str(obj)+'.private').write_bytes(b'injected')
        names=sorted(next(x['axiom_reports'] for x in scan['source_order'] if x['module']==name));
        if mode=='wrong_report':names[0]='Wrong.report'
        ax='propext' if mode=='wrong_axiom' else 'propext, Classical.choice, Quot.sound'
        text=''.join("'"+n+"' depends on axioms: ["+ax+"]\n" for n in names)
        if mode=='extra_report':text+="'Extra.report' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        if mode=='noaxiom_report':text+="'Extra.report' does not depend on any axioms\n"
        if mode=='warning':text+='warning: injected\n'
        if mode=='sorry':text+='sorryAx\n'
        log.write_text(text)
        return (True if mode=='boolean_exit' else 1 if mode=='compiler_exit' else 0),100,('stop' if mode=='stop_reason' else None)
    m.load_monitor=lambda:types.SimpleNamespace(overlay=overlay,monitored=monitored)
    real_run=subprocess.run
    def fake_run(cmd,env=None,**kw):
        assert '--deps' in cmd
        src=Path(cmd[-1]);lib=Path(env['LEAN_PATH'].split(':')[0]);calls.append(src.stem)
        row=next(x for x in scan['source_order'] if x['module'].endswith('.'+src.stem))
        paths=[str(m.PACKAGE/'Init.olean')]+[str((lib/Path(*dep.split('.'))).with_suffix('.olean')) for dep in row['imports']]
        if mode=='missing_init':(m.PACKAGE/'Init.olean').unlink()
        if mode=='missing_external':(lib/'DiophantineConsistency/ArithmeticWindowDigits.olean').unlink()
        if mode=='missing_built' and src.stem=='AdjacentDigits':(lib/'DiophantineConsistency/FractionalDigits.olean').unlink()
        if mode=='wrong_deps':paths.append('/tmp/wrong.olean')
        if mode=='duplicate_deps':paths.append(paths[1])
        if mode=='duplicate_init':paths.append(paths[0])
        return subprocess.CompletedProcess(cmd,0,stdout='\n'.join(paths)+'\n',stderr='')
    copied=[]
    def copying(src,dst):
        result=shutil.copyfile(src,dst);copied.append(str(dst))
        if mode=='copy_directory_symlink' and len(copied)==1:
            directory=Path(dst).parent;outside=tmp/'outside';directory.rename(outside);directory.symlink_to(outside,target_is_directory=True)
        return result
    space_calls=[]
    def space(_):
        space_calls.append(1)
        return types.SimpleNamespace(free=0 if mode=='disk_below_initial' or mode=='disk_below_mid' and len(space_calls)>3 else 10*1024**3)
    m.subprocess=types.SimpleNamespace(run=fake_run);m.shutil=types.SimpleNamespace(copyfile=copying,disk_usage=space)
    sys.argv=[str(D),'--verify-only','--expected-head',HEAD] if mode=='verify_only' else [str(D),'--output',str(out),'--expected-head',HEAD]
    real_mkdir=Path.mkdir
    def injected_mkdir(p,*a,**kw):
        result=real_mkdir(p,*a,**kw)
        if mode=='frozen_root_before_subdir' and p==out/'frozen' and not p.is_symlink():
            outside=tmp/'outside';p.rename(outside);p.symlink_to(outside,target_is_directory=True)
        if mode=='copy_directory_before' and p==out/'frozen/DiophantineConsistency' and not p.is_symlink():
            outside=tmp/'outside';p.rename(outside);p.symlink_to(outside,target_is_directory=True)
        return result
    Path.mkdir=injected_mkdir
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            try:m.main();err=None
            except Exception as e:err=str(e)
        if mode=='verify_only':
            assert err is None and not calls and not out.exists(),(mode,err)
        elif mode in ('good','duplicate_init'):
            assert err is None and len(calls)==28 and len(json.loads((out/'receipt.json').read_bytes())['runs'])==2,(mode,err)
        else:
            assert err is not None,(mode,err)
            expected={'wrong_report':'axiom reports','extra_report':'axiom reports','noaxiom_report':'axiom reports','wrong_axiom':'axiom reports','warning':'compiler failure','sorry':'compiler failure','compiler_exit':'compiler failure','boolean_exit':'compiler failure','stop_reason':'compiler failure','wrong_deps':'dependency mismatch','duplicate_deps':'dependency mismatch','missing_init':'companion drift','missing_external':'companion drift','missing_built':'companion drift','sibling_mismatch':'paired outputs differ','parent_drift':'final input or HEAD drift','frozen_symlink':'invalid frozen destination','frozen_directory_symlink':'invalid frozen source directory','late_frozen_directory':'invalid frozen source directory','output_directory_symlink':'invalid output directory','late_output_directory':'companion drift','late_source':'frozen source drift','late_object':'companion drift','late_log':'final output drift','head_drift':'HEAD drift','output_companion':'unexpected output companion','output_companion_last':'unexpected output companion','output_companion_peer':'unexpected output companion','late_companion':'unexpected companion','preexisting_companion':'unexpected output companion','copy_directory_symlink':'invalid frozen source directory','copy_directory_before':'invalid frozen source directory','disk_below_initial':'sampled free space below reserve','disk_below_mid':'sampled free space below reserve','frozen_root_before_subdir':'invalid frozen root','late_external_companion':'unexpected companion','late_source_same_symlink':'invalid frozen destination','output_symlink':'invalid emitted object','late_output_symlink':'companion drift'}[mode]
            assert expected in err,(mode,expected,err)
            if mode=='frozen_root_before_subdir':assert not (tmp/'outside/DiophantineConsistency').exists() and not calls,(mode,calls)
            if mode=='copy_directory_before':assert not list((tmp/'outside').glob('*.lean')) and not calls,(mode,calls)
            if mode=='copy_directory_symlink':assert len(copied)==1 and len(list((tmp/'outside').glob('*.lean')))==1 and not calls,(mode,copied,calls)
        print(mode,'PASS',len(calls),'fake deps')
    finally:Path.mkdir=real_mkdir;shutil.rmtree(out,ignore_errors=True);shutil.rmtree(tmp,ignore_errors=True)
# Explicitly exercise every non-object companion slot, both before and after a child.
for suffix in (s for s in m.SUFFIXES if s != '.olean'):
    with tempfile.TemporaryDirectory(prefix='ipra-sat-output-slot-',dir='/tmp') as td:
        stem=Path(td)/'Object';obj=Path(str(stem)+'.olean');comp=Path(str(stem)+suffix);comp.write_bytes(b'injected')
        for before in (True,False):
            if not before:obj.write_bytes(b'object')
            try:m.output_guards(obj,before)
            except ValueError as e:assert 'unexpected output companion' in str(e),(suffix,before,str(e))
            else:raise AssertionError(('accepted companion',suffix,before))
print('all_nine_output_companion_slots_before_and_after PASS')

# Real provider and fresh-output families are distinct; do not mask this in the full-loop fixtures.
spec=importlib.util.spec_from_file_location('real_provider_check',D);v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
assert v.PREFIX==Path('/tmp/ipra-indexed-graph-carry-pair-01')
v.validate_provider()
v.PREFIX=Path('/tmp/ipra-rotation-windows-pair-01')
try:v.validate_provider()
except ValueError as e:assert 'unexpected provider path' in str(e)
else:raise AssertionError('wrong output-family provider accepted')
v.PREFIX=Path('/tmp/ipra-indexed-graph-carry-pair-01')
v.git_head=lambda:HEAD
sys.argv=[str(D),'--output',str(v.PREFIX),'--expected-head',HEAD]
try:v.main()
except ValueError as e:assert 'fresh direct /tmp output required' in str(e)
else:raise AssertionError('parent provider accepted as fresh output')
print('real_provider_wrong_output_family_and_parent_as_output PASS')
