#!/usr/bin/env python3
"""Fake fourteen-child full-loop controls: never launches Lean or parent audits."""
import contextlib,hashlib,importlib.util,io,json,os,shutil,subprocess,sys,tempfile,types
from pathlib import Path
D=Path(__file__).resolve().with_name('replay-reviewed-e421.py')
WANT='169f39ddd34647819ff480fb61561007b59e81ff1ee7cc9a9ea853632092a4e0'
assert hashlib.sha256(D.read_bytes()).hexdigest()==WANT
PLAN=Path(__file__).resolve().parents[3]/'research/ordinary12-ipra-bridge/compact44-direct-symbolic-k-closure-plan/scan.json'
scan=json.loads(PLAN.read_bytes());HEAD='a'*40
modes=['frozen_parent_during_copy']
for mode in modes:
    spec=importlib.util.spec_from_file_location('driver',D);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    tmp=Path(tempfile.mkdtemp(prefix='ipra-sat-fake-fixture-',dir='/tmp'));out=Path(tempfile.mkdtemp(prefix='ipra-direct-symbolic-k-pair-fake-',dir='/tmp'));out.rmdir()
    m.PACKAGE=tmp/'package';m.PACKAGE.mkdir();(m.PACKAGE/'Init.olean').write_bytes(b'init')
    m.PREFIX=tmp/'provider';ext=['ArithmeticWindowDigits','ArithmeticStandardCasts','CompactGraphDerivedRadix']
    for side in ('author','peer'):
        d=m.PREFIX/side/'lib/DiophantineConsistency';d.mkdir(parents=True)
        for name in ext:(d/(name+'.olean')).write_bytes(name.encode())
    calls=[];audits=[];heads=[]
    def git_head():
        heads.append(1);return 'b'*40 if mode=='head_drift' and len(heads)>1 else HEAD
    m.git_head=git_head
    def verify():
        audits.append(1)
        if len(audits)>1 and mode=='late_source':
            p=out/'frozen/DiophantineConsistency/CompactDirectParamGraphDraft.lean';p.write_text(p.read_text()+'\n-- injected')
        if len(audits)>1 and mode=='late_companion':(out/'author/lib/DiophantineConsistency/CompactDirectParamGraphDraft.olean.private').write_bytes(b'injected')
        if len(audits)>1 and mode=='late_frozen_directory':
            directory=out/'frozen/DiophantineConsistency';back=directory.parent/'late-backing';directory.rename(back);directory.symlink_to(back,target_is_directory=True)
        if len(audits)>1 and mode=='late_output_directory':
            directory=out/'author/lib/DiophantineConsistency';back=directory.parent/'late-backing';directory.rename(back);directory.symlink_to(back,target_is_directory=True)
        if len(audits)>1 and mode=='late_object':(out/'author/lib/DiophantineConsistency/CompactDirectParamGraphDraft.olean').write_bytes(b'drift')
        if len(audits)>1 and mode=='late_log':(out/'author/DiophantineConsistency_CompactDirectParamGraphDraft.log').write_text('drift')
        return scan,{'status':'drift' if mode=='parent_drift' and len(audits)>1 else 'parent'}
    m.verify=verify
    def overlay(base,lib):
        d=lib/'DiophantineConsistency';d.mkdir(parents=True)
        for name in ext:(d/(name+'.olean')).symlink_to(base/'DiophantineConsistency'/(name+'.olean'))
        if mode=='preexisting_companion':(d/'Compact943Data.olean.private').write_bytes(b'injected')
    def monitored(cmd,env,log,timeout):
        obj=Path(cmd[-1]);src=Path(cmd[-3]);name='DiophantineConsistency.'+obj.stem
        if mode=='frozen_symlink':
            data=src.read_bytes();src.unlink();back=src.with_suffix('.backing');back.write_bytes(data);src.symlink_to(back)
        if mode=='frozen_directory_symlink':
            directory=src.parent;back=directory.parent/'backing';directory.rename(back);directory.symlink_to(back,target_is_directory=True)
        obj.write_bytes(b'peer' if mode=='sibling_mismatch' and 'peer' in str(obj) else name.encode())
        if mode=='output_directory_symlink':
            directory=obj.parent;back=directory.parent/'backing';directory.rename(back);directory.symlink_to(back,target_is_directory=True)
        if mode=='output_companion' or (mode=='output_companion_last' and obj.stem=='CompactDirectParamGraphDraft') or (mode=='output_companion_peer' and 'peer' in str(obj)):Path(str(obj)+'.private').write_bytes(b'injected')
        names=sorted(m.REPORTS[name]);
        if mode=='wrong_report':names[0]='Wrong.report'
        text=''.join("'"+n+("' depends on axioms: ["+', '.join(sorted(m.REPORTS[name].get(n,{'propext'})))+"]\n" if m.REPORTS[name].get(n,{'propext'}) else "' does not depend on any axioms\n") for n in names)
        if mode=='wrong_axiom':text=text.replace('propext','bad_axiom',1)
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
        if mode=='missing_built' and src.stem=='CompactSymbolicKernel':(lib/'DiophantineConsistency/CompactCoefficientMass.olean').unlink()
        if mode=='wrong_deps':paths.append('/tmp/wrong.olean')
        if mode=='duplicate_deps':paths.append(paths[1])
        if mode=='duplicate_init':paths.append(paths[0])
        return subprocess.CompletedProcess(cmd,0,stdout='\n'.join(paths)+'\n',stderr='')
    m.subprocess=types.SimpleNamespace(run=fake_run)
    def copy_and_redirect(src,dst):
        result=shutil.copyfile(src,dst)
        d=Path(dst).parent
        if Path(dst).suffix=='.lean' and not d.is_symlink():
            outside=tmp/'outside';d.rename(outside);d.symlink_to(outside,target_is_directory=True)
        return result
    m.shutil=types.SimpleNamespace(copyfile=copy_and_redirect,disk_usage=lambda _:types.SimpleNamespace(free=10*1024**3))
    sys.argv=[str(D),'--verify-only','--expected-head',HEAD] if mode=='verify_only' else [str(D),'--output',str(out),'--expected-head',HEAD]
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            try:m.main();err=None
            except Exception as e:err=str(e)
        if mode=='frozen_parent_during_copy':
            assert err and 'frozen source drift' in err and len(list((tmp/'outside').glob('*.lean')))==7 and not calls,(mode,err,calls)
        elif mode=='verify_only':
            assert err is None and not calls and not out.exists(),(mode,err)
        elif mode in ('good','duplicate_init'):
            assert err is None and len(calls)==14 and len(json.loads((out/'receipt.json').read_bytes())['runs'])==2,(mode,err)
        else:
            assert err is not None,(mode,err)
            expected={'wrong_report':'axiom reports','extra_report':'axiom reports','noaxiom_report':'axiom reports','wrong_axiom':'axiom reports','warning':'compiler failure','sorry':'compiler failure','compiler_exit':'compiler failure','boolean_exit':'compiler failure','stop_reason':'compiler failure','wrong_deps':'dependency mismatch','duplicate_deps':'dependency mismatch','missing_init':'companion drift','missing_external':'companion drift','missing_built':'companion drift','sibling_mismatch':'paired outputs differ','parent_drift':'final input or HEAD drift','frozen_symlink':'frozen source drift','frozen_directory_symlink':'frozen source drift','late_frozen_directory':'frozen source drift','output_directory_symlink':'invalid output directory','late_output_directory':'companion drift','late_source':'frozen source drift','late_object':'companion drift','late_log':'final output drift','head_drift':'HEAD drift','output_companion':'unexpected output companion','output_companion_last':'unexpected output companion','output_companion_peer':'unexpected output companion','late_companion':'unexpected companion','preexisting_companion':'unexpected output companion'}[mode]
            assert expected in err,(mode,expected,err)
        print(mode,'PASS',len(calls),'fake deps')
    finally:shutil.rmtree(out,ignore_errors=True);shutil.rmtree(tmp,ignore_errors=True)
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
