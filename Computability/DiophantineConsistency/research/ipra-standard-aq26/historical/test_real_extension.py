#!/usr/bin/env python3
"""Small real-Lean paired extension and adversarial controls; not an AQ29 run."""
if not __debug__:
    raise RuntimeError('controls require Python assertions enabled')

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE=Path(__file__).resolve().parent
PARENT_TOOLS=HERE.parents[1]/'fresh-project-closure'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL=LEAN.parent.parent/'lib/lean'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def run(*args,cwd=None,ok=True):
    q=subprocess.run(list(map(str,args)),cwd=cwd,capture_output=True,text=True)
    if ok and q.returncode:raise RuntimeError((args,q.returncode,q.stdout,q.stderr))
    return q

with tempfile.TemporaryDirectory(prefix='reference-extension-control-') as td:
    root=Path(td);workspace=root/'workspace';workspace.mkdir()
    run('git','init','-q',cwd=workspace)
    (workspace/'lakefile.toml').write_text('name = "Toy"\n')
    (workspace/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
    policy=workspace/'Computability/DiophantineConsistency/research/ipra-standard-aq26/historical/task-policy.json'
    policy.parent.mkdir(parents=True);policy.write_text(json.dumps({'target':'Toy.ReferenceChecks',
        'expected_axiom_names':['extResult','toyBase'], 'addition_order':['Toy.Extra','Toy.Silent','Toy.ReferenceChecks'], 'sources':{}, 'expected_axiom_by_module':{'Toy.Extra':['extResult'],'Toy.Silent':[],'Toy.ReferenceChecks':['extResult','toyBase']}}))
    texts={'Toy.A':'def value : Nat := 1\n',
           'Toy.BaseChecks':'import Toy.A\ntheorem toyBase : value = 1 := rfl\n#print axioms toyBase\n'}
    deps={'Toy.A':[],'Toy.BaseChecks':['Toy.A']}
    def write_sources():
        for name,text in texts.items():
            path=workspace/'src'/(name.replace('.','/')+'.lean');path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
    def commit():
        run('git','add','.',cwd=workspace)
        run('git','-c','user.name=Toy','-c','user.email=toy@example.invalid','commit','-q','-m','toy',cwd=workspace)
    def snapshot(path,target,names=None):
        rows={}
        for name,text in texts.items():
            q=path/'src'/(name.replace('.','/')+'.lean');q.parent.mkdir(parents=True,exist_ok=True);q.write_text(text)
            rows[name]={'workspace_path':str(q.relative_to(path)),'snapshot_path':str(q.relative_to(path)),
                        'sha256':H(q),'imports':deps[name]}
        manifest={'status':'FROZEN_NOT_COMPILED','root':str(workspace),'target':target,'order':list(texts),
                  'project_modules':len(texts),'sources':rows,'lakefile_sha256':H(workspace/'lakefile.toml'),
                  'lean_toolchain_sha256':H(workspace/'lean-toolchain'),
                  'head':run('git','rev-parse','HEAD',cwd=workspace).stdout.strip()}
        if names is not None:
            manifest['expected_axiom_names']=names;manifest['target_policy_sha256']=H(policy)
        (path/'manifest.json').write_text(json.dumps(manifest))
    write_sources();commit();old=root/'old';snapshot(old,'Toy.BaseChecks')
    provider=root/'provider';foundation=provider/'.lake/build/lib/lean/Foundation';foundation.mkdir(parents=True)
    pkg=provider/'package-lib';pkg.mkdir();(pkg/'Foundation').symlink_to(foundation)
    for name in ('Init','Init.olean','Init.ir','Init.olean.private','Init.olean.server'):
        source=TOOL/name
        if source.exists():(pkg/name).symlink_to(source,target_is_directory=source.is_dir())
    finput=provider/'input.json';finput.write_text(json.dumps({'lean_sha256':H(LEAN)}))
    receipt=provider/'receipt.json';receipt.write_text(json.dumps({'manifest_sha256':H(finput),
        'status':'BUILT','exit_code':0,'declared_external_guard':{},'overlay':str(pkg),
        'root':str(provider),'foundation_artifacts':{}}))
    parent=root/'parent'
    q=run(sys.executable,PARENT_TOOLS/'run_pair.py','--snapshot',old,'--snapshot-sha256',H(old/'manifest.json'),
          '--provider-receipt',receipt,'--provider-sha256',H(receipt),'--foundation-input',finput,
          '--expected-axiom-reports','1','--output',parent)
    pair=parent/'pair-state.json';observation=root/'observation.json'
    observation.write_text(json.dumps({'observed_exit_code':q.returncode,'observed_stdout':q.stdout,
        'pair_state_sha256':H(pair),'pair_state_path':str(pair)}))
    texts['Toy.Extra']='import Toy.A\ntheorem extResult : value = 1 := rfl\n#print axioms extResult\n'
    texts['Toy.Silent']='import Toy.A\ndef silent := value\n'
    texts['Toy.ReferenceChecks']='import Toy.BaseChecks\nimport Toy.Extra\n#print axioms extResult\n#print axioms toyBase\n'
    deps['Toy.Extra']=['Toy.A'];deps['Toy.Silent']=['Toy.A'];deps['Toy.ReferenceChecks']=['Toy.BaseChecks','Toy.Extra']
    write_sources();(workspace/'src/Toy/A.lean').write_text(texts['Toy.A']+'-- committed parent drift\n')
    commit();new=root/'new';snapshot(new,'Toy.ReferenceChecks',['extResult','toyBase'])
    old_manifest=json.loads((old/'manifest.json').read_text())
    manifest=json.loads((new/'manifest.json').read_text())
    task=json.loads(policy.read_text()); task['sources']={n:{k:manifest['sources'][n][k] for k in ('workspace_path','sha256','imports')} for n in task['addition_order']}
    policy.write_text(json.dumps(task))
    # Copy production tools and substitute only the fixture trust anchor.
    original_here=HERE; toy_here=policy.parent
    for name in ('prepare.py','freeze.py','rebuild.py','compare.py','run_pair.py'):
        shutil.copyfile(original_here/name,toy_here/name)
    shutil.copyfile(original_here.parent/'paired_plan.py',toy_here.parent/'paired_plan.py')
    toy_parent=toy_here.parents[1]/'fresh-project-closure';toy_parent.mkdir(parents=True)
    for name in ('rebuild.py','compare.py','run_pair.py'):
        shutil.copyfile(PARENT_TOOLS/name,toy_parent/name)
    preparer=toy_here/'prepare.py'; source=preparer.read_text()
    anchor="POLICY_SHA256 = '500a50fdaf136f32ddd945309d0793725e0de1a006bccbc81342d92d0826976b'"
    assert source.count(anchor)==1
    preparer.write_text(source.replace(anchor,"POLICY_SHA256 = '"+H(policy)+"'"))
    HERE=toy_here
    run('git','add','.',cwd=workspace);run('git','-c','user.name=Toy','-c','user.email=toy@example.invalid','commit','-qm','pin policy',cwd=workspace)
    manifest['head']=run('git','rev-parse','HEAD',cwd=workspace).stdout.strip();manifest['target_policy_sha256']=H(policy)
    manifest['expected_axiom_by_module']=task['expected_axiom_by_module']
    manifest.update(parent_manifest_sha256=H(old/'manifest.json'),parent_pair_sha256=H(pair),
                    parent_observation_sha256=H(observation),freezer_sha256=H(HERE/'freeze.py'),
                    preparer_sha256=H(HERE/'prepare.py'),planner_sha256=H(HERE.parent/'paired_plan.py'),
                    source_basis='HISTORICAL_PARENT',parent_git_commit=old_manifest['head'],
                    parent_source_count=len(old_manifest['order']))
    (new/'manifest.json').write_text(json.dumps(manifest))
    freezer_observation=root/'freezer-observation.json'
    def write_freezer_observation(path,snapshot):
        digest=H(snapshot/'manifest.json')
        path.write_text(json.dumps({'observed_exit_code':0,
          'observed_stdout':f'FROZEN_NOT_COMPILED {len(texts)} sources {digest}\n',
          'snapshot_manifest_sha256':digest,'snapshot_path':str(snapshot)}))
    write_freezer_observation(freezer_observation,new)
    args=[sys.executable,HERE/'prepare.py','--parent',parent,'--old-snapshot',old,'--new-snapshot',new,
          '--old-sha256',H(old/'manifest.json'),'--new-sha256',H(new/'manifest.json'),
          '--parent-pair-sha256',H(pair),'--parent-observation',observation,
          '--parent-observation-sha256',H(observation),'--freezer-observation',freezer_observation,
          '--freezer-observation-sha256',H(freezer_observation)]
    def prep(name):
        path=root/name;run(*args,'--output',path);return path
    # A rejected preparation must never create artifacts under shared
    # Foundation or Lean installations, even if those paths are writable.
    for protected in (provider, LEAN.parent.parent):
        unsafe=protected/('aq26-unsafe-output-'+root.name)
        assert not unsafe.exists()
        try:
            q=run(*args,'--output',unsafe,ok=False)
            assert q.returncode and 'output overlaps protected root' in q.stderr,(q.stdout,q.stderr)
            assert not unsafe.exists()
        finally:
            if unsafe.exists():shutil.rmtree(unsafe)
    stale=prep('stale');sidecar=stale/'author/lib/Toy/Extra.olean.private';sidecar.parent.mkdir(parents=True,exist_ok=True);sidecar.write_bytes(b'stale')
    q=run(sys.executable,HERE/'rebuild.py','--prepared',stale,'--preparation-sha256',H(stale/'preparation.json'),
          '--old-snapshot',old,'--new-snapshot',new,'--sibling','author','--expected-axiom-reports','2',ok=False)
    assert q.returncode and 'seed artifact drift' in q.stderr,(q.stdout,q.stderr)
    out=prep('extension');result=json.loads((out/'preparation.json').read_text())
    assert result['plan']['unaffected']==['Toy.A','Toy.BaseChecks']
    assert result['plan']['affected']==['Toy.Extra','Toy.Silent','Toy.ReferenceChecks']
    paired=root/'extension-pair'
    for protected in (old,new,parent,provider):
        q=run(sys.executable,HERE/'run_pair.py','--prepared',out,'--preparation-sha256',H(out/'preparation.json'),
              '--old-snapshot',old,'--new-snapshot',new,'--expected-axiom-reports','2',
              '--output',protected/'unsafe-output',ok=False)
        assert q.returncode and 'coordinator output overlaps protected root' in q.stderr
        assert not (protected/'unsafe-output').exists()
    run(sys.executable,HERE/'run_pair.py','--prepared',out,'--preparation-sha256',H(out/'preparation.json'),
        '--old-snapshot',old,'--new-snapshot',new,'--expected-axiom-reports','2','--output',paired)
    state=json.loads((paired/'pair-state.json').read_text())
    assert state['status']=='MATCHED_SELECTIVE_PASS' and [x['exit'] for x in state['runs']]==[0,0]
    assert state['source_basis']=='HISTORICAL_PARENT' and state['comparison']['source_basis']=='HISTORICAL_PARENT'
    def compare_fails(reason):
        q=run(sys.executable,HERE/'compare.py',out,old,new,H(out/'preparation.json'),ok=False)
        assert q.returncode and reason in q.stderr,(reason,q.stdout,q.stderr)
    # Forging both sibling provenance labels cannot erase the historical basis.
    saved_basis={}
    for label in ('author','peer'):
        sp=out/label/'rebuild-state.json';saved_basis[label]=sp.read_bytes();s=json.loads(saved_basis[label])
        s['source_basis']='CURRENT';sp.write_text(json.dumps(s))
    compare_fails('historical sibling basis required')
    for label,raw in saved_basis.items():(out/label/'rebuild-state.json').write_bytes(raw)
    prep=out/'preparation.json';raw=prep.read_bytes();s=json.loads(raw);s['source_basis']='CURRENT';prep.write_text(json.dumps(s))
    compare_fails('historical preparation basis required');prep.write_bytes(raw)
    # A uniform same-count forged declaration in both states and logs is rejected.
    saved={}
    for label in ('author','peer'):
        sp=out/label/'rebuild-state.json';raw=sp.read_bytes();s=json.loads(raw);row=s['records'][-1]
        lp=Path(row['log']);log=lp.read_bytes();saved[label]=(sp,raw,lp,log)
        lp.write_bytes(log.replace(b"'toyBase'",b"'toyFake'"));row['log_sha256']=H(lp)
        row['axiom_report_names']=['extResult','toyFake'];sp.write_text(json.dumps(s))
    compare_fails('per-module axioms')
    for sp,raw,lp,log in saved.values():sp.write_bytes(raw);lp.write_bytes(log)
    # Both siblings can be forged identically in a nonterminal report too.
    saved={}
    for label in ('author','peer'):
        sp=out/label/'rebuild-state.json';raw=sp.read_bytes();s=json.loads(raw);row=s['records'][0]
        lp=Path(row['log']);log=lp.read_bytes();saved[label]=(sp,raw,lp,log)
        assert b"'extResult'" in log
        lp.write_bytes(log.replace(b"'extResult'",b"'fakeResult'"));row['log_sha256']=H(lp)
        row['axiom_report_names']=['fakeResult'];sp.write_text(json.dumps(s))
    compare_fails('per-module axioms')
    for sp,raw,lp,log in saved.values():sp.write_bytes(raw);lp.write_bytes(log)
    # A report injected identically into both originally silent modules fails.
    saved={}
    for label in ('author','peer'):
        sp=out/label/'rebuild-state.json';raw=sp.read_bytes();s=json.loads(raw);row=s['records'][1]
        lp=Path(row['log']);log=lp.read_bytes();saved[label]=(sp,raw,lp,log)
        lp.write_bytes(log+b"'forged' does not depend on any axioms\n");row['log_sha256']=H(lp)
        row['axiom_report_names']=['forged'];row['axiom_reports']=[''];sp.write_text(json.dumps(s))
    compare_fails('per-module axioms')
    for sp,raw,lp,log in saved.values():sp.write_bytes(raw);lp.write_bytes(log)
    # Omitting the same absent output companion from both records must fail.
    saved_states={}
    for label in ('author','peer'):
        sp=out/label/'rebuild-state.json';raw=sp.read_bytes();saved_states[label]=raw;s=json.loads(raw)
        group=s['outputs']['Toy.Extra'];key=next(k for k,v in group.items() if v is None)
        del group[key];sp.write_text(json.dumps(s))
    compare_fails('output companion coverage')
    for label,raw in saved_states.items():(out/label/'rebuild-state.json').write_bytes(raw)
    # Direct-input guards also need all absent and present companion entries.
    for label in ('author','peer'):
        sp=out/label/'rebuild-state.json';s=json.loads(saved_states[label])
        q=s['records'][0]['direct_inputs']['Toy.A']['path'];guards=s['guarded_companions']
        key=next(q[:-6]+suffix for suffix in ('.olean.private','.olean.server','.ir','.ilean')
                 if guards.get(q[:-6]+suffix,'missing') is None)
        del guards[key];sp.write_text(json.dumps(s))
    compare_fails('input companion coverage')
    for label,raw in saved_states.items():(out/label/'rebuild-state.json').write_bytes(raw)
    # Different fresh sidecar bytes must fail even if each state's guard is
    # updated and both output inventories have the same paths.
    added=[]
    for label,contents in (('author',b'first'),('peer',b'second')):
        sp=out/label/'rebuild-state.json';s=json.loads(saved_states[label]);group=s['outputs']['Toy.ReferenceChecks']
        path=out/label/'lib/Toy/ReferenceChecks.ir';assert group[str(path)] is None
        path.write_bytes(contents);added.append(path)
        group[str(path)]={'realpath':str(path.resolve()),'sha256':H(path)};sp.write_text(json.dumps(s))
    compare_fails('fresh companion mismatch')
    for path in added:path.unlink()
    for label,raw in saved_states.items():(out/label/'rebuild-state.json').write_bytes(raw)
    # Equal-byte hardlinks across siblings must not pass as isolated copies.
    a=out/'author/lib/Toy/A.olean';b=out/'peer/lib/Toy/A.olean';data=b.read_bytes();b.unlink();os.link(a,b)
    compare_fails('sibling hardlink');b.unlink();b.write_bytes(data)
    a=out/'author/lib/Toy/Extra.olean';b=out/'peer/lib/Toy/Extra.olean';data=b.read_bytes();b.unlink();os.link(a,b)
    compare_fails('sibling hardlink');b.unlink();b.write_bytes(data)
    # Added source drift is rejected, although committed parent drift is allowed.
    a=workspace/'src/Toy/Extra.lean';raw=a.read_bytes();a.write_text('theorem bad : True := trivial\n')
    compare_fails('added workspace source drift');a.write_bytes(raw)
    # An unobserved parent coordinator exit is not accepted.
    bad=json.loads(observation.read_text());bad['observed_exit_code']=None;observation.write_text(json.dumps(bad))
    badargs=list(args);badargs[badargs.index('--parent-observation-sha256')+1]=H(observation)
    badnew=root/'bad-new';shutil.copytree(new,badnew)
    badmanifest=json.loads((badnew/'manifest.json').read_text());badmanifest['parent_observation_sha256']=H(observation)
    (badnew/'manifest.json').write_text(json.dumps(badmanifest))
    badargs[badargs.index('--new-snapshot')+1]=badnew
    badargs[badargs.index('--new-sha256')+1]=H(badnew/'manifest.json')
    badfreezer=root/'bad-freezer-observation.json';write_freezer_observation(badfreezer,badnew)
    badargs[badargs.index('--freezer-observation')+1]=badfreezer
    badargs[badargs.index('--freezer-observation-sha256')+1]=H(badfreezer)
    q=run(*badargs,'--output',root/'unobserved',ok=False)
    assert q.returncode and 'parent coordinator terminal observation does not match' in q.stderr
print('PASS: paired real-Lean historical extension; committed parent drift accepted; added-source drift, stale/differing/omitted companions, wrong names, seed/fresh hardlinks and unobserved exit rejected')
