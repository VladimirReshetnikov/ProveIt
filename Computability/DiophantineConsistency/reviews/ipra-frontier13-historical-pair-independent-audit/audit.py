#!/usr/bin/env python3
"""Independent point-in-time audit of the historical joint 13-variable sibling artifacts."""
import hashlib,json,os,re,subprocess,time
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency'
RUN=Path('/tmp/ipra-frontier13-historical-paired-run-01');PARENT=Path('/tmp/ipra-aq29-fresh-project-pair');OLD=Path('/tmp/ipra-aq29-fresh-source-closure-v2');NEW=RUN/'snapshot';PREP=RUN/'prepared';PAIR=RUN/'pair'
EVID=BASE/'reviews/ipra-frontier13-historical-pair-terminal';PRIOR=BASE/'reviews/fresh-project-pair-independent-audit';TOOLS=BASE/'research/ipra-standard-13-frontier/historical';POLICY=TOOLS/'task-policy.json'
RATE=8*1024*1024;started=time.monotonic();read_bytes=0;cache={}
def digest(path):
    global read_bytes
    p=Path(path);real=p.resolve(strict=True);st=real.stat();key=(str(real),st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns)
    if key not in cache:
        h=hashlib.sha256()
        with real.open('rb') as f:
            while chunk:=f.read(1024*1024):
                h.update(chunk);read_bytes+=len(chunk);delay=read_bytes/RATE-(time.monotonic()-started)
                if delay>0:time.sleep(delay)
        after=real.stat();assert (after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns,after.st_ctime_ns)==key[1:],('mutation',str(real));cache[key]=h.hexdigest()
    return cache[key]
def J(p):return json.loads(Path(p).read_text())
def guard(entries):
    for name,record in entries.items():
        q=Path(name)
        if record is None:assert not os.path.lexists(q),('unexpected companion',name)
        else:assert q.is_file() and str(q.resolve())==record['realpath'] and digest(q)==record['sha256'],('guard',name)
def check_seed_binding(pinned,seeds):
    if pinned!=seeds:raise ValueError('seed inventory differs from pinned parent outputs')
suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
script_sha=digest(__file__);outer=J(EVID/'outer-terminal-observation.json');observation=J(RUN/'pair-observation.json');pair=J(PAIR/'pair-state.json');prep=J(PREP/'preparation.json');old=J(OLD/'manifest.json');new=J(NEW/'manifest.json');policy=J(POLICY)
assert outer['observed_exit_code']==0 and outer['session_id']==83295
assert outer['observed_stdout'].endswith('author exit 0\npeer exit 0\nMATCHED_SELECTIVE_PASS 8 affected modules\n')
assert outer['pair_observation_sha256']==digest(RUN/'pair-observation.json')==digest(EVID/'pair-observation.json')
assert observation['observed_exit_code']==0 and observation['observed_stdout']=='author exit 0\npeer exit 0\nMATCHED_SELECTIVE_PASS 8 affected modules\n'
assert observation['pair_state_path']==str(PAIR/'pair-state.json')
assert digest(PAIR/'pair-state.json')==digest(EVID/'pair-state.json')==observation['pair_state_sha256']==outer['pair_state_sha256']=='bc1e548b6a35d05569cdf53c941a9f728e649edd0f29ea769dc691986fbc44a5'
assert pair['status']=='MATCHED_SELECTIVE_PASS' and pair['source_basis']=='HISTORICAL_PARENT'
assert pair['comparison']['status']=='MATCHED_SELECTIVE_PASS' and pair['comparison']['affected_modules']==8 and pair['comparison']['seed_modules']==1210
assert [(r['label'],r['exit']) for r in pair['runs']]==[('author',0),('peer',0)]
assert digest(PREP/'preparation.json')==pair['preparation_sha256']==outer['preparation_sha256']=='7c33063c00906e9969635bcda7522e5f7f6a2a4692ccb2ba037caecd1af1b924'
assert prep['status']=='PREPARED_NOT_REBUILT' and prep['source_basis']=='HISTORICAL_PARENT'
assert prep['workspace_head_before']==prep['workspace_head_after']=='31a336689d670c87ff5da441393599bdb8b4bcd7'
assert digest(OLD/'manifest.json')==prep['old_snapshot_sha256']=='63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
assert digest(NEW/'manifest.json')==prep['new_snapshot_sha256']==outer['snapshot_manifest_sha256']=='1ff658a6021b0457f561be0c56a64c2e6547ab8639a7c82c8801f81849979710'
assert digest(POLICY)==new['target_policy_sha256']=='18258bc1c51e59d883688efb2eaf76f9c8f2dfa4d6128582a0d967bedef13b6b'
assert J(RUN/'preparer-process.json')['observed_exit_code']==0 and digest(RUN/'preparer-process.json')==digest(EVID/'preparer-process.json')
assert J(RUN/'freezer-process.json')['exit_code']==0 and digest(RUN/'freezer-process.json')==digest(EVID/'freezer-process.json')
assert digest(RUN/'freezer-observation.json')==prep['freezer_observation_sha256']==digest(EVID/'freezer-observation.json')
for name,key in [('rebuild.py','driver_sha256'),('compare.py','comparator_sha256'),('run_pair.py','coordinator_sha256')]:assert digest(TOOLS/name)==pair[key]
assert digest(TOOLS/'prepare.py')==prep['preparer_sha256']==new['preparer_sha256']
assert digest(PARENT/'pair-state.json')==prep['parent_pair_sha256']=='04832cc18c11ad9da49d2cfc0c865baed07a18ace44d1de9d8319b150890e7dd'
prior=J(PRIOR/'receipt.json');terminal=J(PRIOR/'terminal-observation.json')
assert terminal['exit_code']==0 and terminal['receipt_sha256']==digest(PRIOR/'receipt.json')
assert prior['status']=='PASS_INDEPENDENT_PAIRED_ARTIFACT_AUDIT' and prior['pair_state_sha256']==prep['parent_pair_sha256']
parent_observation=Path(prep['parent_observation']);assert digest(parent_observation)==prep['parent_observation_sha256']
assert J(parent_observation)['observed_exit_code']==0 and J(parent_observation)['pair_state_sha256']==prep['parent_pair_sha256']
assert len(old['order'])==1210 and new['order'][:1210]==old['order'] and new['parent_source_count']==1210
names=new['order'][1210:];assert len(names)==len(set(names))==8 and names==policy['addition_order']==prep['plan']['affected']
assert prep['plan']['unaffected']==old['order'] and prep['plan']['changed']==[]
assert new['source_basis']=='HISTORICAL_PARENT' and new['parent_git_commit']==old['head'] and new['head']==new['head_after']==prep['workspace_head_before']
assert all(new['sources'][name]==old['sources'][name] for name in old['order'])
assert new['expected_axiom_by_module']==policy['expected_axiom_by_module'] and new['expected_axiom_names']==policy['expected_axiom_names']
assert sum(map(len,new['expected_axiom_by_module'].values()))==13
assert new['target']==policy['target']=='DiophantineConsistency.IPRAStandardProduct13'
sum_name='DiophantineConsistency.IPRAStandardSquareSums13'; product_name='DiophantineConsistency.IPRAStandardProduct13'
sum_reports=['DiophantineConsistency.IPRASquareSumsNative.'+n for n in ('sameZero','bridge','equivalence','literal_eq','literal_equivalence')]+[sum_name+'.'+n for n in ('literal_equivalence','selected_foundation_consistency','literal_iff_translated_consistency')]
product_reports=['DiophantineConsistency.HAAdaptiveDirectOrdinate86.polynomialBridge']+[product_name+'.'+n for n in ('native_equivalence','literal_equivalence','selected_foundation_consistency','literal_iff_translated_consistency')]
assert new['expected_axiom_by_module']=={n:(sum_reports if n==sum_name else product_reports if n==product_name else []) for n in names}
assert new['expected_axiom_names']==product_reports
print('Checking all frozen sources and Git additions',flush=True)
for name in new['order']:
    row=new['sources'][name];path=NEW/row['snapshot_path'];assert path.is_file() and not path.is_symlink() and digest(path)==row['sha256']
    if name in old['sources']:assert digest(OLD/old['sources'][name]['snapshot_path'])==row['sha256']
    else:
        spec=policy['sources'][name];assert all(row[k]==spec[k] for k in ('workspace_path','sha256','imports'))
        blob=subprocess.run(['git','show',new['head']+':'+row['workspace_path']],cwd=ROOT,check=True,capture_output=True).stdout
        assert hashlib.sha256(blob).hexdigest()==row['sha256']
for key,path in [('lakefile_sha256','lakefile.toml'),('lean_toolchain_sha256','lean-toolchain')]:assert old[key]==new[key]==digest(ROOT/path)
endpoint=(NEW/new['sources'][product_name]['snapshot_path']).read_text()
assert 'theorem literal_iff_translated_consistency : standardTheory ⊢' in endpoint
assert 'AdaptiveDirectOrdinate86Literal.naturalExpression86 🡘' in endpoint
assert '(Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ :=' in endpoint
square=(NEW/new['sources'][sum_name]['snapshot_path']).read_text()
assert 'theorem literal_iff_translated_consistency : standardTheory ⊢' in square
assert 'AdaptiveDirectOrdinateSquareSumsLiteral.literal CurrentWindowCarry2011.ports' in square
assert '(Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ :=' in square
# The two package selections must be byte-identical to the author-draft blobs.
author_manifest=J(BASE/'research/ipra-standard-13-frontier/author-additions.json')
package_rows=J(EVID/'selected-package-sources.json')
assert digest(EVID/'selected-package-sources.json')==outer['selected_package_source_rows_sha256']=='7595c47b34c951d372082904c9b8fbe9e7d157aac433263c69bfce611db4a0ac'
selected=('DiophantineConsistency.AdaptiveDirectOrdinateSquareSumsLiteral','DiophantineConsistency.IPRASquareSumsNative')
assert set(package_rows)==set(selected)
for name in selected:
    row=new['sources'][name];author=author_manifest['sources'][name]
    assert row==package_rows[name] and row['sha256']==author['sha256'] and row['imports']==author['imports']
    package_blob=subprocess.run(['git','show',new['head']+':'+row['workspace_path']],cwd=ROOT,check=True,capture_output=True).stdout
    author_blob=subprocess.run(['git','show',author_manifest['source_commit']+':'+author['workspace_path']],cwd=ROOT,check=True,capture_output=True).stdout
    saved=(EVID/'selected-package-sources'/Path(row['workspace_path']).name).read_bytes()
    assert package_blob==author_blob==saved==(NEW/row['snapshot_path']).read_bytes()
parent_states={label:J(PARENT/label/'state.json') for label in ('author','peer')}
for native in ('DiophantineConsistency.HAAdaptiveDirectOrdinate86','DiophantineConsistency.AdaptiveDirectOrdinate86Literal','DiophantineConsistency.AdaptiveDirectOrdinateSquareSums'):
    native_rows=[next(r for r in parent_states[label]['records'] if r['module']==native) for label in ('author','peer')]
    assert native_rows[0]['exit']==native_rows[1]['exit']==0 and native_rows[0]['object_sha256']==native_rows[1]['object_sha256']
for label in ('author','peer'):
    ps=parent_states[label];assert ps['status']=='PASS' and ps['manifest_sha256']==prep['old_snapshot_sha256']
    assert digest(PARENT/label/'state.json')==prior[label+'_state_sha256']
provider_path=Path(parent_states['author']['provider']);provider=J(provider_path)
assert digest(provider_path)==prior['foundation_provider_receipt_sha256'] and provider['status']=='BUILT' and provider['exit_code']==0
assert parent_states['author']['provider_receipt_sha256']==parent_states['peer']['provider_receipt_sha256']==digest(provider_path)
assert digest(parent_states['author']['lean_path'])==parent_states['author']['lean_sha256']==parent_states['peer']['lean_sha256']
assert digest(parent_states['author']['foundation_input_path'])==parent_states['author']['foundation_input_sha256']
foundation=Path(provider['root'])/'.lake/build/lib/lean/Foundation';guard(provider['declared_external_guard'])
actual_f={str(x.relative_to(foundation)) for x in foundation.rglob('*') if x.is_file() or x.is_symlink()}
assert actual_f==set(provider['foundation_artifacts']) and len(actual_f)==1540
for path,sha in provider['foundation_artifacts'].items():
    q=foundation/path;assert q.is_file() and not q.is_symlink() and digest(q)==sha
print('Checking independent sibling seeds, objects, logs, imports and companions',flush=True)
results={};all_inodes={};allowed={'propext','Classical.choice','Quot.sound'};rx=re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",re.M|re.S)
for label in ('author','peer'):
    state_path=PREP/label/'rebuild-state.json';state=J(state_path);process=next(x for x in pair['runs'] if x['label']==label)
    assert digest(state_path)==digest(EVID/label/'rebuild-state.json')==process['builder_state_sha256']==pair['comparison'][label+'_state_sha256']
    assert digest(process['process_log'])==digest(EVID/(label+'-process.log'))==process['process_log_sha256'] and process['exit']==0
    assert state['status']=='PASS' and state['phase']=='complete' and state['sibling']==label and state['source_basis']=='HISTORICAL_PARENT'
    assert state['preparation_sha256']==digest(PREP/'preparation.json') and state['new_snapshot_sha256']==digest(NEW/'manifest.json')
    assert [r['module'] for r in state['records']]==names and set(state['outputs'])==set(names)
    lib=PREP/label/'lib';seed=prep['seeds'][label];assert len(seed)==1210
    expected_inventory=set(seed);parents=parent_states[label];direct=0;reports=[]
    parentlib=PARENT/label/'lib'
    pinned_seeds={str(Path(path).relative_to(parentlib)):entry['sha256']
                  for group in parents['outputs'].values()
                  for path,entry in group.items() if entry is not None}
    check_seed_binding(pinned_seeds,seed)
    changed=dict(seed);changed[next(iter(changed))]='0'*64
    try:check_seed_binding(pinned_seeds,changed)
    except ValueError:pass
    else:raise AssertionError('modified seed binding accepted')
    for rel,sha in seed.items():
        child=lib/rel;original=PARENT/label/'lib'/rel
        assert child.is_file() and not child.is_symlink() and original.is_file() and not original.is_symlink()
        assert digest(child)==sha==digest(original)
        assert (child.stat().st_dev,child.stat().st_ino)!=(original.stat().st_dev,original.stat().st_ino)
    for group in parents['outputs'].values():guard(group)
    declared_guards=set()
    for i,row in enumerate(state['records']):
        name=row['module'];spec=new['sources'][name];assert row['exit']==0 and row['source_sha256']==spec['sha256']
        obj=lib/(name.replace('.','/')+'.olean');assert obj.is_file() and not obj.is_symlink() and digest(obj)==row['object_sha256']
        outputs=state['outputs'][name];assert set(outputs)=={str(obj)[:-6]+s for s in suffixes} and outputs[str(obj)]['sha256']==row['object_sha256'];guard(outputs)
        expected_inventory.update(str(Path(p).relative_to(lib)) for p,v in outputs.items() if v is not None)
        log=Path(row['log']);assert digest(log)==digest(EVID/label/'rebuild-logs'/log.name)==row['log_sha256'];text=log.read_text()
        assert not re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b|\bsorry\b',text)
        matches=rx.findall(text);assert [x[0] for x in matches]==row['axiom_report_names']==new['expected_axiom_by_module'][name]
        assert [x[1] for x in matches]==row['axiom_reports']
        assert all({x.strip() for x in values.split(',') if x.strip()}<=allowed for _,values in matches);reports.extend(x[0] for x in matches)
        declared=set(spec['imports']);actual=set(row['direct_inputs']);assert declared<=actual and actual-declared<={'Init'}
        for dep,item in row['direct_inputs'].items():
            direct+=1;q=Path(item['path']);declared_guards.update(str(q)[:-6]+s for s in suffixes)
            g=state['guarded_companions'][str(q)];assert g is not None and g['sha256']==item['sha256']==digest(q)
            if dep in new['sources']:
                kind='seed' if dep in old['sources'] else 'fresh';assert item['kind']==kind and q==lib/(dep.replace('.','/')+'.olean')
                assert new['order'].index(dep)<new['order'].index(name)
            else:
                pkg=Path(parents['package_overlay']);tool=Path(parents['lean_path']).parent.parent/'lib/lean';base={'package':pkg,'toolchain':tool}[item['kind']]
                assert q==base/(dep.replace('.','/')+'.olean')
                if dep.startswith('Foundation.'):assert item['kind']=='package' and q.resolve().is_relative_to(foundation.resolve())
    assert set(state['guarded_companions'])==declared_guards;guard(state['guarded_companions'])
    actual={str(p.relative_to(lib)) for p in lib.rglob('*') if p.is_file() or p.is_symlink()}
    assert actual==expected_inventory and not any((lib/x).is_symlink() for x in actual)
    for rel in actual:
        q=lib/rel;key=(q.stat().st_dev,q.stat().st_ino);assert key not in all_inodes,('cross-sibling/duplicate hardlink',label,rel);all_inodes[key]=(label,rel)
    assert len(reports)==13 and reports==[n for name in names for n in new['expected_axiom_by_module'][name]]
    results[label]={'state_sha256':digest(state_path),'rows':len(state['records']),'direct_imports':direct,'reports':len(reports),'guard_paths':len(state['guarded_companions']),'inventory':len(actual)}
a=J(PREP/'author/rebuild-state.json');b=J(PREP/'peer/rebuild-state.json')
for x,y in zip(a['records'],b['records']):
    for k in ('module','exit','source_sha256','object_sha256','log_sha256','axiom_report_names','axiom_reports'):assert x[k]==y[k],(x['module'],k)
    assert {n:(v['kind'],v['sha256']) for n,v in x['direct_inputs'].items()}=={n:(v['kind'],v['sha256']) for n,v in y['direct_inputs'].items()}
assert prep['seeds']['author']==prep['seeds']['peer'] and results['author']['inventory']==results['peer']['inventory']
for p,expected in [(PAIR/'pair-state.json',outer['pair_state_sha256']),(PREP/'preparation.json',outer['preparation_sha256']),(NEW/'manifest.json',outer['snapshot_manifest_sha256']),(Path(__file__),script_sha)]:assert digest(p)==expected
result={'status':'PASS_INDEPENDENT_FRONTIER13_PAIRED_ARTIFACT_AUDIT','pair_state_sha256':digest(PAIR/'pair-state.json'),'preparation_sha256':digest(PREP/'preparation.json'),
        'snapshot_manifest_sha256':digest(NEW/'manifest.json'),'outer_observation_sha256':digest(EVID/'outer-terminal-observation.json'),
        'parent_pair_sha256':digest(PARENT/'pair-state.json'),'parent_audit_receipt_sha256':digest(PRIOR/'receipt.json'),
        'sibling_results':results,'source_rows':len(new['order']),'added_modules':len(names),'expected_diagnostics':13,'foundation_artifacts':len(actual_f),
        'source_basis':'HISTORICAL_PARENT','workspace_drifts':len(new['parent_source_drift']),'script_sha256':script_sha,'hash_bytes_read':read_bytes,'elapsed_seconds':round(time.monotonic()-started,2),
        'scope':'Independent point-in-time audit of historical joint 13-variable paired artifacts and inherited provider evidence; no Lean replay, formal PDF semantics, current-source claim, package-transitive/dynamic load trace, or guarantee against transient mutation. Foundation wrapper outer exit remains unobserved.'}
out=HERE/'receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(result['status'],digest(out),flush=True)
