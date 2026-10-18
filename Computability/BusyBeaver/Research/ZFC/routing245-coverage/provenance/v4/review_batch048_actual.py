"""Independently read existing coverage evidence; no supplied code or proof execution."""
from pathlib import Path
import hashlib, json, re

B = Path('/tmp/zfc-routing245-lean/coverage-production/v4')
W = B / 'batch048-run1'
checks = 0
pins = {}
cache_hashes = {}
rows = []
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ck(value, message='evidence mismatch'):
    global checks
    assert value, message
    checks += 1
def pin(path, expected):
    path = str(Path(path))
    if path not in cache_hashes:
        cache_hashes[path] = sha(path)
    ck(cache_hashes[path] == expected, path)
    ck(path not in pins or pins[path] == expected, 'conflicting identity: ' + path)
    pins[path] = expected

def load_ref(ref):
    pin(ref['path'], ref['sha256'])
    return json.loads(Path(ref['path']).read_text())

source_review = {'path': str(B/'independent-source-family-review.json'), 'sha256': '8b6b434fffcba8ef242479f451e892cb1c84486cf3d1720f12d752e0a6d6f0b7'}
prior_review = {'path': str(B/'independent-batch024-actual-review.json'), 'sha256': '887747f26168814a2962a2846bd5d9ffda7a841582c5fb9c9c65e9757d25475f'}
load_ref(source_review); previous = load_ref(prior_review)
batch_ref = {'path': str(W/'batch.json'), 'sha256': 'eaecb6d1437784fc87a50abd709fdc81704033af0be14aa35185f2191825c42f'}
batch = load_ref(batch_ref)
ck(batch['status'] == 'PASS_SELECTED_UNITS' and not batch['prepare_only'])
ck(batch['selected_unit_indices'] == list(range(28,52)))
ck(batch['failed_unit'] is None and batch['active_unit'] is None and batch['serial'])
ck(batch['shared_wall_seconds_per_unit'] == 120)
ck(not any(batch[k] for k in ['compiler_version_query_performed','dependency_build','downloads']))
ck(len(batch['completed_units']) == 24 and len(batch['prior_batches']) == 2)
pin(batch['guard']['path'], 'c37473de1eacb7a47a397e49bbff9b0bed9eeb1efbebea21f3c0835ecf42f7b5')
ck(batch['guard']['sha256'] == pins[batch['guard']['path']])
pin(batch['manifest']['path'], 'b79fe539f343ca2f8979ada70f534f2ee08fb2361598a87f39c1e410fe6c32bc')
ck(batch['manifest']['sha256'] == pins[batch['manifest']['path']])
g = json.loads(Path(batch['manifest']['path']).read_text())
priors=[load_ref(q) for q in batch['prior_batches']]
ck(batch['prior_batches'][1] == previous['batch'])
first_review=load_ref(previous['prior_review'])
ck(batch['prior_batches'][0] == first_review['batch'])
objects = {}
records = {}
for prior,indices in zip(priors,[list(range(4)),list(range(4,28))]):
    ck(prior['status']=='PASS_SELECTED_UNITS' and prior['selected_unit_indices']==indices)
    ck(prior['guard']==batch['guard'] and prior['manifest']==batch['manifest'])
    for entry in prior['completed_units']:
        r=load_ref(entry['record']);ck(r['status']=='PASS')
        fresh,=r['fresh_modules'];pin(fresh['path'],fresh['sha256'])
        records[r['module']]=entry['record'];objects[r['module']]=fresh
# Bind each declared historical reuse to its exact existing successful record.
for name, count in [('pilot_reuse',3),('original_batch_reuse',13),('v2_cut_reuse',1),('v3_unit_reuse',8)]:
    ck(len(batch[name]) == count)
    for ref in batch[name]:
        r = load_ref(ref)
        ck(r['status'] == 'PASS')
        f, = r['fresh_modules']; pin(f['path'],f['sha256'])
        records[f['module']] = {k:ref[k] for k in ['path','sha256']}
        objects[f['module']] = f

total_inputs = 0
for expected_idx, row in zip(range(28,52),batch['completed_units']):
    r = load_ref(row['record']); u = g['units'][expected_idx]
    ck(row['status'] == r['status'] == 'PASS' and not r['prepare_only'])
    ck(row['unit_index'] == r['unit_index'] == expected_idx)
    ck(row['module'] == r['module'] == u['module'])
    ck(r['unit_kind'] == u['kind'] and r['cuts'] == u['cuts'] and r['guard_cases'] == u['guards'])
    ck(r['site_fuel'] == 4000 and r['margin'] == 64)
    ck(r['before'] == r['after'])
    ck((r['named_axiom_probes'],r['callers']) == (u['probes'],u['callers']))
    ck((r['expected_named_axiom_probes'],r['expected_callers']) == (u['probes'],u['callers']))
    ck(r['warnings'] == {'source':0,'audit':0})
    ck(r['limits'] == {'threads':1,'memory_mebibytes':4096,'shared_wall_seconds':120,'proof_limits':'Lean defaults'})
    for flag in ['all_input_provider_postchecks','only_standard_axioms','source_object_recorded_before_audit','all_fresh_objects_unchanged_after_audit','exact_project_import_closure']:
        ck(r[flag])
    ck(not any(r[k] for k in ['compiler_version_query_performed','dependency_build','downloads','source_overridden','audit_overridden']))
    ck(r['manifest'] == batch['manifest'])
    ck(r['before'][batch['guard']['path']] == batch['guard']['sha256'])
    for path, h in r['before'].items(): pin(path,h)
    total_inputs += len(r['before'])
    for role in ['source','audit']:
        q = r[role]; pin(q['path'],q['sha256']); pin(q['snapshot'],q['sha256'])
        ck(q['sha256'] == u[role+'_sha256'])
        ck(Path(q['path']).name == u[role])
    imports = re.findall(r'^import (\S+)',Path(r['source']['path']).read_text(),re.M)
    ck(imports == u['imports'])
    commands = r['commands']
    ck([c['label'] for c in commands] == ['source','audit'])
    pin(r['compiler']['path'],r['compiler']['sha256'])
    ck(not r['compiler']['compiler_version_query_performed'])
    for c in commands:
        ck(c['exit_code'] == 0 and not c['timed_out'] and not c['interrupted'])
        ck(c['command'][0] == r['compiler']['path'] and c['command'][1:3] == ['-j1','-M4096'])
        ck(Path(c['log']).read_text() == c['output']); pin(c['log'],sha(c['log']))
        ck(not re.search(r'(^|\n).*\b(?:warning|error):',c['output']))
    ck(commands[0]['command'][-1] == r['source']['snapshot'] and commands[1]['command'][-1] == r['audit']['snapshot'])
    ck(sum(c['seconds'] for c in commands) < 120)
    audit_text = Path(r['audit']['path']).read_text()
    names = re.findall(r'^#print axioms (\S+)$',audit_text,re.M)
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",commands[1]['output'])
    actual = [dict(name=n,axioms=[a.strip() for a in aa.split(',') if a.strip()]) for n,aa in reports]
    ck(len(actual) == u['probes'] and actual == r['actual_axiom_sets'])
    ck([n for n,aa in reports] == names and all(x['axioms'] == ['propext','Quot.sound'] for x in actual))
    ck(len(re.findall(r'^example\b',audit_text,re.M)) == u['callers'])
    f, = r['fresh_modules']; pin(f['path'],f['sha256'])
    ck(f['module'] == r['module'] and f['source_sha256'] == r['source']['sha256'])
    ck(all(f[k] == r['source_pass_object'][k] for k in ['module','path','sha256','source_sha256']))
    ck(r['source_pass_object']['source_command_index'] == 0)
    ck(commands[0]['command'][commands[0]['command'].index('-o')+1] == f['path'])
    first = r['fresh_first_provider_before_audit']
    ck(first['module'] == f['module'] and first['sha256'] == f['sha256'])
    ck(Path(first['actual_first']).resolve() == Path(f['path']).resolve())
    cache = Path(r['LEAN_PATH'])
    ck((cache/Path(*r['module'].split('.'))).with_suffix('.olean').resolve() == Path(f['path']).resolve())
    prov = {p['module']:p for p in r['reused_modules']}
    ck(len(prov) == len(r['reused_modules']) == r['project_module_count'])
    seen = set()
    def dfs(path):
        for mod in re.findall(r'^import (\S+)',Path(path).read_text(),re.M):
            if not mod.startswith('BusyBeaver.'): continue
            ck(mod in prov,'unknown project import '+mod)
            if mod in seen: continue
            seen.add(mod); dfs(prov[mod]['source'])
    dfs(r['source']['path']); ck(seen == set(prov))
    actual_first = {q['module']:q for q in r['actual_first_providers']}
    ck(set(actual_first) == set(prov))
    selected_dependencies = []
    for mod,p in prov.items():
        pin(p['source'],p['source_sha256']); pin(p['object'],p['object_sha256'])
        first = actual_first[mod]
        ck(first['sha256'] == p['object_sha256'])
        ck(Path(first['actual_first']).resolve() == Path(p['object']).resolve())
        ck(Path(first['resolved']).resolve() == Path(p['object']).resolve())
        ck((cache/Path(*mod.split('.'))).with_suffix('.olean').resolve() == Path(p['object']).resolve())
        if mod.startswith('BusyBeaver.ZFC.SitesRouting245'):
            ck(mod in objects,'dependency lacks earlier successful record: '+mod)
            obj = objects[mod]
            ck(p['object_sha256'] == obj['sha256'] and p['source_sha256'] == obj['source_sha256'])
            ck(Path(p['object']).resolve() == Path(obj['path']).resolve())
            ck(records[mod] in [{k:e[k] for k in ['path','sha256']} for e in r['provider_evidence']])
            selected_dependencies.append(records[mod])
    expected_parts = ['BusyBeaver.ZFC.'+x for x in u.get('refinement_parts',[])]
    ck(set(expected_parts) == {mod for mod in imports if mod.startswith('BusyBeaver.ZFC.SitesRouting245')})
    for mod in expected_parts: ck(mod in prov and mod in objects)
    ck(len(prov) == 23 + len(expected_parts))
    ck(r['external_project_boundaries'] == [])
    ck({p['module'] for p in r['toolchain_providers']} == {'Init','Lean.Elab.Tactic.Omega'})
    for p in r['toolchain_providers']:
        pin(p['object'],p['object_sha256']); ck(Path(p['actual_first']).resolve() == Path(p['object']).resolve())
    for ref in r['provider_evidence']: pin(ref['path'],ref['sha256'])
    pref = r['preparation']; ck(pref == row['preparation']); p = load_ref(pref)
    ck(p['status'] == 'PREPARED_NOT_BUILT' and p['prepare_only'] and p['commands'] == [] and p['fresh_modules'] == [])
    ck(p['before'] == p['after'] == r['before'] and p['all_input_provider_postchecks'])
    for path,h in p['before'].items(): pin(path,h)
    for k in ['source','audit','manifest','compiler','limits','reused_modules','actual_first_providers','toolchain_providers']:
        ck(p[k] == r[k])
    rows.append(dict(record=row['record'],preparation=pref,module=r['module'],unit_index=expected_idx,kind=u['kind'],cuts=u['cuts'],inputs=len(r['before']),projects=len(prov),fresh=f,probes=u['probes'],callers=u['callers'],actual_axiom_sets=actual,warnings=r['warnings'],source_seconds=commands[0]['seconds'],audit_seconds=commands[1]['seconds'],checked_generated_dependencies=selected_dependencies))
    objects[r['module']] = f; records[r['module']] = row['record']

# Rehash every distinct examined identity after the full review, without cached digests.
for path,h in pins.items(): ck(sha(path) == h,'changed during review: '+path)
ck(sum(r['probes'] for r in rows) == 25 and sum(r['callers'] for r in rows) == 25)
out = dict(status='CLEAN_EXISTING_ROUTING245_V4_BATCH048_REVIEW',findings=[],reviewer_role='Independent existing-record and provider review; not author or executor of the source generator, production guard, or proof batch.',checks=checks,reviewer_script_sha256=sha(__file__),batch=batch_ref,source_review=source_review,prior_review=prior_review,unit_indices=list(range(28,52)),units=rows,input_references=total_inputs,unique_current_identities=len(pins),current_pins=pins,probes=25,callers=25,warnings=0,source_seconds=sum(r['source_seconds'] for r in rows),audit_seconds=sum(r['audit_seconds'] for r in rows),max_source_seconds=max(r['source_seconds'] for r in rows),all_selected_current_inputs_checked=True,all_selected_actual_providers_checked=True,all_fresh_objects_recorded_before_audit=True,scope='The 24 actual v4 units28 through51 passed, including seven original-cut composition modules which use the exact earlier passed part objects. Cut058 specifically reuses Part000 from the previous batch alongside newly passed Part001. The earlier28 units retain separate reviews; Cut066 remains only partially collected in this batch. This is partial coverage, not the complete SitesRouting245 theorem, BinaryRouting245 endpoint, or a PA equivalence.',preserved_failure_boundary='The prior immutable review preserves the original timeout and two non-timeout recursion diagnostic failures; this receipt does not replace those records.',no_proof_guard_compiler_version_simulation_execution=True)
result = B/'independent-batch048-actual-review.json'
ck(not result.exists(),'immutable receipt already exists')
result.write_text(json.dumps(out,indent=2)+'\n')
print(result,sha(result),checks,total_inputs,len(pins),out['source_seconds'],out['audit_seconds'])
