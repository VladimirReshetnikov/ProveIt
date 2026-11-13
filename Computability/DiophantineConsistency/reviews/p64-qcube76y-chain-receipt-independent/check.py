#!/usr/bin/env python3
"""Read-only direct-input and receipt audit; runs no Lean."""
import ast,hashlib,json,os,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent; research=here.parents[1]/'research'
stages=[('graph','p64-qcube76-independent-y-guarded-check/observations/attempt04',[]),
('bounds','p64-qcube76-independent-y-guarded-check/observations/bounds-attempt03',['pell_c_bound','strong_f_bound','strict_auxiliary','old_root_ne_zero']),
('binding','p64-qcube76y-binding-guarded-check/observations/attempt01',['first','main','strong','auxiliary','transport','output','auxiliary_same_square','output_same_square']),
('graphmodel','p64-qcube76y-graph-model-guarded-check/observations/attempt02',['residuals','main_root']),
('size','p64-qcube76y-size-guarded-check/observations/attempt06',['actual_f_bound']),
('strict','p64-qcube76y-strict-guarded-check/observations/attempt01',['oldV_decomposition','auxiliary_eval','actual_strict']),
('oldroot','p64-qcube76y-oldroot-guarded-check/observations/attempt03',['nonzero_of_aux_norm','old_root_ne_zero']),
('witness','p64-qcube76y-witness-guarded-check/observations/attempt02',['positive_magnitude','positive_difference','old_to_new_conditional','new_to_old_conditional']),
('conditional','p64-qcube76y-join-guarded-check/observations/conditional01',['positive_zero_iff_of_guards']),
('full','p64-qcube76y-join-guarded-check/observations/full01',['positive_zero_iff']),
('ipra','p64-qcube76y-ipra-guarded-check/observations/attempt02',['positiveBridge','native_equivalence','standard_equivalence','reference_equivalence'])]
expected_links={'P64QCube76Y':'graph','IndependentYBounds':'bounds','P64QCube76YBinding':'binding','IndependentYGraphDraft':'graphmodel','IndependentYSizeDraft':'size','IndependentYStrictDraft':'strict','IndependentYOldRootDraft':'oldroot','IndependentYWitnessDraft':'witness','IndependentYJoinDraft':'conditional','IndependentYFullJoinDraft':'full'}
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=[]; objects={}; issues=[]; monitor_asts={}
for label,sub,names in stages:
    d=research/sub; receipt=d/'result.json'; log=d/'compile.log'; x=json.loads(receipt.read_text())
    if x.get('status')!='PASS' or x.get('exit')!=0 or x.get('stop_reason') is not None or not x.get('guards_stable') or x['guards_before']!=x['guards_after']:
        issues.append(label+': failed recorded status or guard stability')
    if x.get('group_rss_samples',0)<1 or x['sampled_peak_group_rss_bytes']>=x['sampled_group_rss_limit_bytes'] or x['minimum_memavailable_bytes']<x['min_required_memavailable_bytes']:
        issues.append(label+': monitor receipt mismatch')
    if sha(log)!=x['log_sha256']: issues.append(label+': log hash mismatch')
    packet=d.parent.parent
    runners=[str(t) for t in packet.glob('*.py') if sha(t)==x.get('runner_sha256')]
    helper=packet/'missing_child.py'
    if len(runners)!=1: issues.append(label+': recorded runner missing or ambiguous')
    else:
        tree=ast.parse(Path(runners[0]).read_text())
        functions=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='group_rss']
        if len(functions)!=1: issues.append(label+': group_rss function missing')
        else: monitor_asts[label]=hashlib.sha256(ast.dump(functions[0],include_attributes=False).encode()).hexdigest()
    if not helper.is_file() or sha(helper)!=x.get('missing_child_helper_sha256'):
        issues.append(label+': missing-child helper mismatch')
    cmd=x['command']; sources=[Path(a) for a in cmd if a.endswith('.lean')]; src=sources[0] if len(sources)==1 else None
    if src is None or str(src) not in x['guards_before'] or sha(src)!=x['guards_before'][str(src)]['sha256']:
        issues.append(label+': source guard mismatch')
        continue
    obj=Path(cmd[cmd.index('-o')+1]);
    if not obj.is_file() or obj.is_symlink() or sha(obj)!=x['object_sha256']:
        issues.append(label+': object mismatch')
    objects[label]={'path':str(obj),'sha256':x['object_sha256']}
    namespace=src.stem
    expected=[]
    for n in names:
        ax='[propext]' if label=='binding' or (label=='strict' and n in ('oldV_decomposition','auxiliary_eval')) else '[propext, Classical.choice, Quot.sound]'
        expected.append(f"'{namespace}.{n}' depends on axioms: {ax}")
    if log.read_text()!=''.join(line+'\n' for line in expected):issues.append(label+': axiom log not exact')
    direct=[]
    for line in src.read_text().splitlines():
        if not line.startswith('import '):continue
        mod=line[7:].strip(); rel=mod.replace('.','/')+'.olean'; search=[Path(p)/rel for p in x['lean_path'].split(':') if p]
        selected=next((p for p in search if p.is_file()),None)
        if selected is None:
            issues.append(label+': unresolved import '+mod);continue
        guard=x['guards_before'].get(str(selected),'MISSING_GUARD')
        if not isinstance(guard,dict) or guard.get('sha256')!=sha(selected):
            issues.append(label+': selected import unguarded or changed '+mod+' '+str(selected))
        if mod in expected_links:
            earlier=objects.get(expected_links[mod])
            if earlier is None or str(selected)!=earlier['path'] or sha(selected)!=earlier['sha256']:
                issues.append(label+': chain mismatch '+mod)
        direct.append({'module':mod,'path':str(selected),'sha256':sha(selected)})
    for path,item in x['guards_before'].items():
        pp=Path(path)
        if item is None:
            if os.path.lexists(pp):issues.append(label+': recorded absence now exists '+path)
        elif not pp.is_file() or str(pp.resolve())!=item['realpath'] or sha(pp)!=item['sha256']:
            issues.append(label+': guard missing or changed '+path)
    rows.append({'stage':label,'receipt_sha256':sha(receipt),'log_sha256':sha(log),'source_sha256':sha(src),'object':objects[label],
                 'runner':runners[0] if len(runners)==1 else None,'runner_sha256':x.get('runner_sha256'),
                 'missing_child_helper_sha256':x.get('missing_child_helper_sha256'),
                 'samples':x['group_rss_samples'],'sampled_peak_group_rss_bytes':x['sampled_peak_group_rss_bytes'],
                 'minimum_memavailable_bytes':x['minimum_memavailable_bytes'],'direct_imports':direct})
if len(set(monitor_asts.values()))!=1: issues.append('group_rss monitor implementations differ')
parent=research/'p64-qcube77-ipra-draft/observations/attempt01'; pr=json.loads((parent/'result.json').read_text())
parent_obj=Path('/tmp/p64-qcube77-ipra-check01/P64QCube77Endpoint.olean')
if pr['exit']!=0 or pr['object_sha256']!=sha(parent_obj) or sha(parent/'compile.log')!=pr['log_sha256']:
    issues.append('77 parent endpoint receipt mismatch')
for pp,hh in pr['guards_before_after'].items():
    if not Path(pp).is_file() or sha(pp)!=hh: issues.append('77 parent endpoint direct guard mismatch '+pp)
for n in ('positiveBridge','native_equivalence','standard_equivalence','reference_equivalence'):
    if f"'P64QCube77Endpoint.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" not in (parent/'compile.log').read_text():
        issues.append('77 parent missing axiom report '+n)
if not any(i['module']=='P64QCube77Endpoint' and i['sha256']==pr['object_sha256'] for i in rows[-1]['direct_imports']):
    issues.append('76Y client does not link to checked 77 parent')
failed=research/'p64-qcube76y-ipra-guarded-check/observations/attempt01'; f=json.loads((failed/'result.json').read_text());fl=(failed/'compile.log').read_text()
if f['status']!='FAILED' or f['exit']!=-6 or f['object_sha256'] is not None or Path(f['command'][f['command'].index('-o')+1]).exists() or 'lean::memory_exception' not in fl or sha(failed/'compile.log')!=f['log_sha256']:
    issues.append('earlier iPRA client failure mismatch')
result={'status':'PASS' if not issues else 'ISSUES','script_sha256':sha(__file__),'stages':rows,'issues':issues,'failed_ipra_attempt01':{'receipt_sha256':sha(failed/'result.json'),'log_sha256':sha(failed/'compile.log'),'exit':f['exit'],'object':f['object_sha256']},
        'group_rss_ast_hashes':monitor_asts,'parent77_receipt_sha256':sha(parent/'result.json'),'parent77_object_sha256':pr['object_sha256'],
        'endpoint_timeout_reason_label':'runner compares to 180 seconds but emits a 120-second timeout message; no timeout fired',
        'scope':'Read-only current source/object/log/direct-import and sampled receipt audit, not fresh Lean or full project/package/dynamic ancestry, JSON/gzip/PDF binding.'}
out=here/'result.json';payload=json.dumps(result,indent=2,sort_keys=True)+'\n'
if sys.argv[1:]==['--write']:
    with out.open('x') as ff:ff.write(payload)
elif sys.argv[1:]:raise SystemExit('usage: python3 -I -S -B check.py [--write]')
elif out.read_text()!=payload:raise SystemExit('result differs')
print(json.dumps({'status':result['status'],'stages':len(rows),'issues':issues},indent=2))
if issues:raise SystemExit(1)
