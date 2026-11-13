#!/usr/bin/env python3
"""Read-only static positional-pin triage of ten captured runners; no Lean."""
from hashlib import sha256
from pathlib import Path
from collections import Counter
import ast,json,re,sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1]
INV=D/'research/trace75-upstream-141-inventory/observations/attempt01/stdout'
FINAL=D/'research/trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json'
PINS={INV:'87c27b168b3d242214d75e8de5c4165dd2c7ac9005ac680c6bc812558dbd8575',
      FINAL:'b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c'}
def need(b,m):
    if not b:raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()

# Only this finite expression grammar is interpreted; runner code is never executed.
def value(node,env):
    if isinstance(node,ast.Constant) and isinstance(node.value,str):return node.value
    if isinstance(node,ast.Name) and node.id in env:return env[node.id]
    if isinstance(node,ast.Call) and isinstance(node.func,ast.Name) and node.func.id=='Path' and len(node.args)==1 and not node.keywords:return Path(value(node.args[0],env))
    if isinstance(node,ast.List):return [value(x,env) for x in node.elts]
    if isinstance(node,ast.BinOp) and isinstance(node.op,ast.Add):return value(node.left,env)+value(node.right,env)
    if isinstance(node,ast.BinOp) and isinstance(node.op,ast.Div):return value(node.left,env)/value(node.right,env)
    if isinstance(node,ast.ListComp) and len(node.generators)==1:
        g=node.generators[0];need(isinstance(g.target,ast.Name) and not g.ifs and not g.is_async,'unsupported comprehension')
        return [value(node.elt,{**env,g.target.id:x}) for x in value(g.iter,env)]
    raise RuntimeError('unsupported positional-list syntax '+ast.dump(node,include_attributes=False))
def paths_from_runner(path):
    tree=ast.parse(path.read_text());env={};extra=None;captured=False
    for node in tree.body:
        if isinstance(node,ast.Assign):
            for target in node.targets:
                if isinstance(target,ast.Name) and target.id=='lib':env['lib']=value(node.value,env)
                if isinstance(target,ast.Name) and target.id=='extra':need(not captured and extra is None,'late or multiple extra assignments');extra=value(node.value,env)
                if isinstance(target,ast.Name) and target.id=='pins':captured=True
        elif isinstance(node,ast.AugAssign) and isinstance(node.target,ast.Name) and node.target.id=='extra':
            need(not captured and extra is not None and isinstance(node.op,ast.Add),'late or unsupported extra update');extra+=value(node.value,env)
        elif isinstance(node,ast.Expr) and isinstance(node.value,ast.Call):
            call=node.value
            if isinstance(call.func,ast.Attribute) and isinstance(call.func.value,ast.Name) and call.func.value.id=='extra':
                need(not captured and extra is not None and len(call.args)==1 and not call.keywords,'late or unsupported extra call')
                if call.func.attr=='append':extra.append(value(call.args[0],env))
                elif call.func.attr=='extend':extra.extend(value(call.args[0],env))
                else:raise RuntimeError('unsupported extra method '+call.func.attr)
    need(captured and isinstance(extra,list) and all(isinstance(p,Path) for p in extra),'no captured positional paths')
    return extra
def first_now(module,roots):
    parts=module.split('.')
    for root in roots:
        candidate=root/('/'.join(parts)+'.olean')
        if len(parts)>1 and (root/parts[0]).is_dir():
            return candidate if candidate.is_file() else None
        if candidate.is_file():return candidate
    return None
for p,h in PINS.items():need(sha(p)==h,'input drift '+str(p))
inv=json.loads(INV.read_text());final=json.loads(FINAL.read_text());project=final['selected_project'];outside=final['selected_outside']
need(inv['status']=='PASS' and final['status']=='PASS','input status')
records=[];summary=Counter()
for x in inv['records']:
    if x['module']=='ScaledOffsetGeneric' or x['exact_producer_in_six_runs'] or not x['prior_capture'] or not x['prior_capture']['all_companions_match'] or not x['prior_candidate_receipts']:continue
    project_imports={d for d in x['selected_header'] if d in project}
    compared={e['module'] for r in x['prior_candidate_receipts'] for e in r['recorded_direct_comparisons'] if e.get('matches')}
    if project_imports<=compared:continue
    n=x['module'];need(len(x['prior_candidate_receipts'])==1,'ambiguous candidate receipt '+n)
    candidate=x['prior_candidate_receipts'][0];rp=Path(candidate['path']);need(sha(rp)==candidate['sha256'],'receipt drift '+n)
    receipt=json.loads(rp.read_text());need(receipt['exit']==0 and receipt['reason'] is None and receipt['pins']==receipt['after'],'receipt status or pin drift '+n)
    output=Path(receipt['output_root'])/(n.replace('.','/')+'.olean')
    need(output.is_file() and str(output.resolve())==x['selected_realpath'] and sha(output)==receipt['object_sha256']==x['selected_olean_sha256'],'output mismatch '+n)
    snapshot=rp.parent/'source.txt';copy=Path(receipt['command'][5]);sh=receipt['pins']['source']
    need(snapshot.is_file() and copy.is_file() and sha(snapshot)==sha(copy)==sh,'source mismatch '+n)
    imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',snapshot.read_text(),re.M)
    need(imports==[d for d in x['selected_header'] if d!='Init'],'source/header mismatch '+n)
    for ext in ['stdout','stderr']:
        p=rp.parent/ext;need(p.is_file() and sha(p)==receipt[ext+'_sha256'],'log drift '+n+' '+ext)
    prototype=rp.parents[2];runner_candidates=[p for p in prototype.glob('*.py') if p.is_file() and sha(p)==receipt['pins']['runner']]
    need(len(runner_candidates)==1,'runner source not uniquely identified '+n);runner=runner_candidates[0]
    extra=paths_from_runner(runner);captured=receipt['pins']['extra'];need(len(extra)==len(captured),'positional count mismatch '+n)
    roots=[Path(p) for p in receipt['lean_path'].split(':')];direct=[]
    for dep in imports:
        selected=project.get(dep) or outside.get(dep);need(selected is not None,'final import missing '+dep)
        now=first_now(dep,roots);indexes=[i for i,p in enumerate(extra) if p==now] if now else []
        valid=[i for i in indexes if now.is_file() and sha(now)==captured[i]]
        same=bool(now and now.is_file() and sha(now)==selected['.olean']['sha256'])
        status='current_first_path_in_positional_pins' if valid else 'not_named_by_positional_path_list'
        summary[status]+=1
        if not same:summary['current_first_differs_or_missing']+=1
        direct.append({'module':dep,'recorded_lean_path_current_first':str(now) if now else None,
                       'final_selected_realpath':selected['.olean']['resolved'],'final_selected_sha256':selected['.olean']['sha256'],
                       'current_first_matches_final_hash':same,'positional_indexes':valid,'classification':status})
    records.append({'module':n,'receipt':str(rp),'receipt_sha256':candidate['sha256'],'runner':str(runner),
                    'runner_sha256':receipt['pins']['runner'],'source_sha256':sh,'output_realpath':str(output.resolve()),
                    'positional_pin_count':len(extra),'direct':direct})
need(len(records)==10,'ten-runner subset changed')
for p,h in PINS.items():need(sha(p)==h,'input changed '+str(p))
print(json.dumps({'status':'PASS','summary':dict(summary),'records':records,
 'scope':'static pinned-runner positional lists and current first-resolution only; historical path choice, implicit Init, companions, package/dynamic and transitive ancestry are not authenticated'},sort_keys=True))
