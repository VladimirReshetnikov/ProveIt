#!/usr/bin/env python3
"""Bounded exact245 table source/audit check over one selected Core object.

No dependency builds, downloads, version queries or inherited proof-limit
options. --prepare-only checks provenance and snapshots with no compilation.
Source and audit share120 seconds, -j1 and Lean's4096MiB memory ceiling.
All path overrides must retain the pinned bytes and selected provider identity.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
MODULE = 'BusyBeaver.ZFC.TableRouting245'
EVIDENCE_REL = 'Computability/BusyBeaver/Research/ZFC/results/table-prefix246-verification.json'
CORE_REL = 'Computability/BusyBeaver/Lean/BusyBeaver/Core.lean'
DATA_REL = 'Computability/BusyBeaver/Research/ZFC/candidate-routing245'
CORE_OBJECT = Path('/tmp/zfc-native91-integration-yduvdh8f/BusyBeaver/Core.olean')
PINS = {
    'source': 'a00da51f6c813bdbb9ff573ba75a0a6cb1e7f1eb9d630758b5b1bfed4a5b673b',
    'audit': 'c31149ed1cc480deb84737f18f82212742f5abc296062aa3f6a7cded4e788796',
    'evidence': '70a9a9bfb1546a1c0c6f1503c6261d2d23637dd901e7debec220e7185137ed6d',
    'core_source': '436336133fa107c62eb00322333ec9451a0705964bd2b62fce3f44ce848672a6',
    'core_object': '2c18d0fc971038cdd3cf5998857f56a88ea1cf33cd11f90f6794866fcc2e1148',
    'compiler': 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
    'init': 'd2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e',
    'canonical': '17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13',
    'old': 'f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267',
    'renumbering': 'ff8f44548b4f121c2d8838d56fb9c7ccabcc7e78d678cab518fb3c3b5569ba76',
    'generator': '2b7e8f1eafe2a073b65eab0c2223727348db1e0283b2a91e15dbf1a0b05b167e',
    'boundary': '76c111db69c473acf86f106386a41a36bd80efb3447153948e7d025f718778bd',
    'inventory': '35da86deacfbb0e968b1f15cf500483cdb6d15edb78bbc3b9a1740a4be724886',
}

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def need(condition, message):
    if not condition:
        raise RuntimeError(message)

def imports(path):
    return re.findall(r'^import\s+(\S+)\s*$', path.read_text(), re.M)

def table(path):
    start, rows = None, {}
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            need(start is None, 'Duplicate start declaration.')
            start = int(line.split()[-1])
        if not line or line.startswith('#'):
            continue
        q,b,w,d,t = line.split()
        q,b,w,t = map(int,(q,b,w,t))
        need((q,b) not in rows and b in (0,1) and w in (0,1) and d in ('L','R'),
             'Invalid or duplicate literal row.')
        rows[q,b] = w,d,t
    return start, rows

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, default=REPO)
    ap.add_argument('--source', type=Path, default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TableRouting245.lean')
    ap.add_argument('--audit', type=Path, default=HERE/'table_routing245_audit.lean')
    ap.add_argument('--canonical', type=Path)
    ap.add_argument('--old-source', type=Path)
    ap.add_argument('--renumbering', type=Path)
    ap.add_argument('--evidence', type=Path)
    ap.add_argument('--core-source', type=Path)
    ap.add_argument('--core-object', type=Path, default=CORE_OBJECT)
    ap.add_argument('--lean', type=Path)
    ap.add_argument('--generator', type=Path, default=HERE/'generate_table_routing245.py')
    ap.add_argument('--boundary', type=Path, default=HERE/'results/table-routing245-boundary.json')
    ap.add_argument('--inventory', type=Path, default=HERE/'results/table-routing245-source-inventory.json')
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--prepare-only', action='store_true')
    a = ap.parse_args()
    repo, work = a.repo.resolve(), a.output.resolve()
    need(not work.exists() or not any(work.iterdir()), 'Use new/empty external output.')
    need(not work.is_relative_to(repo), 'Output must be outside maintained checkout.')
    files = {
        'source': a.source.resolve(), 'audit': a.audit.resolve(),
        'evidence': (a.evidence or repo/EVIDENCE_REL).resolve(),
        'core_source': (a.core_source or repo/CORE_REL).resolve(),
        'core_object': a.core_object.resolve(),
        'canonical': (a.canonical or repo/DATA_REL/'zfc_routing245.tm').resolve(),
        'old': (a.old_source or repo/DATA_REL/'zfc_routing245_old.tm').resolve(),
        'renumbering': (a.renumbering or repo/DATA_REL/'renumbering.json').resolve(),
        'generator': a.generator.resolve(), 'boundary': a.boundary.resolve(),
        'inventory': a.inventory.resolve(),
    }
    for name,path in files.items():
        need(path.is_file() and sha(path)==PINS[name], 'Changed '+name)
        need(not path.is_relative_to(work), 'An input is inside output: '+name)
    source,audit,core = files['source'],files['audit'],files['core_source']
    prior = json.loads(files['evidence'].read_text())
    need(prior['status']=='PASS' and prior['all_input_provider_postchecks'] is True and
         prior['all_fresh_objects_unchanged_after_audit'] is True and
         prior['only_standard_axioms'] is True, 'Selected Core parent must be a complete PASS.')
    need([c['label'] for c in prior['commands']]==['source','audit'] and
         all(c['exit_code']==0 and not c.get('timed_out',False) for c in prior['commands']),
         'Parent source/audit commands are not successful.')
    need(prior['source_object_recorded_before_audit'] is True, 'Parent has no pre-audit source binding.')
    core_rows = [r for r in prior['reused_modules'] if r['module']=='BusyBeaver.Core']
    need(len(core_rows)==1 and core_rows[0]['source_sha256']==PINS['core_source'] and
         core_rows[0]['object_sha256']==PINS['core_object'], 'Selected Core pair differs.')
    first = [r for r in prior['actual_first_providers'] if r['module']=='BusyBeaver.Core']
    need(len(first)==1 and first[0]['sha256']==PINS['core_object'] and
         Path(first[0]['resolved']).resolve()==Path(core_rows[0]['object']).resolve(),
         'Parent selected a different actual Core provider.')
    boundary = json.loads(files['boundary'].read_text())
    need(boundary['selected_core_parent']['sha256']==PINS['evidence'] and
         len(boundary['selected_project_providers'])==1 and
         boundary['selected_project_providers'][0]['source_sha256']==PINS['core_source'] and
         boundary['selected_project_providers'][0]['object_sha256']==PINS['core_object'],
         'Reviewed first-unit boundary differs.')
    compiler = (a.lean or Path(prior['compiler']['path'])).resolve()
    need(compiler.is_file() and sha(compiler)==PINS['compiler'] and
         prior['compiler']['sha256']==PINS['compiler'], 'Wrong compiler identity.')
    init = compiler.parent.parent/'lib/lean/Init.olean'
    need(init.is_file() and sha(init)==PINS['init'], 'Changed supplied Init provider.')
    parent_init = [q for q in prior['toolchain_providers'] if q['module']=='Init']
    need(len(parent_init)==1 and parent_init[0]['object_sha256']==PINS['init'], 'Wrong parent Init identity.')
    need(imports(core)==[] and imports(source)==['BusyBeaver.Core'] and
         imports(audit)==[MODULE], 'Import closure changed.')
    text,audit_text = source.read_text(),audit.read_text()
    need(not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text), 'Forbidden source proof shortcut.')
    need(not re.search(r'\b(sorry|admit|native_decide)\b',audit_text), 'Forbidden audit proof shortcut.')
    need(not re.search(r'set_option\s+max(Heartbeats|RecDepth)',text+audit_text), 'Use default proof limits.')
    names = re.findall(r'^theorem (\w+)',text,re.M)
    probes = re.findall(r'^#print axioms (.+)$',audit_text,re.M)
    need(len(names)==64 and probes==['SetTheory.BusyBeaver.ZFC.'+n for n in names] and
         len(re.findall(r'^example\b',audit_text,re.M))==64, 'Exact64/64 audit contract changed.')
    # Parse all emitted actions and both directions of the explicit numbering.
    pattern = r'^  \(\((true|false), \.(left|right), (\d+)\), \((true|false), \.(left|right), (\d+)\)\),? -- (\d+); old(\d+)$'
    emitted = re.findall(pattern,text,re.M)
    need(len(emitted)==245, 'Missing emitted rows.')
    actual,comments = {},{}
    for w0,d0,t0,w1,d1,t1,q,old in emitted:
        q,old = int(q),int(old)
        need(q not in comments, 'Duplicate emitted state.')
        comments[q] = old
        for b,(w,d,t) in enumerate([(w0,d0,t0),(w1,d1,t1)]):
            actual[q,b] = int(w=='true'),'R' if d=='right' else 'L',int(t)
    start,expected = table(files['canonical'])
    oldstart,oldrows = table(files['old'])
    mapping = json.loads(files['renumbering'].read_text())
    labels = mapping['canonical_to_old']
    oldnew = {int(k):v for k,v in mapping['old_to_canonical'].items()}
    need(start==0 and oldstart==95 and len(labels)==len(set(labels))==245 and
         oldnew=={**{q:i for i,q in enumerate(labels)},254:245}, 'Renumbering census differs.')
    need(set(expected)=={(q,b) for q in range(245) for b in (0,1)} and
         set(oldrows)=={(q,b) for q in labels for b in (0,1)}, 'Literal table domain differs.')
    need({(oldnew[q],b):(w,d,oldnew[t]) for (q,b),(w,d,t) in oldrows.items()}==expected,
         'Old-label canonical row bijection differs.')
    need(actual==expected and len(actual)==490 and comments==dict(enumerate(labels)),
         'Emitted actions/label comments differ from canonical data.')
    label_match = re.search(r'def oldLabelsRouting245 : Array Nat := #\[(.*?)\n\]',text,re.S)
    need(label_match is not None, 'Missing old label array.')
    emitted_labels = [int(v) for v in re.findall(r'\d+',label_match.group(1))]
    map_match = re.search(r'def oldStateRouting245 : Nat → Fin 245\n(.*?)\n  \| _ => 0',text,re.S)
    need(map_match is not None, 'Missing inverse state map.')
    emitted_inverse = {int(q):int(v) for q,v in re.findall(r'^  \| (\d+) => (\d+)$',map_match.group(1),re.M)}
    need(emitted_labels==labels and emitted_inverse=={q:i for i,q in enumerate(labels)},
         'Emitted label/inverse data differs.')
    need(oldnew[95]==0 and oldnew[96]==88 and
         {k for k,v in expected.items() if v[2]==245}=={(71,1)}, 'Start/dispatch/halt binding differs.')
    work.mkdir(parents=True,exist_ok=True)
    cache = work/'cache'; (cache/'BusyBeaver/ZFC').mkdir(parents=True)
    core_link = cache/'BusyBeaver/Core.olean'; core_link.symlink_to(files['core_object'])
    src = work/'sources/BusyBeaver/ZFC/TableRouting245.lean'; src.parent.mkdir(parents=True)
    audited = work/'Audit.lean'
    shutil.copyfile(source,src); shutil.copyfile(audit,audited)
    all_inputs = list(dict.fromkeys([Path(__file__).resolve(),*files.values(),compiler,init]))
    before = {str(p):sha(p) for p in all_inputs}
    record = dict(
        status='PREPARED_NOT_BUILT' if a.prepare_only else 'RUNNING', prepare_only=a.prepare_only,
        scope='Exact routing245 finite table/renumbering/graph only; no runtime or consistency endpoint.',
        source=dict(path=str(source),sha256=sha(source),snapshot=str(src)),
        audit=dict(path=str(audit),sha256=sha(audit),snapshot=str(audited)),
        compiler=dict(prior['compiler'],path=str(compiler)),compiler_version_query_performed=False,
        selected_parent=dict(path=str(files['evidence']),sha256=sha(files['evidence'])),
        reused_modules=[dict(module='BusyBeaver.Core',source=str(core),source_sha256=sha(core),
            object=str(files['core_object']),object_sha256=sha(files['core_object']))],
        actual_first_providers=[dict(module='BusyBeaver.Core',actual_first=str(core_link),
            resolved=str(core_link.resolve()),sha256=sha(core_link))],
        toolchain_providers=[dict(module='Init',object=str(init),object_sha256=sha(init),
            scope='Implicit supplied toolchain boundary; not rebuilt.')],
        exact_project_import_closure=True,project_module_count=1,external_boundary_count=0,
        actual_direct_tool_imports=[],dependency_build=False,downloads=False,
        LEAN_PATH=str(cache),limits=dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,
            proof_limits='Lean defaults'),
        before=before,commands=[],fresh_modules=[],generated_literal_actions_checked=490,
        emitted_renumbering_checked=True,expected_named_axiom_probes=64,expected_callers=64)
    def save():
        (work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    def post():
        record['after'] = {str(p):sha(p) for p in all_inputs}
        need(record['after']==before, 'An input/provider changed.')
        need(sha(src)==PINS['source'] and sha(audited)==PINS['audit'], 'Snapshot changed.')
        need(core_link.is_symlink() and core_link.resolve()==files['core_object'] and
             sha(core_link)==PINS['core_object'], 'Core first provider changed.')
        need(not (cache/'Init.olean').exists(), 'Implicit Init was shadowed in isolated cache.')
        record['all_input_provider_postchecks'] = True
    save()
    try:
        if a.prepare_only:
            post();save();print(work/'verification.json');return
        env = dict(os.environ,LEAN_PATH=str(cache),LEAN_NUM_THREADS='1',
                   LEAN_SYSROOT=str(compiler.parent.parent),PYTHONDONTWRITEBYTECODE='1')
        env.pop('PYTHONOPTIMIZE',None)
        deadline = time.monotonic()+120
        def run(label,command):
            began = time.monotonic();remaining = deadline-began
            need(remaining>0, 'Shared120-second budget exhausted.')
            log = work/(label+'.log')
            try:
                result = subprocess.run(command,cwd=work,env=env,capture_output=True,text=True,timeout=remaining)
            except subprocess.TimeoutExpired as error:
                def decoded(x):
                    return x.decode(errors='replace') if isinstance(x,bytes) else (x or '')
                output = decoded(error.stdout)+decoded(error.stderr);log.write_text(output)
                record['commands'].append(dict(label=label,command=command,cwd=str(work),exit_code=None,
                    timed_out=True,seconds=time.monotonic()-began,log=str(log),output=output));save()
                raise
            output = result.stdout+result.stderr;log.write_text(output)
            record['commands'].append(dict(label=label,command=command,cwd=str(work),exit_code=result.returncode,
                seconds=time.monotonic()-began,log=str(log),output=output));save()
            need(result.returncode==0 and 'sorryAx' not in output and "declaration uses 'sorry'" not in output,
                 label+' failed; inspect '+str(log))
            return output
        obj = cache/'BusyBeaver/ZFC/TableRouting245.olean'
        source_log = run('source',[str(compiler),'-j1','-M4096','--root='+str(work/'sources'),'-o',str(obj),str(src)])
        need(obj.is_file() and not obj.is_symlink(), 'Fresh source object missing.')
        fresh = dict(module=MODULE,path=str(obj),sha256=sha(obj),source_sha256=sha(src))
        record['fresh_modules'] = [fresh]
        record['source_pass_object'] = dict(fresh,source_command_index=0)
        record['source_object_recorded_before_audit'] = True
        record['fresh_first_provider_before_audit'] = dict(module=MODULE,actual_first=str(obj),
            resolved=str(obj.resolve()),sha256=sha(obj))
        save()
        audit_log = run('audit',[str(compiler),'-j1','-M4096',str(audited)])
        reports = re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",audit_log,re.S)
        need([n for n,_ in reports]==probes, 'Missing or reordered axiom reports.')
        actual_axiom_sets = [dict(name=n,axioms=[x.strip() for x in block.split(',') if x.strip()]) for n,block in reports]
        expected_axiom_sets = [dict(name=n,axioms=[] if i<6 else ['propext']) for i,n in enumerate(probes)]
        record['actual_axiom_sets'] = actual_axiom_sets
        record['expected_axiom_sets'] = expected_axiom_sets;save()
        need(actual_axiom_sets==expected_axiom_sets, 'Unexpected exact axiom distribution; inspect actual reports.')
        need(obj.is_file() and not obj.is_symlink() and sha(obj)==fresh['sha256'], 'Fresh object changed during audit.')
        post()
        record.update(status='PASS',named_axiom_probes=64,callers=64,no_axioms=False,
            only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,
            warnings=dict(source=source_log.count('warning:'),audit=audit_log.count('warning:')))
    except Exception as error:
        record.update(status='FAIL',error=str(error))
        try:
            post()
        except Exception as post_error:
            record['postcheck_error'] = str(post_error)
        save();raise
    save();print(work/'verification.json')

if __name__=='__main__':
    main()
