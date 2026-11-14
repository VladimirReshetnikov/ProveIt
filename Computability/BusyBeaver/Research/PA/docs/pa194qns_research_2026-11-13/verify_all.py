#!/usr/bin/env python3
"""Reproduce and verify both delivered PA194QNS/PA194QS constructions offline.

Default mode reruns the construction symbolic engine and the independent
literal-tape symbolic engine for both families. --quick skips those four
long symbolic passes, verifies their frozen receipts and input bindings,
and still rebuilds exact tables, source graphs, all local folds and complete
blank startup. All new output goes to a separate temporary directory.

No repository checkout, network, solver or third-party package is required.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,subprocess,sys,tempfile
from concurrent.futures import ThreadPoolExecutor

ROOT=Path(__file__).resolve().parent
FAMILIES=('PA194QNS','PA194QS')

def require(test,message):
    if not test:raise AssertionError(message)

def load(path):return json.loads(path.read_text())
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def dump(path,value):path.write_text(json.dumps(value,indent=2)+'\n')

def child(base,name):
    path=(base/name).resolve()
    require(path!=base.resolve() and base.resolve() in path.parents,'Path escapes its package directory: '+name)
    return path

def check_manifest():
    manifest=ROOT/'SHA256SUMS'
    if not manifest.exists():
        return {'status':'not_present','note':'Initial development replay permitted before the final release manifest is written.'}
    count=0
    for line in manifest.read_text().splitlines():
        if not line.strip():continue
        parts=line.split(maxsplit=1);require(len(parts)==2,'Malformed SHA256SUMS line')
        expected,name=parts
        if name.startswith('*'):name=name[1:]
        require(re.fullmatch(r'[0-9a-fA-F]{64}',expected) is not None,'Malformed digest')
        path=child(ROOT,name)
        require(path.is_file() and sha(path)==expected.lower(),'Manifest mismatch: '+name)
        count+=1
    require(count>0,'Empty SHA256SUMS')
    return {'status':'PASS','listed_files_verified':count,'manifest_sha256':sha(manifest)}

def run_script(work,label,script,*args):
    command=[sys.executable,'-B',str(ROOT/script),*[str(x) for x in args]]
    print('Running '+label+' ...',flush=True)
    log=work/'logs'/(label+'.log')
    env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
    with log.open('w') as stream:
        result=subprocess.run(command,cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT,env=env)
    if result.returncode:
        raise RuntimeError(label+' failed; log '+str(log)+'\n'+log.read_text()[-8000:])
    return {'status':'PASS','log':str(log)}

def compare_build(family,generated,quick):
    frozen=ROOT/'machines'/family
    exact_files=('machine.tm','machine.native.tm','raw.native.tm','parent.native.tm')
    json_files=('labels.json','source.json','instructions.json','sites.json','nodes.json',
                'parent.instructions.json','folds.json','local_cases.json')
    for name in exact_files:
        require((generated/name).read_bytes()==(frozen/name).read_bytes(),family+' rebuilt byte mismatch: '+name)
    for name in json_files:
        require(load(generated/name)==load(frozen/name),family+' rebuilt JSON-value mismatch: '+name)
    built=load(generated/'construction_receipt.json');old=load(frozen/'construction_receipt.json')
    for key in ('family','working_states','transition_rows','native_start','native_halt','dense_start','dense_halt',
                'raw_states','fixed_states','AX_readers','AX_folds','controller_folds','folds','simultaneous_fold_cases',
                'source_sites','source_outcomes','source_prefix_identical_to_parent','removed_source_sites',
                'startup','arithmetic_box_rows_unchanged','graph_reachable_working_states','dense_sha256','native_sha256',
                'physical_register_map'):
        require(built[key]==old[key],family+' construction field mismatch: '+key)
    require(built['generic_runtime_performed']==(not quick),'Incorrect symbolic replay flag')
    if not quick:require(built['symbolic_runtime']==old['symbolic_runtime'],'Construction symbolic receipt differs')
    return {'status':'PASS','exact_byte_files':list(exact_files),'equal_JSON_value_files':list(json_files),
            'note':'JSON object/list content is compared exactly; harmless whitespace and object-key formatting may differ.',
            'construction_symbolic_replay':'skipped' if quick else 'PASS',
            'full_blank_startup_rerun':True,'startup_steps':built['startup']['steps'],
            'dense_sha256':sha(generated/'machine.tm'),'native_sha256':sha(generated/'machine.native.tm'),
            'rebuilt_source_sha256':sha(generated/'source.json'),'frozen_source_sha256':sha(frozen/'source.json')}

def check_recorded(family):
    machine=ROOT/'machines'/family;recorded=ROOT/'verification/recorded'/family
    r=load(recorded/'receipt.json');construction=load(machine/'construction_receipt.json')
    require(r['status']=='PASS' and r['family']==family,'Wrong frozen independent receipt')
    for field,name in (('dense_sha256','machine.tm'),('native_sha256','machine.native.tm'),('source_sha256','source.json')):
        require(r[field]==sha(machine/name),family+' frozen receipt input mismatch: '+name)
    require(r['contracts_sha256']==sha(recorded/'contracts.json'),family+' frozen contracts digest mismatch')
    for name in ('labels.json','sites.json','instructions.json'):
        require(load(recorded/name)==load(machine/name),family+' frozen literal binding mismatch: '+name)
    contracts=load(recorded/'contracts.json');sites=load(machine/'sites.json')
    expected={(i,positive) for i,(_,op,_) in enumerate(sites) for positive in ((False,True) if op=='dec' else (False,))}
    observed={(x['site'],x['positive']) for x in contracts}
    require(observed==expected and len(contracts)==len(expected)==r['source_contracts'],'Frozen branch coverage mismatch')
    require(r['source_sites']==len(sites)==construction['source_sites'],'Frozen source size mismatch')
    require(r['source_contracts']==construction['source_outcomes'],'Frozen outcome count mismatch')
    require(sum(x['symbolic_steps'] for x in contracts)==r['symbolic_steps'],'Frozen symbolic count mismatch')
    require(max(x['symbolic_steps'] for x in contracts)==r['maximum_symbolic_steps'],'Frozen maximum count mismatch')
    require(min(x['duration'][0] for x in contracts)==r['minimum_positive_duration_constant']>0,'Frozen positive progress mismatch')
    require(r['arithmetic_box_oracles'] is False and r['list_lemmas_rederived_from_actual_rows']==4,'Frozen checker scope mismatch')
    require(len(load(recorded/'list_lemmas.json'))==4,'Frozen list lemma count mismatch')
    require(r['independent_cfg_resolvers_agree'] and r['declared_instruction_graph_exact'] and r['dense_native_conjugacy_exact'],'Frozen identity flags missing')
    seed=load(recorded/'blank_seed.json');startup=construction['startup']
    require(r['whole_blank_tape_equal'] and r['startup_steps']==startup['steps']==58004,'Frozen startup receipt mismatch')
    require(seed['state']==startup['state'] and seed['head']==startup['head'],'Frozen startup endpoint mismatch')
    require(seed['ones']==startup['one_cells'],'Frozen whole startup support mismatch')
    require(seed['physical_registers']+seed['spare_values']==startup['physical_file'],'Frozen register seed mismatch')
    require(seed['source_site']==25 and seed['source_path']==sites[25][0],'Frozen source entry mismatch')
    return {'status':'PASS','scope':'Frozen receipt integrity, coverage bookkeeping, and exact table/source/seed bindings only; this check does not rerun the symbolic proof.',
            'receipt_sha256':sha(recorded/'receipt.json'),'dense_sha256':r['dense_sha256'],'native_sha256':r['native_sha256'],
            'source_sha256':r['source_sha256'],'contracts_sha256':r['contracts_sha256'],'source_contracts':r['source_contracts']}

def import_census():
    spec=importlib.util.spec_from_file_location('release_census',ROOT/'comparison/current_census.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

def check_frontier(work):
    module=import_census();directory=ROOT/'comparison/frontier40_tables'
    manifest=load(directory/'manifest.json');frontier=ROOT/'comparison/combined_frontier194.json'
    require(manifest['classes']==40 and manifest['combined_frontier_sha256']==sha(frontier),'Frozen frontier manifest binding mismatch')
    expected={tuple(x['canonical']) for x in load(frontier)};seen=set()
    for item in manifest['tables']:
        path=child(directory,item['file']);require(sha(path)==item['sha256'],'Raw frontier table digest mismatch: '+item['file'])
        parsed=module.parse_table(path.read_bytes());require(parsed is not None,'Invalid frontier table')
        rows,states,start,halts=parsed;key,roots=module.canonical(rows,states)
        require(len(states)==194 and len(rows)==388 and start==item['declared_or_dense_start'],'Frontier machine metadata mismatch')
        require(key==tuple(item['canonical']) and key in expected and key not in seen,'Frontier exact tuple mismatch or duplicate')
        require(module.graph_digest(key)==item['whole_graph_sha256'],'Frontier graph digest mismatch')
        seen.add(key)
    require(len(seen)==40 and seen==expected,'Raw tables do not cover the exact frontier')
    receipt={'status':'PASS','classes':40,'exact_original_table_bytes_retained':True,'all_raw_tuples_equal_frozen_frontier':True,
             'manifest_sha256':sha(directory/'manifest.json'),'frontier_sha256':sha(frontier)}
    dump(work/'frontier_replay.json',receipt);return receipt

def compare_fresh_literal(family,generated,evidence):
    fresh=load(evidence/'receipt.json');old=load(ROOT/'verification/recorded'/family/'receipt.json')
    require(fresh['status']=='PASS','Fresh literal replay did not pass')
    for field,name in (('dense_sha256','machine.tm'),('native_sha256','machine.native.tm'),('source_sha256','source.json')):
        require(fresh[field]==sha(generated/name),'Fresh literal input hash mismatch: '+name)
    for field in ('family','working_states','transition_rows','dense_sha256','native_sha256','source_sites','source_contracts',
                  'symbolic_steps','maximum_symbolic_steps','minimum_positive_duration_constant','list_lemmas_rederived_from_actual_rows',
                  'arithmetic_box_oracles','startup_steps','whole_blank_tape_equal','contracts_sha256'):
        require(fresh[field]==old[field],family+' fresh literal result differs: '+field)
    for name in ('labels.json','sites.json','instructions.json','blank_seed.json','list_lemmas.json','contracts.json'):
        require(load(evidence/name)==load(ROOT/'verification/recorded'/family/name),'Fresh literal evidence differs: '+name)
    return {'status':'PASS','receipt':str(evidence/'receipt.json'),'source_contracts':fresh['source_contracts'],
            'symbolic_steps':fresh['symbolic_steps'],'list_lemmas_rederived_from_actual_rows':4,'arithmetic_box_oracles':False}

def main():
    require(__debug__ and not sys.flags.optimize,'Assertions must be enabled; do not use -O or PYTHONOPTIMIZE.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--quick',action='store_true',help='Skip both full symbolic engines; verify recorded bindings and rerun all finite/source/structural checks.')
    ap.add_argument('--work',type=Path,help='New output directory outside this release; default is a fresh system temporary directory.')
    args=ap.parse_args()
    manifest=check_manifest()
    if args.work:
        work=args.work.resolve();require(not work.exists(),'Choose a new work directory.')
        require(work!=ROOT and ROOT not in work.parents,'Work directory must be outside the frozen release.')
        work.mkdir(parents=True)
    else:work=Path(tempfile.mkdtemp(prefix='pa194qns-replay-'))
    (work/'logs').mkdir();(work/'machines').mkdir()
    result={'status':'RUNNING','mode':'quick' if args.quick else 'full','output_directory':str(work),'manifest':manifest,'families':{}}
    implementation_files=[ROOT/'verify_all.py',ROOT/'build.py']
    implementation_files+=list((ROOT/'verification').glob('*.py'))
    implementation_files+=list((ROOT/'verification/reference').glob('*.py'))
    implementation_files+=list((ROOT/'vendor').rglob('*.py'))
    implementation_files+=[ROOT/'comparison/check_novelty.py',ROOT/'comparison/current_census.py']
    result['implementation_sha256']={str(path.relative_to(ROOT)):sha(path) for path in sorted(set(implementation_files))}
    print('Evidence directory: '+str(work),flush=True)
    if args.quick:
        print('QUICK MODE: full construction and independent literal symbolic replays are skipped. Frozen physical receipts are checked only for integrity and exact bindings. Exact blank startup is still rerun.',flush=True)
    def reconstruct_family(family):
        generated=work/'machines'/family
        options=['--family',family,'--output',generated]+(['--quick'] if args.quick else [])
        run_script(work,'build_'+family,'build.py',*options)
        return {'reconstruction':compare_build(family,generated,args.quick),'recorded_physical_receipts':check_recorded(family)}
    # Each builder is a separate process and writes only its own temporary
    # machine directory. Their module-level compiler state is not shared.
    with ThreadPoolExecutor(max_workers=2) as pool:
        pending={family:pool.submit(reconstruct_family,family) for family in FAMILIES}
        for family in FAMILIES:result['families'][family]=pending[family].result()
    binding=work/'source_binding'
    run_script(work,'bind_q_sources','verification/bind_q_sources.py',ROOT/'inputs/parent_qn.nodes.json',ROOT/'inputs/q.grammar.json',
               ROOT/'inputs/parent_qn.instructions.json',work/'machines/PA194QNS/instructions.json',work/'machines/PA194QS/instructions.json',binding)
    for parent,family in (('QN','PA194QNS'),('Qpush','PA194QS')):
        require(load(binding/(parent+'_instructions.json'))==load(work/'machines'/family/'parent.instructions.json'),'Independent parent source differs: '+parent)
        run_script(work,'source_preservation_'+family,'verification/check_source_preservation.py',binding/(parent+'_instructions.json'),
                   work/'machines'/family/'instructions.json','--output',work/('source_preservation_'+family+'.json'))
    run_script(work,'emitter_exchange','verification/check_emitter.py','--output',work/'emitter_exchange.json')
    result['source_binding']=load(binding/'source_binding_receipt.json')
    result['source_preservation']={family:load(work/('source_preservation_'+family+'.json')) for family in FAMILIES}
    result['emitter_exchange']=load(work/'emitter_exchange.json')
    result['frontier']=check_frontier(work)
    candidate_tuples=[];module=import_census()
    for family in FAMILIES:
        run_script(work,'novelty_'+family,'comparison/check_novelty.py',work/'machines'/family/'machine.tm','--frontier',
                   ROOT/'comparison/combined_frontier194.json','--output',work/('novelty_'+family+'.json'))
        novelty=load(work/('novelty_'+family+'.json'))
        require(novelty['frontier_classes']==40 and novelty['novel_in_recognized_corpus'] and not novelty['matches'],'Novelty check failed')
        result['families'][family]['novelty']=novelty
        rows,states,_,_=module.parse_table((work/'machines'/family/'machine.tm').read_bytes())
        candidate_tuples.append(module.canonical(rows,states)[0])
    require(candidate_tuples[0]!=candidate_tuples[1],'Candidates are the same action graph')
    def replay_literal(family):
        evidence=work/'literal'/family
        run_script(work,'literal_'+family,'verification/check_literal.py',work/'machines'/family,'--output',evidence)
        return compare_fresh_literal(family,work/'machines'/family,evidence)
    if not args.quick:
        with ThreadPoolExecutor(max_workers=2) as pool:
            pending={family:pool.submit(replay_literal,family) for family in FAMILIES}
            for family in FAMILIES:result['families'][family]['fresh_literal_replay']=pending[family].result()
    else:
        for family in FAMILIES:
            result['families'][family]['fresh_literal_replay']={'status':'SKIPPED','reason':'--quick; frozen receipts are not represented as fresh physical verification.'}
    result['candidates_structurally_distinct']=True
    result['status']='PASS'
    result['physical_replays_skipped']=args.quick
    result['scope']='Exact deterministic constructions, whole startup, source/guard preservation, emitter/exchange, and 40-class novelty; '+('full symbolic engines skipped, frozen physical receipt bindings checked.' if args.quick else 'both full physical symbolic implementations rerun for each machine.')
    dump(work/'receipt.json',result)
    print(json.dumps({'status':result['status'],'mode':result['mode'],'physical_replays_skipped':args.quick,
        'whole_blank_startups_rerun':True,'frontier_classes':40,'candidates_structurally_distinct':True,
        'receipt':str(work/'receipt.json'),'scope':result['scope']},indent=2),flush=True)

if __name__=='__main__':main()
