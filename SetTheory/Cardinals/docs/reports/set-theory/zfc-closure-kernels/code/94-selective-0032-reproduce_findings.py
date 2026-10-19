#!/usr/bin/env python3
"""Reproduce bounded framework findings, not a 244-state consistency theorem.

The default run checks exact table construction, three complete blank prefixes,
the literal first-frame discrepancy, all 8,391 symbolic instruction cases for
the contracted scanner, and the bounded state-166 local router search.
--full also recompiles and repeats all three finite mutation sweeps.
No stochastic search is required to verify the retained checkpoint.
"""
from __future__ import annotations
import argparse,gzip,hashlib,json,os,subprocess,sys,tempfile,time
from pathlib import Path

HERE=Path(__file__).resolve().parent
PIN='f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267'
PHYSICAL=(6,2,0,4,3,7,8,5,1)

def read_table(path):
    table={}
    for line in path.read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,t=line.split();table[int(q),int(b)]=(int(w),d,int(t))
    return table

def encode(table,start=95):
    return '#! start '+str(start)+'\n'+''.join(f'{q} {b} {w} {d} {t}\n'for(q,b),(w,d,t)in sorted(table.items()))

def exact_blank(table,steps):
    ones=set();q,h=95,0
    for _ in range(steps):
        w,d,q=table[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
    # Independently represented dense tape; neither scan nor macro shortcut.
    cells=bytearray(2*steps+3);origin=steps+1;position,q2=origin,95
    for _ in range(steps):
        w,d,q2=table[q2,cells[position]];cells[position]=w
        position+=1 if d=='R' else -1
    dense=[i-origin for i,x in enumerate(cells)if x]
    assert (q2,position-origin,dense)==(q,h,sorted(ones))
    assert q==96 and min(ones)==h-1
    header=min(x for x in ones if x>=h);maximum=max(ones)
    values=[];position=header+1
    while position<=maximum:
        assert position not in ones and position+1 in ones
        first=position+1;position=first
        while position in ones:position+=1
        values.append(position-first-1)
    assert len(values)>=10
    logical=[values[i]for i in PHYSICAL]
    assert logical[1]==logical[2]==logical[5]==0
    return {'steps':steps,'state':q,'head':h,'header':header,'header_distance':header-h,
            'physical_registers':values[:9],'logical_registers':logical,
            'spare_values':values[9:],'one_count':len(ones),'all_one_positions':sorted(ones),
            'all_other_cells_zero':True,'sparse_dense_exact_agreement':True}

def run_python(name,env):
    result=subprocess.run([sys.executable,str(HERE/name)],env=env,check=True,capture_output=True,text=True)
    return result.stdout.strip()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--reference',type=Path,default=Path(os.environ.get('ZFC245_REFERENCE',str(HERE.parent/'packages/zfc245-proof-20261018'))))
    ap.add_argument('--full',action='store_true',help='Also repeat the three finite C++ mutation sweeps.')
    ap.add_argument('--output',type=Path,default=HERE/'framework-reproduction.json')
    args=ap.parse_args();reference=args.reference.resolve();began=time.monotonic()
    assert __debug__,'Assertions are mandatory; do not run Python with -O.'
    source=reference/'certificate/machine_old.tm'
    assert hashlib.sha256(source.read_bytes()).hexdigest()==PIN
    assert (HERE/'base_old.tm').read_bytes()==source.read_bytes()
    table=read_table(source);results={'baseline_old_table_sha256':PIN,'working_states_baseline':len(table)//2}
    boot_specs=[('baseline245',table,407915,[3,0,0,0,3,0,0,0,0],-5,181,167)]
    t244={k:v for k,v in table.items()if k[0]!=58};t244[41,0]=(0,'L',84)
    t243={k:v for k,v in t244.items()if k[0]!=41};t243[29,0]=(0,'L',84)
    for label,edited in [('unverified_scanner244',t244),('unverified_scanner243',t243)]:
        states={q for q,b in edited};assert {t for w,d,t in edited.values()}-states=={254}
        old_text=encode(edited);(HERE/(label+'_old.tm')).write_text(old_text)
        order=[95]+sorted(states-{95});mapping={q:i for i,q in enumerate(order)}|{254:len(states)}
        canonical={(mapping[q],b):(w,d,mapping[t])for(q,b),(w,d,t)in edited.items()}
        (HERE/(label+'.tm')).write_text(encode(canonical,0))
        (HERE/(label+'_renumbering.json')).write_text(json.dumps({'old_to_canonical':mapping,'canonical_to_old':order,'status':'UNVERIFIED_DIAGNOSTIC_ONLY'},indent=2)+'\n')
    boot_specs.extend([('unverified_scanner244',t244,818324,[6,0,0,0,4,0,0,0,1],-8,245,233),
                       ('unverified_scanner243',t243,1389062,[6,0,0,0,6,0,0,0,1],-8,331,321)])
    boots={}
    for label,edited,steps,logical,h,D,spares in boot_specs:
        boot=exact_blank(edited,steps)
        assert (boot['logical_registers'],boot['head'],boot['header_distance'])==(logical,h,D)
        assert boot['spare_values']==[1]*spares
        boots[label]=boot;print(label,'exact blank prefix PASS',flush=True)
    (HERE/'exact-blank-prefixes.json').write_text(json.dumps(boots,indent=2)+'\n')
    env={**os.environ,'ZFC245_REFERENCE':str(reference)}
    run_python('literal_scanner_counterexample.py',env)
    literal=json.loads((HERE/'literal_scanner_counterexample.json').read_text())
    assert literal['baseline']['steps']==574 and literal['mutant']['steps']==650
    assert literal['baseline']['status']=='EXPECTED_FIRST_CLEAN_FRAME'
    assert literal['mutant']['status']=='DIFFERENT_FIRST_CLEAN_FRAME'
    results['first_clean_frame_disagreement']={'baseline_steps':574,'mutant_steps':650,'baseline_added_one':15,'mutant_added_one':13}
    run_python('collect_scanner_failures.py',env)
    failures=json.loads((HERE/'shorter58-full-failures.json').read_text())
    assert (failures['cases'],failures['failed_cases'])==(8391,99)
    assert failures['by_opcode']=={'CD':98,'CI':1}
    sites=json.loads((reference/'certificate/sites_physical.json').read_text())
    bad_indices={case['index']for case in failures['failures']}
    assert bad_indices=={i for i,(p,op,r)in enumerate(sites)if '000000' in p}
    assert len(bad_indices)==50 and all(sites[i][0].endswith('000000')for i in bad_indices)
    results['symbolic_audit']={'guarded_cases':8391,'failed_cases':99,'failed_source_leaves':50,
        'scope':'Failure of the inherited sufficient symbolic checker; fuel is 1000 symbolic rules per case.'}
    run_python('map_scanner_contexts.py',env)
    contexts=json.loads((HERE/'scanner-semantic-contexts.json').read_text())
    assert contexts['bad_leaf_context_counts']=={'AX':49,'MP':1}
    results['scanner_source_contexts']=contexts['bad_leaf_context_counts']
    run_python('reachable_scanner_discrepancy.py',env)
    reachable=json.loads((HERE/'reachable-scanner-discrepancy.json').read_text())
    assert reachable['blank_prefix_steps']==835524 and reachable['contracted244_wrong_return_step_from_blank']==837626
    results['blank_reachable_first_clean_frame_disagreement']={k:reachable[k]for k in('blank_prefix_steps','source_index','source_path','contracted244_wrong_return_step_from_blank','independent_sparse_dense_exact_agreement')}
    run_python('local_reroute_search.py',env)
    local=json.loads((HERE/'local_reroute_search.json').read_text())
    assert all(not row['replacement_states'] for row in local['results'])
    results['state166_local_search']={'forced_written_bits':[0,1],'bounded_steps':12,'replacements':0}
    checkpoint=json.loads((HERE/'zero5-710418.json').read_text())
    assert checkpoint['rules_count']==132 and checkpoint['properties']==[3,6,45,11]
    run_python('verify_zero5_checkpoint.py',env)
    results['zero5_search_checkpoint']={k:checkpoint[k]for k in ('rules_count','properties','iterations','seconds','seed')}
    # Retained mutation records explicitly concern finite fixtures and fuel.
    records={}
    for name,expected in [('merge-search-summary.json',119560),('edge-reroute-summary.json',119316),('combined-reroute-summary.json',1566)]:
        record=json.loads((HERE/name).read_text());assert record['candidate_count']==expected
        assert record.get('finite_only') is True;records[name]=record
    assert records['merge-search-summary.json']['full_literal_pass_count']==0
    assert records['edge-reroute-summary.json']['full_literal_pass_count']==109
    assert records['combined-reroute-summary.json']['survivors']==0
    if args.full:
        programs=[(reference/'code/state_reduction/resource_merge_search.cpp','merge-search-summary.json'),
                  (HERE/'edge_reroute_search.cpp','edge-reroute-summary.json'),
                  (HERE/'combined_reroute_search.cpp','combined-reroute-summary.json')]
        with tempfile.TemporaryDirectory(prefix='zfc-framework-')as td:
            directory=Path(td)
            fixture=directory/'fixtures.txt';fixture.write_bytes(gzip.decompress((reference/'inputs/state_reduction/candidate245-literal-cases.txt.gz').read_bytes()))
            for code,summary in programs:
                executable=directory/code.stem
                subprocess.run(['g++','-O3','-std=c++17',str(code),'-o',str(executable)],check=True,capture_output=True,text=True)
                subprocess.run([str(executable),str(fixture)],cwd=directory,check=True,capture_output=True,text=True)
                fresh=json.loads((directory/summary).read_text())
                assert {k:v for k,v in fresh.items()if k!='seconds'}=={k:v for k,v in records[summary].items()if k!='seconds'}
                print(summary,'finite sweep reproduced',flush=True)
    results['mutation_records']=records;results['mutation_sweeps_freshly_repeated']=args.full
    results['status']='PASS_FINDINGS_REPRODUCED'
    results['scope']='This status certifies reproduction of the stated finite findings, not correctness or consistency equivalence of a 244-state or 243-state machine.'
    results['seconds']=time.monotonic()-began
    args.output.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__=='__main__':main()
