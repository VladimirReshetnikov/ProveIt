#!/usr/bin/env python3
"""Replay the complete finite bootstrap and the uniform runtime certificate.

No network, third-party Python packages, theorem prover, huge expanded tape,
or conjectured non-halting fact is used. Every skipped register loop has an
exact recognized control graph. Every periodic tape skip checks a literal
finite transition cycle. Cantor arithmetic is retained as an exact DAG.
"""
from pathlib import Path
import argparse,hashlib,json,time
import macro252 as M
import periodic_tape252 as T
import lazy252 as L
from verify_runtime import verify
from generate_machine import generate

ROOT=Path(__file__).resolve().parents[1]

def stable(x):
    if isinstance(x,dict):return {k:stable(v) for k,v in x.items() if k!='seconds'}
    if isinstance(x,(list,tuple)):return [stable(v) for v in x]
    return x

def write(p,x):
    p.write_text(json.dumps(stable(x),indent=2)+'\n')

def replay(output,check=True):
    started=time.monotonic();output.mkdir(parents=True,exist_ok=True)
    manifest=json.loads((ROOT/'source_manifest.json').read_text())
    for item in manifest['sources']:
        p=ROOT/item['local_path']
        assert hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256'],p
    machine=generate(output/'machines')
    saved_machine=json.loads((ROOT/'machines/old_to_new.json').read_text())
    assert json.loads(json.dumps(machine))==saved_machine
    crosschecks=T.prefix_test()
    assert crosschecks==11788
    literal=M.m.blank_checkpoint()
    first=M.main(initial=literal)
    assert first['result']=='failed_local_contract'
    assert first['state']['p']=='1110100100101010001000110110110'
    assert first['state']['gap']==32
    assert first['state']['regs']==[0,4,2,10,1347166087,0,0,0,0]
    write(output/'macro32.json',first)
    one=T.recover_collision(output/'macro32.json',output/'recovered34.json')
    assert one['status']=='recovered'
    assert one['frame']['gap']==34 and one['frame']['head']==0
    assert one['frame']['regs']==[4,2,10,1347166086,0,1,0,0,0]
    assert one['frame']['steps']==2079923824320782982672
    second=M.main(initial=one['frame'])
    assert second['result']=='failed_local_contract'
    assert second['state']['gap']==34
    assert second['state']['regs']==[0,2,10,1347166092,1347166413,1,0,0,0]
    write(output/'macro34.json',second)
    two=T.recover_collision(output/'macro34.json',output/'recovered36.json')
    assert two['status']=='recovered'
    assert two['frame']['gap']==36 and two['frame']['head']==0
    assert two['frame']['regs']==[2,10,1347166092,1347166413,1,0,0,0,0]
    assert two['frame']['steps']==2101702102394623143846
    runtime=verify();write(output/'uniform252.json',runtime)
    last=L.run(two['frame'])
    assert last['status']=='root' and last['path']=='' and last['gap']==37
    assert last['relative_head']==-1 and last['normal_overflows']==1
    assert last['registers']==[2122,5,5,5,5,5,5,6217,5]
    assert len(last['nodes'])==6321
    assert last['nodes'][5]==('c',0)
    write(output/'lazy36.json',last)
    # All exterior tape is retained: this expression is a finite list of
    # arbitrary spare block values followed by the exact number of new zeros.
    # Ordinary register steps keep the dispatch head fixed except for an
    # overflow, which grows the gap by one and moves that head left once.
    # Each full-tape repair reports its own exact relative head motion.
    first_collision_head=literal['head']-(first['state']['gap']-literal['gap'])
    second_collision_head=first_collision_head+one['frame']['head']-(second['state']['gap']-one['frame']['gap'])
    absolute_head=second_collision_head+two['frame']['head']+last['relative_head']
    assert absolute_head==3 and absolute_head+last['gap']==40
    root_frame={
        'source_state':96,'state':machine['old_to_new'][96],
        'absolute_head':absolute_head,'absolute_pc_marker':absolute_head-1,
        'absolute_header':absolute_head+last['gap'],
        'head_derivation':{'literal_checkpoint':literal['head'],
                           'first_collision':first_collision_head,
                           'first_repair_relative_motion':one['frame']['head'],
                           'second_collision':second_collision_head,
                           'second_repair_relative_motion':two['frame']['head'],
                           'last_segment_relative_motion':last['relative_head']},
        'path':'','gap':37,'physical_register_nodes':last['registers'],
        'arithmetic_dag':'lazy36.json#nodes',
        'spare_tail':{'initial_block_value_runs':two['tail_blocks'],
                      'append_zero_blocks_node':last['positive_decrements']},
        'left_of_marker':'all zero','right_after_encoded_spare_tail':'all zero',
        'block_encoding':'value v is encoded as 0 followed by v+1 ones',
    }
    write(output/'root_frame.json',root_frame)
    summary={
        'scope':'Executable ordinary-mathematics certificate; not a Coq/Lean kernel build.',
        'machine_sha256':machine['sha256'],'working_states':252,
        'literal_initial_prefix_steps':999186,'periodic_sparse_crosschecks':crosschecks,
        'macro_small_graph_checks':first['discovery']['exact_small_graph_tests'],
        'first_macro_stage':{'rm_steps':first['state']['rm_steps'],'positive_decrements':first['state']['positive_decs'],'operations':first['counts'],'local_cases':first['cases']},
        'first_header_repair_tm_steps':one['frame']['steps'],
        'second_macro_stage':{'rm_steps':second['state']['rm_steps'],'positive_decrements':second['state']['positive_decs'],'operations':second['counts'],'local_cases':second['cases']},
        'second_header_repair_tm_steps':two['frame']['steps'],
        'final_macro_stage':{'operations':last['counts'],'local_cases':last['checked_local_cases'],'arithmetic_nodes':len(last['nodes']),'rm_steps_node':last['rm_steps'],'positive_decrements_node':last['positive_decrements']},
        'uniform_runtime_cases':sum(x['cases'] for x in runtime.values()),
        'final_root':'root_frame.json',
    }
    write(output/'summary.json',summary)
    names=['macro32.json','recovered34.json','macro34.json','recovered36.json','uniform252.json','lazy36.json','root_frame.json','summary.json']
    if check:
        for name in names:
            assert stable(json.loads((output/name).read_text()))==stable(json.loads((ROOT/'certificates'/name).read_text())),name
    print('COMPLETE: blank input reaches the recorded root; all uniform runtime cases pass.')
    print('Replay directory:',output)
    print('Wall seconds:',round(time.monotonic()-started,3))
    return summary

if __name__=='__main__':
    if not __debug__:raise SystemExit('Run without -O; assertions are certificate checks.')
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=ROOT/'replayed')
    p.add_argument('--write-canonical',action='store_true',help='regenerate the stored certificates instead of comparing them')
    a=p.parse_args()
    replay(ROOT/'certificates' if a.write_canonical else a.output.resolve(),check=not a.write_canonical)
