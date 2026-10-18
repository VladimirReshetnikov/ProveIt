#!/usr/bin/env python3
"""Reproduce the complete diagnostic evidence for the faster253 candidate.

All work is local and uses Python's standard library. This verifies exact
finite computations and the register-program certificate. The affine TM
audit relies on the unchanged, pinned published register-box contracts.
It does not run Coq or claim kernel acceptance.
"""
from pathlib import Path
import argparse,hashlib,json,runpy
import cost_search as s
import prior_rm_verify as rm

HERE=Path(__file__).resolve().parent
DEST=HERE/'candidate'
PINS={
    '../upstream253/ZF/m254/machine/zfc_254.tm':'d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb',
    '../upstream253/ZF/m253/machine/zfc_253.tm':'84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95',
    '../upstream253/ZF/m254/coq/tm/Prog254.v':'1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746',
    '../upstream253/ZF/m254/tools/tm/symexec.py':'5bf83da419c47b9c8d79fcc755e40048f599255c2f1b2cb4656dc04bb02bb85d',
}

def digest(data):return hashlib.sha256(data).hexdigest()

def data_table(rows,start):
    return ('#! start '+str(start)+'\n'+''.join(f'{q} {b} {w} {d} {t}\n'
        for (q,b),(w,d,t) in sorted(rows.items(),key=lambda e:(str(e[0][0]),e[0][1])))).encode()

def parse(data):
    rows={};start=None
    for line in data.decode().splitlines():
        if line.startswith('#! start '):start=int(line.split()[-1]);continue
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();key=int(q),int(b)
        assert key not in rows and int(b) in (0,1) and int(w) in (0,1) and d in ('L','R')
        rows[key]=int(w),d,int(t)
    assert start is not None
    return rows,start

def literal_boot(rows,start,steps):
    state,head,tape=start,0,set()
    for _ in range(steps):
        write,direction,state=rows[state,int(head in tape)]
        if write:tape.add(head)
        else:tape.discard(head)
        head+=1 if direction=='R' else -1
    return state,head,tape

def construct():
    # The finite old-label edit can be reviewed independently of the emitter.
    rows={key:val for key,val in s.BASE253.items() if key[0] not in {'12','110','128'}}
    rows['96',0]=0,'R','257'
    rows.update({('255',0):(0,'R','148'),('255',1):(1,'R','17'),
                 ('256',0):(0,'R','255'),('256',1):(1,'R','18'),
                 ('257',0):(0,'R','33'),('257',1):(1,'R','256')})
    assert len(rows)==506
    module=runpy.run_path(str(HERE.parent/'upstream253/ZF/m253/tools/generate_candidate.py'))
    old_of=tuple({12:255,110:257,128:256}.get(q,q) for q in module['OLD_OF'])
    compact_of={q:i for i,q in enumerate(old_of)}
    assert len(compact_of)==254 and old_of[0]==5 and old_of[33]==96 and old_of[253]==254
    compact={(compact_of[int(q)],b):(w,d,compact_of[int(t)]) for (q,b),(w,d,t) in rows.items()}
    assert set(compact)=={(q,b) for q in range(253) for b in (0,1)}
    assert all(0<=t<=253 for w,d,t in compact.values())
    reached={0};todo=[0]
    while todo:
        q=todo.pop()
        if q==253:continue
        for b in (0,1):
            target=compact[q,b][2]
            if target not in reached:reached.add(target);todo.append(target)
    assert reached==set(range(254))
    return rows,compact,old_of,compact_of

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--write',action='store_true');args=ap.parse_args()
    for path,expected in PINS.items():assert digest((HERE/path).read_bytes())==expected,('pinned input mismatch',path)
    rows,compact,old_of,compact_of=construct()
    DEST.mkdir(exist_ok=True)
    expected=data_table(compact,0)
    mapdata=(json.dumps({'old_of_compact':old_of},indent=2)+'\n').encode()
    olddata=data_table(rows,'5')
    if args.write:
        (DEST/'faster253.tm').write_bytes(expected)
        (DEST/'faster253_old_labels.tm').write_bytes(olddata)
        (DEST/'state_map.json').write_bytes(mapdata)
    assert (DEST/'faster253.tm').read_bytes()==expected
    assert (DEST/'faster253_old_labels.tm').read_bytes()==olddata
    assert (DEST/'state_map.json').read_bytes()==mapdata
    # Check against the independently generated reassociation/pruning result.
    n,edge,kind=s.rot.options(s.NODES)[0]
    assert n==7 and kind=='associate_left'
    nodes,root=s.rot.mutate(s.NODES,s.ROOT,n,edge)
    result=s.evaluate(nodes,root)
    assert result['outcome']=='passed' and result['working_states']==253
    assert result.pop('table')==rows
    # The baseline compact DAG unfolds to the pinned accepted Coq program.
    assert s.sites(s.NODES,s.ROOT)==s.ctx.program_sites(s.BASE/'coq/tm/Prog254.v')
    certificate=json.loads((HERE/'results/rotation0_rm_certificate.json').read_text())
    forward=rm.check((s.NODES,s.ROOT),(nodes,root),certificate)
    backward=rm.check((nodes,root),(s.NODES,s.ROOT),[[b,a,j,k] for a,b,j,k in certificate])
    # Independent sparse execution of the complete compact tables, exact steps.
    upstream,start=parse((HERE.parent/'upstream253/ZF/m253/machine/zfc_253.tm').read_bytes())
    reference=literal_boot(upstream,start,312975)
    actual=literal_boot(compact,0,312935)
    assert {k:v for k,v in upstream.items() if v[2]==253}=={k:v for k,v in compact.items() if v[2]==253}
    assert reference==actual,'complete compact-state/head/tape endpoint differs'
    assert actual[0]==33 and actual[1]==-17 and len(actual[2])==178
    assert result['boot']['rm_prefix_steps']==330 and result['boot']['gap']==40
    assert result['boot']['ones']==sorted(actual[2])
    altered=[]
    for key,value in compact.items():
        if upstream[key]!=value:altered.append({'state':key[0],'read':key[1],'old':upstream[key],'new':value})
    output={'candidate_sha256':digest(expected),'working_states':253,'transitions':506,
            'blank_symbol':0,'start_state':0,'terminal_state':253,'dispatcher_state':33,
            'upstream_boot_steps':312975,'candidate_boot_steps':312935,'steps_saved':40,
            'exact_full_endpoint_equal':True,'endpoint_head':-17,'endpoint_ones':sorted(actual[2]),
            'endpoint_pc_normalized':'','gap':40,'source_registers':[5,0,0,0,2,0,0,0,0],
            'spare_blocks':158,'spare_nonzero':[[2,1],[8,1]],'rm_prefix_steps':330,
            'affine_cases_passed':result['branch_cases'],'protected_box_pairs':len(s.BOX_PAIRS),
            'rm_certificate_entries':len(certificate),'rm_certificate_both_directions':True,
            'all_states_graph_reachable':True,'halting_transitions_unchanged':True,
            'rm_maximum_segment':max(forward,backward),'compact_transition_delta':altered,
            'input_pins':PINS,'kernel_verified':False,
            'scope':'Exact finite literal boot and state-map checks; finite RM bisimulation; complete published affine audit with unchanged box contracts. No Coq run and no new ZFC-internal proof object. The state count ties the known253 machine.'}
    (DEST/'verification_result.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:v for k,v in output.items() if k not in {'endpoint_ones','input_pins','compact_transition_delta'}},indent=2))

if __name__=='__main__':main()
