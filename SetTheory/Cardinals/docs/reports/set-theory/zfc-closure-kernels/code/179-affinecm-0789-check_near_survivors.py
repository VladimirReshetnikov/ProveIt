#!/usr/bin/env python3
"""Independently bind three late-failing tables, startup prefixes and scope.

The universal tail-extension argument is ordinary mathematics: the fixed
failing prefix never reads a cell in which a valid register/spare/gap
valuation can differ. No proof-assistant theorem is asserted.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parent
REF=ROOT.parent if(ROOT.parent/'k215.tm').exists()else ROOT.parent/'deliverable'
sys.path.insert(0,str(REF))
from audit_spare_counterexamples import table,build,decoded,source_output,SIZE,ORIGIN
import json,hashlib

def blank(rows):
    tape=bytearray(SIZE);q=0;h=ORIGIN
    for tick in range(100001):
        assert 1<h<SIZE-2 and q!=215
        if tick and q==83:
            frame=decoded(tape,h)
            if frame is not None:
                return dict(steps=tick,frame=frame,one_cells=[i-ORIGIN for i,b in enumerate(tape)if b])
        assert tick<100000
        wr,d,z=rows[q,tape[h]];tape[h]=wr;h+=d;q=z

def witness_prefix(rows,w):
    tape=build(w['site'],w['registers'],w['spares'],w['gap']);original=bytes(tape)
    q=83;h=ORIGIN;reads=[]
    for tick in range(w['steps']):
        assert tick==0 or q!=83,'An earlier dispatcher control occurred'
        assert q!=215 and 1<h<SIZE-2
        reads.append(h-ORIGIN)
        wr,d,z=rows[q,tape[h]];tape[h]=wr;h+=d;q=z
    assert q==83 and h==ORIGIN
    out=decoded(tape,h);assert out==w['actual']
    assert max(reads)<64 and bytes(tape[ORIGIN+64:])==original[ORIGIN+64:]
    targets=[]
    for positive in [False,True]:
        regs=[0]*9
        if positive:regs[w['site'][2]]=1
        want=source_output(w['site'],regs);assert want is not None
        targets.append(want[0]);assert want[0]!=out['pc_one_positions']
    return dict(min_read_head=min(reads),max_read_head=max(reads),intermediate_dispatcher_controls=0,
                zero_branch_counter=targets[0],positive_branch_counter=targets[1],actual_counter=out['pc_one_positions'])

def main():
    parent=table(REF/'k215.tm');base=blank(parent)
    first=json.loads((ROOT/'forced_provider_results.json').read_text())
    refined=json.loads((ROOT/'forced_provider_refinement.json').read_text())
    lookup={(c['provider'],c['mode']):c for c in first['results']}
    results=[]
    for p in [95,188,213]:
        c=next(r for r in refined['results']if r['provider']==p and r['mode']=='both')
        rows={k:v for k,v in parent.items()if k[0]!=189};rows[66,0]=(1,1,p)
        rows[p,0]=parent[189,0];rows[p,1]=parent[189,1]
        assert len(rows)==428 and all(z!=189 for wr,d,z in rows.values())
        startup=blank(rows);assert startup['frame']==base['frame'] and startup['one_cells']==base['one_cells']
        assert lookup[p,'both']['blank_start']==dict(kind='first_clean_dispatch',steps=startup['steps'],**startup['frame'])
        prefix=witness_prefix(rows,c['witness'])
        raw=('#! start 0\n'+''.join(f'{q} {b} {wr} {"R"if d==1 else"L"} {z}\n'for(q,b),(wr,d,z)in sorted(rows.items()))).encode()
        name=f'rejected_provider{p}_214.dense.tm';(ROOT/name).write_bytes(raw)
        reach={0};pending=[0]
        while pending:
            q=pending.pop()
            for b in(0,1):
                if(q,b)in rows:
                    z=rows[q,b][2]
                    if z not in reach:reach.add(z);pending.append(z)
        results.append(dict(provider=p,mode='both',table=name,table_sha256=hashlib.sha256(raw).hexdigest(),
                            listed_working_states=214,graph_reachable_working_states=len(reach-{215}),
                            passed_full_source_cases=c['passed_full_source_cases'],startup=startup,
                            witness=c['witness'],prefix=prefix,
                            consequence='At this exact source address the fixed prefix fails for every natural register file, every nonnegative gap and every nonempty finite natural spare suffix, since it reads and writes only cells below64 and returns to the dispatcher with an incorrect continuation for both source branches. Only excluding the source address itself can avoid this primitive mismatch. Blank-run calibration remains undecided.'))
    result=dict(status='THREE_STARTUP_MATCHES_AND_REGISTER_INDEPENDENT_PREFIX_OBSTRUCTIONS_CHECKED',parent_startup=base,results=results,
                scope='The startup matches are exact finite tape configurations at a decoded frame, not correctness or calibration theorems. The tail-extension argument is ordinary finite-trace reasoning, not proof-assistant kernel verification.')
    (ROOT/'near_survivors_checked.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'])
    for r in results:print(r['provider'],r['passed_full_source_cases'],r['startup']['steps'],r['prefix']['min_read_head'],r['prefix']['max_read_head'],r['table_sha256'])

if __name__=='__main__':main()
