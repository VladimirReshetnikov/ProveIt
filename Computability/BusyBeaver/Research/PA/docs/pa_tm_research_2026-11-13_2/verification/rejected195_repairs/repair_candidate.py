#!/usr/bin/env python3
"""Focused semantic repair of the single failing source26 contract in candidate195."""
from pathlib import Path
from collections import defaultdict
import json
import time
import sys
from types import SimpleNamespace
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'zero_jump_machine'))
import verify as V
F=SimpleNamespace(S=V.S, BASE=V.S.load_machine())

HERE=Path(__file__).resolve().parent
S=F.S
original_oracle=S.oracle


def oracle(q,br,x):
    if isinstance(br,dict):
        tag,effect,r=x
        if effect=='mark' and q==S.LITERAL[0]:
            if r not in br:return None
            if br[r]:return S.LITERAL[97],S.box(),False
            return S.LITERAL[40],S.box('dec',r),True
        return original_oracle(q,None,x)
    return original_oracle(q,br,x)


S.oracle=oracle
ZERO={S.PHYSICAL[r]:True for r in (3,6,7)}
CONTRACTS=list(S.contracts())
BAD=next(c for c in CONTRACTS if c[0]==26)


def run(machine,c,record=None):
    i,branch,br,start,target=c
    if i==26:br=ZERO
    return S.execute(machine,br,start,target,record=record)


def save(machine,path):
    path.write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {t}\n' for(q,b),(w,d,t)in sorted(machine.items())))


def main():
    started=time.monotonic()
    successes=[]
    # First identify genuinely valid one-row implementations of the source jump.
    parent=dict(F.BASE)
    one=[]
    for destination in range(197):
        for write in (0,1):
            for move in (-1,1):
                parent[27,1]=(write,move,destination)
                if run(parent,BAD) is not None:
                    one.append([write,move,destination])
    (HERE/'valid_source26_actions.json').write_text(json.dumps({'actions_old_dense':one,
                    'actions_native':[[w,d,S.LABELS[t]]for w,d,t in one],
                    'scope':'Whole symbolic source26 contract with logical registers3,6,7 fixedzero; other source contracts and startup separate.'},indent=2)+'\n')
    print('valid_source26_actions',len(one),[[w,d,S.LABELS[t]]for w,d,t in one],flush=True)
    machine=S.load_machine(HERE/'candidate195_sparse_dense.tm')
    record=[]
    bad_result=run(machine,BAD,record)
    print('unrepaired_source26',bad_result,flush=True)
    if bad_result is not None:raise ValueError('Expected the known rejected candidate')
    possible=sorted({key for kind,conf,key in record if kind!='oracle'}-S.ENGINE_ROWS-{(45,0)})
    print('repair_row_candidates',len(possible),[[S.LABELS[q],b]for q,b in possible],flush=True)
    # Only contracts whose already-validated trace uses the repaired literal row
    # can change. Oracle contract rows are excluded above.
    affected=defaultdict(list)
    for number,c in enumerate(CONTRACTS):
        if c[0]==26:continue
        trace=[]
        if run(machine,c,trace) is None:raise ValueError(('unexpected bad contract',c[:2]))
        for key in {k for kind,conf,k in trace if kind!='oracle'}:
            affected[key].append(number)
    tested=local_pass=0
    for row in possible:
        original=machine[row]
        for destination in range(197):
            if destination==27:continue
            for write in (0,1):
                for move in (-1,1):
                    action=(write,move,destination)
                    if action==original:continue
                    tested+=1;machine[row]=action
                    if run(machine,BAD) is None:continue
                    local_pass+=1
                    failure=None
                    for number in affected[row]:
                        if run(machine,CONTRACTS[number]) is None:
                            failure=list(CONTRACTS[number][:2]);break
                    if failure is None:
                        name=f'repaired195_{row[0]}_{row[1]}_{write}_{move}_{destination}.tm'
                        save(machine,HERE/name)
                        successes.append(dict(row=list(row),action=list(action),file=name,
                                              affected_contracts=len(affected[row]),all_contracts=4959))
                        print('SURVIVOR',successes[-1],flush=True)
        machine[row]=original
        print('row',row,'tested',tested,'local_pass',local_pass,'survivors',len(successes),'elapsed',round(time.monotonic()-started,2),flush=True)
    out=dict(status='FOCUSED_SEMANTIC_REPAIR_SCREEN',correct_single_parent_actions=one,repair_rows=len(possible),
             patched_actions=tested,site26_pass=local_pass,survivors=successes,seconds=time.monotonic()-started,
             scope='One additional non-oracle row on rejected source26 trace; complete4959 symbolic contracts via affected-trace dependency check. No state lower bound.')
    (HERE/'semantic_repair_receipt.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2),flush=True)


if __name__=='__main__':main()
