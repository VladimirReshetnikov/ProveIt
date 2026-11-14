#!/usr/bin/env python3
"""Focused semantic repair with a left-reading dispatcher and one helper row.

Retains the already checked proposed27->46 fold and its zero-row dispatcher.
Changes native46/1 to write0/1, moveleft, enter one of five specified helper
states; searches either row of that helper. Every positive would require all
4959 uniform source contracts and exact startup.
"""
from collections import defaultdict
from pathlib import Path
import json,time
import repair_candidate as R

HERE=Path(__file__).resolve().parent
S=R.S


def main():
    began=time.monotonic()
    base=S.load_machine(HERE/'candidate195_sparse_dense.tm')
    require=S.check_engine(base)
    if not require:raise ValueError('baseline changes engine')
    kept=S.LITERAL[46]
    dropped=S.LITERAL[27]
    affected=defaultdict(set)
    for i,c in enumerate(R.CONTRACTS):
        if c[0]==26:continue
        trace=[]
        if R.run(base,c,trace) is None:raise ValueError(('baseline failure',c[:2]))
        for row in {key for kind,conf,key in trace if kind!='oracle'}:affected[row].add(i)
    results=[];tested=source_pass=0;branches=[]
    for native in (31,107,108,128,310):
        helper=S.LITERAL[native]
        for write in (0,1):
            first=(write,-1,helper)
            for bit in (0,1):
                helper_row=helper,bit
                if helper_row in S.ENGINE_ROWS:raise ValueError('cannot modify engine row')
                machine=dict(base);machine[kept,1]=first
                checking=sorted(affected[kept,1]|affected[helper_row])
                local_tested=local_pass=0
                failures=defaultdict(int)
                for target in range(197):
                    if target==dropped:continue
                    for hw in (0,1):
                        for move in (-1,1):
                            action=(hw,move,target)
                            machine[helper_row]=action
                            tested+=1;local_tested+=1
                            if R.run(machine,R.BAD) is None:continue
                            source_pass+=1;local_pass+=1
                            failure=None
                            for number in checking:
                                c=R.CONTRACTS[number]
                                if R.run(machine,c) is None:
                                    failure=c[:2];failures[str(failure)]+=1;break
                            if failure is not None:continue
                            # Explicit final whole-contract gate, independently
                            # of dependency pruning.
                            for c in R.CONTRACTS:
                                if R.run(machine,c) is None:raise ValueError(('dependency error',c[:2]))
                            if not S.check_engine(machine):raise ValueError('engine changed')
                            name=f'dispatch195_{native}_{write}_{bit}_{hw}_{move}_{target}.tm'
                            R.save(machine,HERE/name)
                            item=dict(file=name,first_row_native=[46,1],
                                      first_action_native=[write,-1,native],
                                      helper_row_native=[native,bit],
                                      helper_action_native=[hw,move,S.LABELS[target]],
                                      all_contracts=4959,unchanged_engine=True)
                            results.append(item)
                            print('SURVIVOR',item,flush=True)
                entry=dict(helper_native=native,first_write=write,helper_bit=bit,
                           tested=local_tested,source26_pass=local_pass,
                           affected_contracts=len(checking),first_failures=dict(failures))
                branches.append(entry)
                print(entry,'elapsed',round(time.monotonic()-began,2),flush=True)
    out=dict(status='FOCUSED_TWO_ROW_DISPATCH_SCREEN',tested=tested,source26_pass=source_pass,
             survivors=results,branches=branches,seconds=time.monotonic()-began,
             scope='Five specified helpers, both leaf writes, either helper row, all existing write/move/destination actions. Other table rows fixed; no general lower bound.')
    (HERE/'two_row_dispatch_receipt.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items()if k!='branches'},indent=2),flush=True)


if __name__=='__main__':main()
