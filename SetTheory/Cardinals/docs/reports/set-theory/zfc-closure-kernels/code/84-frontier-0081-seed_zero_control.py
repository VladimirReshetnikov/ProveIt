#!/usr/bin/env python3
"""Finite exact DAG control: first NIP cache from the 246 logical seed."""
import hashlib
import json
from pathlib import Path
import atomic_target_experiment as m

here=Path(__file__).resolve().parent
blob=(here/'inputs/Dag254.v').read_bytes()
assert hashlib.sha256(blob).hexdigest()==m.recovery.SOURCE_SHA256['ZF/m254/coq/prog/Dag254.v']
nodes,_=m.recovery.parse_dag(blob.decode())
initial=[3,0,0,0,3,0,0,0,0]
regs=initial.copy(); path=(); trace=[]
for steps in range(10000):
    q=0; depth=0
    while True:
        if q==152:
            assert steps==64
            assert regs==[4,0,0,0,3,0,0,0,0]
            result={'source_DAG_sha256':hashlib.sha256(blob).hexdigest(),
                    'initial_registers':initial,'entry_node':152,
                    'nonterminal_leaves_before_first_nip':steps,
                    'entry_path_prefix':list(path[:depth]),
                    'entry_registers':regs,'cache':regs[5],'trace':trace}
            (here/'seed-zero-control.json').write_text(json.dumps(result,indent=2)+'\n')
            print(json.dumps({k:v for k,v in result.items() if k!='trace'}))
            raise SystemExit(0)
        edge=nodes[q][path[depth] if depth<len(path) else 0]
        depth+=1
        if edge.startswith('ENode '): q=int(edge.split()[1])
        else: break
    consumed=(path+(0,)*depth)[:depth]
    trace.append({'step':steps,'edge':edge,'consumed_path':list(consumed),
                  'registers':regs.copy()})
    if edge=='EHalt': raise AssertionError('Unexpected halt before NIP')
    kind,param=edge.split(); param=int(param)
    if kind=='EInc':
        regs[param]+=1; path=m.inc_path(consumed)
    elif kind=='EDecnz':
        if regs[param]: regs[param]-=1; path=m.inc_path(consumed)
        else: path=m.break_path(1,consumed)
    elif kind=='EBreak': path=m.break_path(param,consumed)
    elif kind=='EContinue': path=m.continue_path(param,consumed)
    else: raise AssertionError(edge)
raise AssertionError('Finite control step limit exceeded')
