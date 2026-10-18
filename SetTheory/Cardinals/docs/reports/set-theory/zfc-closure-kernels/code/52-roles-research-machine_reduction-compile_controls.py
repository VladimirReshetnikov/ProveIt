"""Emit complete charged comparison tables with the pinned existing Mira assembler.

These tables measure the code-sharing cost of register-role coalescing. They
are not sub252 candidates and have no newly kernel-checked ZFC endpoint.
"""
from pathlib import Path
from collections import deque
import sys,json,hashlib
ROOT=Path(__file__).parent
sys.path.insert(0,str(ROOT/'input'))
repo=Path(sys.argv[1]) if len(sys.argv)>1 else ROOT.parents[1]/'upstream/ProveIt'
sys.path.insert(0,str(repo/'Computability/BusyBeaver/Research/ZFC'))
import mira_backend as m

def convert(data):
    nodes={int(n):p for n,p in data['nodes'].items()};root=data['root'];root=root[1] if isinstance(root,(list,tuple)) else root
    ids={root:0};q=deque([root]);out={}
    kinds=dict(N='ENode',I='EInc',D='EDecnz',B='EBreak',C='EContinue',H='EHalt')
    while q:
        old=q.popleft();pair=[]
        for e in nodes[old]:
            k=e[0]
            if k=='N':
                if e[1] not in ids:ids[e[1]]=len(ids);q.append(e[1])
                pair.append(f'ENode {ids[e[1]]}')
            elif k=='H':pair.append('EHalt')
            else:pair.append(f'{kinds[k]} {e[1]}')
        out[ids[old]]=tuple(pair)
    return out

out=ROOT/'frozen';out.mkdir(exist_ok=True)
results=[]
inputs=[('original_control',ROOT/'input/27-variant-experiments-machine_search-grammar_search-decoder_entries.json'),('coalesced_control',ROOT/'allocated-dag-compacted.json')]
for label,path in inputs:
    source=convert(json.loads(path.read_text()))
    machine=m.compile_dag(source,initializer='compact')
    checked=machine.check_sites()
    boot=m.initial_configuration_check(machine)
    dest=out/(label+'.tm');machine.save(dest)
    record=dict(label=label,input_source=path.name,input_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),table=dest.name,evidence=machine.evidence,boot=boot)
    results.append(record)
    print(label,machine.evidence['working_states'],machine.evidence['states_by_role'],checked,boot,flush=True)
(out/'complete-table-controls.json').write_text(json.dumps(dict(status='complete charged controls, no new record or kernel endpoint',mira_backend_sha256=hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest(),results=results),indent=2))
