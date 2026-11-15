#!/usr/bin/env python3
"""Action-preserving control partition refinement of every spanning194 table.

The input symbol may vary freely at each transition. A nontrivial stable
partition yields an unconditional same-tape state quotient. Its absence is
not a lower bound against context-dependent quotients or different encodings.
"""
from pathlib import Path
import hashlib,importlib.util,json
HERE=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('current_census',HERE/'rebuild_current_census.py')
c=importlib.util.module_from_spec(s);s.loader.exec_module(c)
out=[]
for r in json.loads((HERE/'current/classes194.json').read_text()):
    if not r['spanning']:continue
    b=(HERE/'current'/r['local_representative']).read_bytes();rows,states,halt=c.ji.lib.parse_table(b)
    block={q:0 for q in states};iterations=0
    while True:
        groups={};new={}
        for q in sorted(states):
            signature=tuple((w,d,block[t] if t in states else -1) for w,d,t in (rows[q,0],rows[q,1]))
            if signature not in groups:groups[signature]=len(groups)
            new[q]=groups[signature]
        iterations+=1
        if new==block:break
        block=new
    parts={}
    for q,k in block.items():parts.setdefault(k,[]).append(q)
    out.append({'table_class':r['table_class'],'states':len(states),'blocks':len(parts),'iterations':iterations,'nontrivial_blocks':[v for v in parts.values() if len(v)>1]})
result={'scope':__doc__,'tables':len(out),'all_singleton':all(r['states']==r['blocks'] for r in out),'results':out}
(HERE/'current/control_bisimulation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='results'},indent=2))
