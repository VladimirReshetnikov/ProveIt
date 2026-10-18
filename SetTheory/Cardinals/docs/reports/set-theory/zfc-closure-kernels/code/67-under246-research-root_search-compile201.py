#!/usr/bin/env python3
"""Experimental contextual integration of the certified 201-node source DAG."""
import json
from pathlib import Path
import compile_rebracket as c

def build():
    n,r,t=c.load();n=n.copy()
    d=json.loads((c.HERE.parent/'sources/beyond252/beyond252/exploratory/historical/decoder_entries.json').read_text())
    entry={int(q):max(v,key=v.get) for q,v in d['state_entries'].items()}
    new=203;entry[new]='256'
    patch={99:(('N',43),('N',new)),59:(('N',99),('I',1)),74:(('N',48),('N',63)),83:(('N',63),('N',new)),new:(('N',48),('N',79))}
    for q,pair in patch.items():
        n[q]=pair
        for b,e in enumerate(pair):
            target=entry[e[1]] if e[0]=='N' else '70'
            t[entry[q],b]=(b,'R',target)
    for q in (49,73,82):del n[q]
    # q243 remains the entry of old source node80.
    t={k:v for k,v in t.items() if k[0] not in ('98','208')}
    return n,r,t

if __name__=='__main__':
    n,r,t=build();result=c.check(t,n,r)
    print(json.dumps(result,indent=2))
    p=Path(__file__).resolve().parent
    (p/'rebracket201_first_result.json').write_text(json.dumps(result,indent=2)+'\n')
    (p/'rebracket201_minimal.json').write_text(json.dumps(dict(root=r,nodes=n),indent=2)+'\n')
    (p/'rebracket201_first.tm').write_text('#! start 95\n'+''.join(f'{q} {b} {w} {m} {s}\n' for (q,b),(w,m,s) in sorted(t.items(),key=lambda kv:(int(kv[0][0]),kv[0][1]))))
