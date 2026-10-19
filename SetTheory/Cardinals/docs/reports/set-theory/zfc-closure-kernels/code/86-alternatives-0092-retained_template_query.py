#!/usr/bin/env python3
"""133-state literal retained-path template query.

The source field list contains four rule bits followed by a complete leaf path.
Reverse copier restores source and produces a raw reversed query; a mirrored
selector and oracle run directly on it. One entry/return; no external root choice.
This is still a query component, not the proof enumerator or arena verifier.
"""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import json,hashlib
import pattern_oracle as O
import reverse_path_copy as C


def compile_query():
    ct,cs,cr,ci=C.compile_copy();_,_,ts=O.load_source();o=O.compile_oracle(ts)
    off=cr;selector=off+o['halt']
    prefixes=['']+[format(i,f'0{d}b') for d in (1,2,3) for i in range(2**d) if i<<(4-d)<12]
    ids={p:selector+i for i,p in enumerate(prefixes)};ret=selector+len(prefixes)
    table={k:(w,d,ids[''] if q==cr else q) for k,(w,d,q) in ct.items()}
    table.update({(q+off,b):(w,'L',ret if q2==o['halt'] else q2+off) for (q,b),(w,d,q2) in o['table'].items()})
    for prefix,q in ids.items():
        for b in range(2):
            p=prefix+str(b)
            if int(p,2)<<(4-len(p))>=12:target=ci['reject']
            elif len(p)==4:target=off+o['roots'][int(p,2)] if int(p,2) in o['roots'] else ci['reject']
            else:target=ids[p]
            table[q,b]=(b,'L',target)
    assert len(table)==2*ret and ret==133
    return table,cs,ret,o


def main():
    t,s,ret,o=compile_query();tests=0;maxsteps=0
    for rule in o['roots']:
        for path,expected,leaf in O.enumerate_leaf_paths(o,rule):
            bits=list(map(int,format(rule,'04b')))+path
            for extra in (2,7,20):
                initial,cursor,anchor,end,_=C.frame(bits,len(bits)+extra)
                initial[-10]=1;initial[end+7]=1
                want=dict(initial);want[cursor]=1
                for j,b in enumerate(reversed(bits)):
                    if b:want[j]=b
                    else:want.pop(j,None)
                want[len(bits)]=1
                word=expected+list(map(int,format(leaf,'03b')))
                for j,b in enumerate(word):
                    p=len(path)-1-j
                    if b:want[p]=b
                    else:want.pop(p,None)
                actual,h,steps=C.run(t,s,ret,initial,cursor)
                assert actual==want and h==-4
                tests+=1;maxsteps=max(maxsteps,steps)
    p=Path(__file__).parent/f'retained_template_query_{ret}.tm';O.save_table(p,t,ret,s)
    rule=3;path,_,_=next(O.enumerate_leaf_paths(o,rule));bits=list(map(int,format(rule,'04b')))+path
    initial,cursor,anchor,end,_=C.frame(bits,len(bits)+2)
    # Whole frame through cursor-1; cursor is already the required erased0.
    # Writing L->R leaves the head exactly at cursor, no uncharged adapter.
    bh=ret+cursor;bt={k:(w,d,bh if q==ret else q) for k,(w,d,q) in t.items()}
    for j in range(cursor):
        for b in range(2):bt[ret+j,b]=(initial.get(j,0),'R',s if j+1==cursor else ret+j+1)
    actual,h,steps=C.run(bt,ret,bh,{},0);want,wh,ws=C.run(t,s,ret,initial,cursor)
    assert actual==want and h==wh and steps==cursor+ws
    bp=p.parent/f'blank_retained_query_probe_{bh}.tm';O.save_table(bp,bt,bh,ret)
    result={'scope':'Single-entry retained-path template query, not proof verifier or consistency machine',
      'working_states':ret,'components':{'copier_operational':18,'shared_reject':1,'mirrored_oracle':102,'mirrored_selector':12},
      'tests':tests,'max_steps':maxsteps,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
      'blank_probe':{'working_states':bh,'initializer_states':cursor,'steps':steps,'purpose':'Always-halting component demo'},
      'blank_sha256':hashlib.sha256(bp.read_bytes()).hexdigest()}
    (p.parent/'retained_template_query_results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
