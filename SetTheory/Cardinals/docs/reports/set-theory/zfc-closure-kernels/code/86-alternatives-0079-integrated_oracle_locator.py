#!/usr/bin/env python3
"""134-state literal composition: rule selector -> oracle -> arena locator.

This executes the first native-tape stages of a path query. It does not yet
compare the actual arena path or implement the complete proof search. Inputs
must satisfy the validated-frame contract; rejection sink is NOT the intended
malformed-certificate behavior of the future fair enumerator.
"""
if not __debug__:
    raise RuntimeError('Assertions must be enabled; do not use python -O.')
from pathlib import Path
import hashlib,json,itertools
import pattern_oracle as O
import unary_locator as L


def compile_pipeline():
    C,P,templates=O.load_source();o=O.compile_oracle(templates);loc=L.compile_locator()
    n=o['halt'];ln=L.RETURN;seek0=n+ln;seek1=seek0+1
    # Exactly the full 0..11 four-bit rule-selector prefix trie. 0/1/2 targets
    # are reserved for future truth/MP/GEN handlers and currently hit reject.
    prefixes=['']+[format(i,f'0{d}b') for d in (1,2,3) for i in range(2**d)
                      if i<<(4-d)<12]
    assert len(prefixes)==12
    ids={p:seek1+1+i for i,p in enumerate(prefixes)}
    done=seek1+1+len(ids);reject=n+L.IDS['reject']
    table={key:(w,d,seek0 if q==o['halt'] else q) for key,(w,d,q) in o['table'].items()}
    table.update({(q+n,b):(w,d,done if q2==L.RETURN else q2+n)
                  for (q,b),(w,d,q2) in loc.items()})
    table[seek0,0]=(0,'R',seek0);table[seek0,1]=(1,'R',seek1)
    table[seek1,1]=(1,'R',seek1);table[seek1,0]=(0,'L',n+L.IDS['counter'])
    for prefix,q in ids.items():
        for b in range(2):
            p=prefix+str(b)
            if int(p,2)<<(4-len(p))>=12:target=reject
            elif len(p)==4:target=o['roots'].get(int(p,2),reject)
            else:target=ids[p]
            table[q,b]=(b,'R',target)
    assert len(table)==2*done and done==134
    return table,ids[''],done,o


def make_frame(rule,path,i,records,gap=4):
    assert len(path)<=23
    local,starts=L.frame(i,records,gap)
    offset=32+i
    tape={p+offset:b for p,b in local.items()}
    prefix=list(map(int,format(rule,'04b')))+path+[0]*(28-len(path))
    for p,b in enumerate(prefix):
        if b:tape[p]=b
        else:tape.pop(p,None)
    return tape,[x+offset for x in starts],offset


def run(table,start,done,tape,limit=2000000):
    tape=dict(tape);q=start;head=0;steps=0
    while q!=done:
        if steps>=limit:raise RuntimeError('fuel exhausted')
        w,d,q=table[q,tape.get(head,0)]
        if w:tape[head]=w
        else:tape.pop(head,None)
        head+=1 if d=='R' else -1;steps+=1
    return tape,head,steps


def add_blank_initializer(table,start,done,bits):
    # Write finite exact prepared frame right to left, then one R adapter.
    # Translation of all tape coordinates is harmless; every state is charged.
    n=done;newdone=n+len(bits)+1
    out={k:(w,d,newdone if q==done else q) for k,(w,d,q) in table.items()}
    for j,b in enumerate(reversed(bits)):
        q=n+j;target=q+1
        for read in range(2):out[q,read]=(b,'L',target)
    adapter=n+len(bits)
    for read in range(2):out[adapter,read]=(read,'R',start)
    return out,n,newdone


def main():
    table,start,done,o=compile_pipeline();count=0;maxsteps=0
    records=[(0,0,0),(1,0,0),(2,0,1),(3,2,2),(0,1,3)]
    for rule in o['roots']:
        for path,expected,leaf in O.enumerate_leaf_paths(o,rule):
            for i in range(len(records)):
                initial,starts,offset=make_frame(rule,path,i,records)
                actual,head,steps=run(table,start,done,initial)
                want=dict(initial)
                output=expected+list(map(int,format(leaf,'03b')))
                for j,b in enumerate(output):
                    if b:want[4+j]=b
                    else:want.pop(4+j,None)
                want[starts[0]]=1;want.pop(starts[i],None)
                for p in range(33,offset+1):want.pop(p,None)
                assert actual==want,(rule,path,i,actual,want)
                assert head==starts[i]+1
                count+=1;maxsteps=max(maxsteps,steps)
    path=Path(__file__).parent/'oracle_locator_pipeline_134.tm'
    O.save_table(path,table,done,start)
    # Fully charged blank probe uses rule3, its first leaf, three arena records.
    p,_,_=next(O.enumerate_leaf_paths(o,3));initial,starts,offset=make_frame(3,p,2,records[:3])
    bits=[initial.get(i,0) for i in range(max(initial)+1)]
    bt,bs,bh=add_blank_initializer(table,start,done,bits)
    actual,h,steps=run(bt,bs,bh,{})
    want,wh,ws=run(table,start,done,initial)
    shift=1-len(bits)
    assert actual=={p+shift:v for p,v in want.items()}
    assert h==wh+shift and steps==len(bits)+1+ws
    blankpath=Path(__file__).parent/f'blank_pipeline_probe_{bh}.tm'
    O.save_table(blankpath,bt,bh,bs)
    result={'scope':'Prepared-frame composition of root selector, destructive oracle query and first arena lookup; not a proof verifier or consistency machine.',
      'states':{'template_constructor':91,'leaf_emitter':11,'locator_operational':17,
                'totalizing_nonhalting_reject':1,'query_to_counter_seek':2,'rule_selector':12},
      'working_states':done,'transition_rows':len(table),'start':start,'separate_return':done,
      'tests':count,'max_steps':maxsteps,'remaining_budget_for_strict_sub246':245-done,
      'blank_probe':{'file':blankpath.name,'working_states':bh,'initializer_states':len(bits)+1,
                     'prepared_bits':len(bits),'blank_steps':steps,'purpose':'Always-halting component demo only'},
      'table_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
      'blank_probe_sha256':hashlib.sha256(blankpath.read_bytes()).hexdigest()}
    (Path(__file__).parent/'integrated_pipeline_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
