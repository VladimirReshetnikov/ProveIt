#!/usr/bin/env python3
"""Replay the rejected padding allocation; never releases a machine table."""
from pathlib import Path
import json,hashlib
import construction as C
c=C.c
HERE=Path(__file__).resolve().parent
P=HERE/'padded_gate'
DEC=lambda r:('leaf','dec',r)
INC=lambda r:('leaf','inc',r)
CC=lambda r:('leaf','continueTo',r)
newraw={
    'getA':(DEC(3),(INC(1),CC(2))),
    'putA':(DEC(1),(INC(3),CC(2))),
    'clearA':(DEC(3),CC(1)),
    'clearD':(DEC(4),CC(1)),
    'clearH':(DEC(5),CC(1)),
}
base_raw=c.raw_nodes
def raw_nodes():
    d=base_raw();d.update(newraw);return d
c.raw_nodes=raw_nodes
c.MACROS.update({DEC(1):41,DEC(3):17,DEC(4):144,DEC(5):45,INC(3):161,'node69':179})

def build(t):
    old,_=c.machine();rows={(q,b):a for(q,b),a in old.items()if q<1300}
    raw=c.raw_nodes();index={};shape={}
    def state(t):
        if t in c.MACROS:return c.MACROS[t]
        if isinstance(t,str):return state(raw[t])
        if t in index:return index[t]
        if not c.isnode(t):raise ValueError(t)
        q=2000+len(index);index[t]=q;shape[q]=t
        for b,ch in enumerate(t):
            if ch==C.BREAK:act=(0,False,302)
            elif ch==CC(1):act=(0,False,1)
            elif ch==CC(2):act=(0,False,10)
            else:act=(b,True,state(ch))
            rows[q,b]=act
        return q
    root=state(t);rows[101,1]=(1,True,root)
    return rows,shape

def main():
    from verify import pin_check,require
    pin_check()
    expected=json.loads((P/'rejection.json').read_text())
    t=c.read_grammar(P/'grammar.json');raw,shape=build(t)
    chosen=json.loads((P/'folds.json').read_text());rows,alias=C.fold(raw,chosen)
    # The declared blank start is native label 74, not native label 0.
    seen={74};todo=[74]
    while todo:
        q=todo.pop()
        for b in(0,1):
            if(q,b)in rows:
                n=rows[q,b][2]
                if n not in seen:seen.add(n);todo.append(n)
    rows={qb:act for qb,act in rows.items()if qb[0]in seen}
    serial=''.join(f'{q} {b} {w} {"R"if d else"L"} {n}\n'for(q,b),(w,d,n)in sorted(rows.items()))
    require(hashlib.sha256(serial.encode()).hexdigest()==expected['native_table_sha256'],'rejected allocation hash')
    require(len(rows)//2==210 and len(shape)==87 and len(chosen)==7,'allocation census')
    sites,ins,contracts=c.source(t)
    require(len(sites)==3812,'source census')
    check=c.validate(rows,contracts)
    require(json.loads(json.dumps(check))=={'ok':False,'failed':[2413,None],'completed':3138},'expected failure changed')
    print(json.dumps({'status':'EXPECTED_REJECTION','working_states_before_validation':210,'source_sites':3812,'runtime':check,'logical_completeness':False,'literal_table_released':False},indent=2))
if __name__=='__main__':main()
