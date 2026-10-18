#!/usr/bin/env python3
"""Diagnose and repair contextual entry sharing after the 201-node rewrite."""
import json
import compile201 as cc
import compile_rebracket as c

def build():
    n,r,t=cc.build()
    d=json.loads((c.HERE.parent/'sources/beyond252/beyond252/exploratory/historical/decoder_entries.json').read_text())
    entry={int(q):max(v,key=v.get) for q,v in d['state_entries'].items()}
    t['218',0]=(0,'R','105')
    t['208',0]=(0,'R','23');t['208',1]=(1,'R','70')
    t['237',0]=(0,'R','208')
    t['243',0]=(0,'R',entry[43]);t['243',1]=(1,'R','218')
    return n,r,t

if __name__=='__main__':
    n,r,t=build();out=c.check(t,n,r)
    print(json.dumps(out,indent=2))
    (c.HERE/'repaired201_result.json').write_text(json.dumps(out,indent=2)+'\n')
    (c.HERE/'repaired201.tm').write_text('#! start 95\n'+''.join(f'{q} {b} {w} {m} {s}\n' for (q,b),(w,m,s) in sorted(t.items(),key=lambda kv:(int(kv[0][0]),kv[0][1]))))
