#!/usr/bin/env python3
"""Replay finite contracts, blank startup, state count, and renumbering."""
from pathlib import Path
import json,hashlib
import symbolic_runtime as s
ROOT=Path(__file__).resolve().parent

def main():
    receipt=json.loads((ROOT/'receipt.json').read_text())
    for name,digest in receipt['hashes'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,('Hash mismatch',name)
    labels=json.loads((ROOT/'dense_labels.json').read_text())['dense_to_native']
    assert len(labels)==200 and len(set(labels))==200 and labels[0]==74 and labels[-1]==254
    dense={}
    for line in (ROOT/'machine.tm').read_text().splitlines():
        q,b,w,d,z=line.split();key=int(q),int(b)
        assert key not in dense
        dense[key]=(int(w),d,int(z))
    assert set(dense)=={(q,b) for q in range(199) for b in (0,1)}
    for (q,b),(w,d,z) in dense.items():
        assert w in (0,1) and d in ('L','R') and 0<=z<=199
        assert s.rows[labels[q],b]==(w,d,labels[z])
    box=json.loads((ROOT/'box_agreement.json').read_text())
    assert len(box['agreement_rows'])==42
    for q,b,w,d,z in box['agreement_rows']:
        assert s.rows[q,b]==(w,d,z)
    ok,details=s.validate(s.rows)
    assert ok,details
    target=json.loads((ROOT/'startup_target.json').read_text())
    tape={};q=74;pos=0
    for _ in range(target['steps']):
        b=tape.get(pos,0);w,d,q=s.rows[q,b];tape[pos]=w;pos+=1 if d=='R' else -1
    assert q==target['native_state'] and pos==target['head_position']
    assert {p for p,b in tape.items() if b}==set(target['one_positions'])
    print(json.dumps({'working_states':199,'transitions':398,'symbolic_contracts':details,'blank_startup_steps':target['steps'],'dense_native_conjugacy':True,'box_agreement_rows':42,'result':'PASS'},indent=2))

if __name__=='__main__':main()
