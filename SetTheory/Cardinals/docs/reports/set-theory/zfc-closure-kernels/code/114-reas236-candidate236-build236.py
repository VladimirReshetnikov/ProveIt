#!/usr/bin/env python3
"""Rebuild the complete 236-state candidate from the pinned 237-state table.

This is a literal table construction. Source semantic equivalence is supplied
by the separately checked single closed-chunk reassociation certificate.
"""
from pathlib import Path
import hashlib,json
import sys
if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Run without -O/-OO: verification assertions are required.')

HERE=Path(__file__).resolve().parent
PIN='a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a'

def read(path):
    data=path.read_bytes();table={}
    for line in data.decode().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();key=int(q),int(b)
        assert key not in table
        table[key]=int(w),d,int(z)
    return table,data

def serialize(t):
    return '#! start 95\n'+''.join(f'{q} {b} {w} {d} {z}\n' for (q,b),(w,d,z) in sorted(t.items()))

def main():
    old,data=read(HERE/'ingredients/composed237_old.tm')
    assert hashlib.sha256(data).hexdigest()==PIN
    t=dict(old)
    edits={(177,0):(0,'R',185),(177,1):(1,'R',212),
           (185,0):(0,'R',165),(185,1):(1,'R',192)}
    t.update(edits)
    middle=serialize(t)
    assert middle==(HERE/'ingredients/reassociated237_old.tm').read_text()
    t={k:(w,d,182 if z==223 else z) for k,(w,d,z) in t.items() if k[0]!=223}
    t[182,0]=(0,'L',198);t[182,1]=(1,'L',210)
    states=sorted({q for q,b in t});assert len(states)==236 and len(t)==472
    assert all(z in states or z==254 for w,d,z in t.values())
    inherited=serialize(t)
    order=[95]+[q for q in states if q!=95];mp={q:i for i,q in enumerate(order)};mp[254]=236
    canonical='#! start 0\n'+''.join(f'{mp[q]} {b} {w} {d} {mp[z]}\n'
                                   for q in order for b in (0,1) for w,d,z in [t[q,b]])
    assert inherited==(HERE/'zfc_reassociate236_old.tm').read_text()
    assert canonical==(HERE/'zfc_reassociate236.tm').read_text()
    result={'status':'LITERAL_BUILD_PASS','input_states':237,'output_states':236,
            'deleted_states':[223],'retained_row_changes':sum(t[k]!=old[k] for k in t),
            'retained_rows_unchanged':sum(t[k]==old[k] for k in t),
            'input_sha256':PIN,'intermediate_sha256':hashlib.sha256(middle.encode()).hexdigest(),
            'output_inherited_sha256':hashlib.sha256(inherited.encode()).hexdigest(),
            'output_canonical_sha256':hashlib.sha256(canonical.encode()).hexdigest(),
            'canonical_start':0,'canonical_dispatcher':mp[96],'canonical_halt':236}
    (HERE/'build_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
