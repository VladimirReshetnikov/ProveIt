#!/usr/bin/env python3
"""Rebuild both final tables and verify arbitrary-register primitive contracts."""
from pathlib import Path
import json,hashlib
import build_composites as bc
from support import apply,localvalid
import verify_emitter
c=bc.c
HERE=Path(__file__).resolve().parent
def verify(family):
    p=HERE/family;t=c.read_grammar(p/'grammar.json');raw,_,shape=c.build(t)
    chosen=json.loads((p/'folds.json').read_text());rows,aliases=apply(raw,chosen)
    assert localvalid(raw,rows,aliases,chosen),'interacting folds fail'
    native=(p/'machine.native.tm').read_text();assert bc.table_text(rows)==native
    assert len(rows)==392
    labels=json.loads((p/'labels.json').read_text());assert len(labels)==197
    assert labels[0]==74 and labels[-1]==254 and len(set(labels))==197
    inverse={q:i for i,q in enumerate(labels)}
    dense=''.join(f'{inverse[q]} {b} {w} {"R" if d else "L"} {inverse[n]}\n'
        for q in labels[:-1] for b in (0,1) for w,d,n in [rows[q,b]])
    assert dense==(p/'machine.tm').read_text()
    seen={74};todo=[74]
    while todo:
        q=todo.pop()
        for b in (0,1):
            n=rows[q,b][2]
            if n!=254 and n not in seen:seen.add(n);todo.append(n)
    assert len(seen)==196
    sites,ins,contracts=c.source(t)
    serialized=[[''.join(map(str,path)),op,arg]for path,op,arg in sites]
    assert serialized==json.loads((p/'sites.json').read_text())
    result=c.validate(rows,contracts);assert result['ok']
    seed_steps=bc.startup(rows,sites[25][0]);assert seed_steps==57922
    old=json.loads((p/'receipt.json').read_text())
    assert old['validation']==result and old['source_sites']==len(sites)
    assert old['sha256']==hashlib.sha256(native.encode()).hexdigest()
    assert old['dense_sha256']==hashlib.sha256(dense.encode()).hexdigest()
    emitter=verify_emitter.audit(family)
    return dict(family=family,states=len(rows)//2,rows=len(rows),source_sites=len(sites),
        symbolic_runtime=result,blank_seed_steps=seed_steps,emitter=emitter,
        dense_sha256=old['dense_sha256'],native_sha256=old['sha256'],
        caveat='Executable checker using inherited arithmetic-engine contracts; not a new Lean endpoint.')
if __name__=='__main__':
    for family in ['diagonal196','separate196']:print(json.dumps(verify(family),indent=2),flush=True)
