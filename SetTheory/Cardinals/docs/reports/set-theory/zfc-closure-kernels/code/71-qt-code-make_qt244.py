#!/usr/bin/env python3
"""Construct QT244 from the pinned routing245 certificate.

Example (from an extracted contribution):
  python code/make_qt244.py --reference reference/routing245 --output certificate

This constructor checks exact table/tree identities and an independent sparse
and dense blank run. Universal runtime and source equivalence are discharged by
separate checkers; this file never infers them from the finite bootstrap.
"""
from pathlib import Path
from hashlib import sha256
import argparse,json,sys

OLD_TABLE_SHA='f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267'
OLD_SITES_SHA='f77a3fb9729382a0b8cd24d480639862b63ecb76bbc205542d1fc7077c025745'
NEW_TABLE_SHA='0160caaf5d6db52eb7eb97a76cb04db4b424eb2bc0d58617818a6c7c6a1fe776'
CANONICAL_SHA='91ff0ff2dfe9155548d21405615934b46784c5e3cb850bbf056682d02b203790'
NEW_SITES_SHA='3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4'

def dump(path,obj):
    path.write_text(json.dumps(obj,indent=2)+'\n',encoding='ascii')

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

def main():
    if not __debug__:
        raise RuntimeError('Assertions are required; do not use Python -O.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--boot-limit',type=int,default=3000000)
    a=parser.parse_args();assert __debug__
    reference=a.reference.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
    sys.path.insert(0,str(reference/'code'))
    import build_routing_machine as B
    oldtable=reference/'certificate/machine_old.tm'
    oldsites=reference/'certificate/sites_logical.json'
    assert digest(oldtable)==OLD_TABLE_SHA
    assert digest(oldsites)==OLD_SITES_SHA
    T,start=B.rebuild.read_table(oldtable)
    assert start==95 and len(T)==490
    assert [k for k,v in T.items()if v[2]==26]==[(17,1)]
    assert [k for k,v in T.items()if v[2]==17]==[(12,0)]
    assert T[12,0]==(0,'R',17) and T[12,1]==(1,'R',18)
    assert T[17,0]==(0,'R',25) and T[17,1]==(1,'R',26)
    assert T[26,0]==(0,'R',18) and T[26,1]==(0,'L',20)
    T[12,0]=(0,'R',18)
    T[12,1]=(1,'R',17)
    T[17,1]=(0,'L',20)
    del T[26,0],T[26,1]
    states={q for q,b in T}
    assert len(states)==244 and len(T)==488
    assert set(T)=={(q,b)for q in states for b in (0,1)}
    assert {q for w,d,q in T.values()}-states=={254}
    (out/'machine_old.tm').write_text(B.rebuild.encode(T,95),encoding='ascii')
    assert digest(out/'machine_old.tm')==NEW_TABLE_SHA
    order=[95]+sorted(states-{95})
    mapping={q:i for i,q in enumerate(order)}|{254:244}
    canon={(mapping[q],b):(w,d,mapping[t])for(q,b),(w,d,t)in T.items()}
    (out/'machine.tm').write_text(B.rebuild.encode(canon,0),encoding='ascii')
    assert digest(out/'machine.tm')==CANONICAL_SHA
    dump(out/'renumbering.json',{'old_to_canonical':mapping,'canonical_to_old':order})
    sites=json.loads(oldsites.read_text());prefix='011'
    old=[[prefix+'00','CD',6],[prefix+'010','CI',0],
         [prefix+'011','CC',2],[prefix+'1','CI',0]]
    assert [s for s in sites if s[0].startswith(prefix)]==old
    new=[s for s in sites if not s[0].startswith(prefix)]+[
         [prefix+'0','CI',0],[prefix+'10','CD',6],[prefix+'11','CC',2]]
    new.sort(key=lambda s:s[0]);assert len(new)==6459
    dump(out/'sites_logical.json',new)
    assert digest(out/'sites_logical.json')==NEW_SITES_SHA
    phys=[(p,op,B.rebuild.PHYSICAL[r]if op in('CI','CD')else r)for p,op,r in new]
    dump(out/'sites_physical.json',phys)
    meta={
        'status':'TABLE_AND_SOURCE_IDENTITIES_ONLY',
        'states':len(states),'binary_rows':len(T),
        'cases':sum(2 if op=='CD'else 1 for p,op,r in new),
        'source_leaves':len(new),'maximum_depth':max(len(p)for p,op,r in new),
        'old_subtree':old,'new_subtree':[s for s in new if s[0].startswith(prefix)],
        'changed_retained_rows':[[12,0,0,'R',18],[12,1,1,'R',17],[17,1,0,'L',20]],
        'deleted_state':26,'unchanged_retained_rows':len(T)-3,
        'source_rewrite':'while X>0: X--; N++; then N++ becomes do N++; while X-- succeeds',
        'old_table_sha256':OLD_TABLE_SHA,'old_sites_sha256':OLD_SITES_SHA,
        'table_sha256':NEW_TABLE_SHA,'canonical_sha256':CANONICAL_SHA,
        'new_sites_sha256':NEW_SITES_SHA,
        'scope_note':'Source equivalence and universal source/TM correspondence require separate checks.'}
    dump(out/'construction.json',meta);print(json.dumps(meta,indent=2),flush=True)
    boot=B.sparse_boot(T,limit=a.boot_limit,minimum_gap=64)
    dump(out/'boot.json',boot)
    assert boot['status']=='PASS',boot
    assert boot['blank_steps']==407931 and boot['head']==-5
    assert boot['header']==176 and boot['header_distance']==181
    assert boot['logical_registers']==[3,0,0,0,3,0,0,0,0]
    assert boot['spare_values']==[1]*167 and boot['one_count']==351
    print(json.dumps({k:v for k,v in boot.items()if k not in(
        'all_one_positions','used_rows','spare_values')},indent=2),flush=True)

if __name__=='__main__':
    main()
