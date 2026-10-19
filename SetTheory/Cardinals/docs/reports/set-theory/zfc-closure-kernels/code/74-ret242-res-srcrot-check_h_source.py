#!/usr/bin/env python3
"""Check every source-context edge for the four shared H rotations."""
import json,sys
from pathlib import Path
from hashlib import sha256
BASE=Path(__file__).resolve().parent
REF=BASE/'support'
sys.path.insert(0,str(REF))
from check_source_244 import Program

def main():
    if not __debug__:
        raise RuntimeError('Assertions are required; do not use Python -O.')
    assert __debug__
    old_path=BASE/'sites_logical.json'
    new_path=BASE/'rotate_h/sites_logical.json'
    old=Program(json.loads(old_path.read_text()))
    new=Program(json.loads(new_path.read_text()))
    prefixes=json.loads((BASE/'rotate_h/construction.json').read_text())['prefixes']
    forbidden=set();mapping={};entries={};exit_maps=[]
    for p in prefixes:
        o=[old.leaves[p+s] for s in ['00','010','011','1']]
        n=[new.leaves[p+s] for s in ['0','10','11']]
        assert [old.sites[i][1:] for i in o]==[['CD',6],['CI',5],['CC',2],['CI',5]]
        assert [new.sites[i][1:] for i in n]==[['CI',5],['CD',6],['CC',2]]
        forbidden.update(o)
        mapping[o[0]]=n[0]
        entries[o[0]]=[]
        # These exact local successor equations establish the two induction
        # stages: X=0 exits after2 instructions; X>0 returns after3 with
        # H increased1 and X decreased1. Seven other registers are unchanged.
        assert old.successors(o[0])=={'zero':o[3],'positive':o[1]}
        assert old.successors(o[1])=={'inc':o[2]}
        assert old.successors(o[2])=={'control':o[0]}
        assert new.successors(n[0])=={'inc':n[1]}
        assert new.successors(n[1])['positive']==n[2]
        assert new.successors(n[2])=={'control':n[0]}
        exit_maps.append((old.successors(o[3])['inc'],new.successors(n[1])['zero']))
    for i,(p,k,a) in enumerate(old.sites):
        if i not in forbidden:
            assert new.sites[new.leaves[p]]==[p,k,a]
            mapping[i]=new.leaves[p]
    for o,n in exit_maps:assert mapping[o]==n
    edges=0
    for i,j in mapping.items():
        if i in forbidden:continue
        a,b=old.successors(i),new.successors(j)
        assert a.keys()==b.keys()
        for branch,target in a.items():
            assert target in mapping,('outside enters loop interior',i,branch,target)
            assert mapping[target]==b[branch]
            edges+=1
            if target in entries:entries[target].append([i,branch])
    assert mapping[old.site_at('')]==new.site_at('')
    old_halt=[i for i,(_,k,_) in enumerate(old.sites)if k=='CH']
    new_halt=[i for i,(_,k,_) in enumerate(new.sites)if k=='CH']
    assert [mapping[i] for i in old_halt]==new_halt
    r={'status':'PASS_SOURCE_CONTEXT_AND_UNBOUNDED_LOOP_INDUCTION_STAGES',
       'old_leaves':len(old.sites),'new_leaves':len(new.sites),
       'ordinary_context_edges':edges,'external_entries':entries,
       'loop_contract':'For all H=a,X=b in Nat, H becomes a+b+1; X becomes0; other7 registers unchanged. Exactly3b+2 source instructions. Proof by induction on b using checked zero/positive stages.',
       'old_sha256':sha256(old_path.read_bytes()).hexdigest(),
       'new_sha256':sha256(new_path.read_bytes()).hexdigest(),
       'no_external_interior_entry':True,'halt_site_map':list(zip(old_halt,new_halt)),
       'scope':'Ordinary source theorem; no additional working-state saving.'}
    (BASE/'rotate_h/source_context.json').write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(r,indent=2))
if __name__=='__main__':main()
