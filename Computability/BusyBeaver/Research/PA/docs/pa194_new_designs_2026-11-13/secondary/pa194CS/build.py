#!/usr/bin/env python3
"""Build the symmetric-guard cached-head candidate PA194CS.

This changes the Shift source, omits restoring scratchX to cacheH, and
uses symmetry of the existing H=X guard. It then folds native41 into330.
"""
from pathlib import Path
import hashlib,json
import compiler as c
import baseline_tools as b
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'machine'
if not __debug__:raise RuntimeError('Assertions required.')

def sha(data):return hashlib.sha256(data).hexdigest()
def js(p,obj):p.write_text(json.dumps(obj,indent=2)+'\n')

def main():
    OUT.mkdir(exist_ok=True)
    original=c.raw_nodes
    def nodes():
        ns=original();ns['node163']=('node6','node147')
        ns['node170']=(('node36',('node167','node145')),'node56')
        ns['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
        return ns
    c.raw_nodes=nodes
    inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    basepath=ROOT/'inputs/pa194C.native.tm'
    assert sha(basepath.read_bytes())=='b35d80b01ce9c2e95c8b29222881f40928247cdeffac322e4643f4f6694cd33c'
    raw=b.read_table(basepath)
    raw.update({(214,1):(1,True,30),(310,1):(1,True,330),
                (330,0):(0,True,63),(330,1):(1,False,73)})
    assert len(raw)==390
    fold=[[41,330,[[0,False,31],[1,False,46]]]]
    child,aliases=b.apply_folds(raw,fold)
    local=b.check_local_folds(raw,child,aliases,fold)
    t=c.read_grammar(ROOT/'inputs/pa194.grammar.json');sites,ins,cs=c.source(t)
    assert len(sites)==3646 and len(cs)==4745
    old=json.loads((ROOT/'inputs/195C.instructions.json').read_text())
    normalized=json.loads(json.dumps(ins))
    assert normalized[:3644]==old[:3644]
    assert normalized[3644:]==[['inc',5,3645],['jump',0]]
    assert old[3644:]==[['dec',6,3647,3645],['inc',5,3646],['jump',3644],['inc',6,3648],['jump',0]]
    incoming=[]
    for i,code in enumerate(old[:3644]):
        targets=code[2:] if code[0] in ('inc','dec') else code[1:] if code[0]=='jump' else []
        incoming.extend((i,target) for target in targets if target>=3644)
    assert incoming==[(3640,3644)]
    valid=c.validate(child,cs);assert valid['ok'],valid
    raw_valid=c.validate(raw,cs);assert raw_valid['ok'],raw_valid
    seed=b.startup(child,sites[25][0]);rawseed=b.startup(raw,sites[25][0])
    dense,labels=b.dense_table(child,194)
    native=b.table_text(child).encode();dense_bytes=b.table_text(dense).encode()
    (OUT/'pa194CS.native.tm').write_bytes(native)
    (OUT/'pa194CS.tm').write_bytes(dense_bytes)
    (OUT/'unfolded195CS.native.tm').write_text(b.table_text(raw))
    js(OUT/'pa194CS.labels.json',labels)
    js(OUT/'pa194CS.sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites])
    js(OUT/'pa194CS.instructions.json',ins)
    js(OUT/'additional_fold.json',fold);js(OUT/'additional_fold_cases.json',local)
    receipt={'family':'PA194CS','working_states':194,'transition_rows':388,'source_sites':3646,
      'source_contracts':4745,'source_change_bound_exactly':True,'additional_fold':fold,
      'additional_local_cases':len(local['cases']),'local_maximum_duration':max(x['duration']for x in local['cases']),
      'symbolic_validation':valid,'raw_symbolic_validation':raw_valid,'startup':seed,'raw_startup':rawseed,
      'native_sha256':sha(native),'dense_sha256':sha(dense_bytes),'kernel_checked':False}
    js(OUT/'construction_receipt.json',receipt)
    print(json.dumps(receipt,indent=2),flush=True)
if __name__=='__main__':main()
