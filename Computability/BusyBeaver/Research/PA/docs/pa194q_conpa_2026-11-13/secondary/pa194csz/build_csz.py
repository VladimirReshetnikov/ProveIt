#!/usr/bin/env python3
"""Build PA194CSZ: symmetric Shift plus a proved zero-register decrement.

All inherited construction code remains attributed. The new operation is
an invariant-guarded physical realization of source jump26; this script
proves the common finite abstraction invariant and checks all outcomes.
"""
from pathlib import Path
import hashlib,json,time
import compiler as c
import baseline_tools as b
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'machine_csz'
START,HALT=74,254
if not __debug__:raise RuntimeError('Assertions required')
def sha(x):return hashlib.sha256(x).hexdigest()
def js(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def succ(code,pc,mask):
    z=code[pc]
    if z[0]=='jump':return [(z[1],mask)]
    if z[0]=='inc':return [(z[2],mask|(1<<z[1]))]
    if z[0]=='dec':
        bit=1<<z[1]
        return [(z[3],mask&~bit),(z[3],mask)] if mask&bit else [(z[2],mask)]
    assert z[0]=='halt';return []
def closure(code):
    seen={(25,1)};todo=list(seen)
    for pc,m in todo:
        for item in succ(code,pc,m):
            assert 0<=item[0]<len(code) and 0<=item[1]<512
            if item not in seen:seen.add(item);todo.append(item)
    assert all(item in seen for pc,m in seen for item in succ(code,pc,m))
    return seen

def main():
    started=time.monotonic();OUT.mkdir(exist_ok=True)
    original_machine,original_nodes=c.machine,c.raw_nodes
    edits={(38,0):(0,True,11),(38,1):(1,True,122),(164,1):(1,True,130),
           (214,0):(0,True,312),(214,1):(1,True,30),(312,0):(0,True,188),
           (310,1):(1,True,330),(330,0):(0,True,63),(330,1):(1,False,73),
           (27,1):(1,True,21)}
    def machine():
        rows,labels=original_machine();rows.update(edits);return rows,labels
    def nodes():
        ns=original_nodes();ns['node163']=('node6','node147')
        ns['node170']=(('node36',('node167','node145')),'node56')
        ns['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
        assert ns['node22']==(('leaf','dec',8),('leaf','breakTo',1))
        ns['node22']=(('leaf','dec',8),('leaf','dec',6))
        return ns
    c.machine,c.raw_nodes=machine,nodes
    inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    tree=c.read_grammar(ROOT/'inputs/pa194.grammar.json')
    raw,index,shape=c.build(tree);assert len(raw)==404 and len(shape)==67
    folds=json.loads((ROOT/'inputs/pa194.folds.json').read_text())+[[41,330,[[0,False,31],[1,False,46]]]]
    assert len(folds)==8
    child,aliases=b.apply_folds(raw,folds);local=b.check_local_folds(raw,child,aliases,folds)
    parent_bytes=(ROOT/'referenceCS/pa194CS.native.tm').read_bytes()
    assert sha(parent_bytes)=='00446d08d3c35909a11460a9e19507d53e8526ad822b94ce9a04c73951eb447b'
    parent=b.read_table(ROOT/'referenceCS/pa194CS.native.tm')
    assert {k for k in child if child[k]!=parent[k]}=={(27,1)}
    assert parent[27,1]==(0,False,40) and child[27,1]==(1,True,21)
    sites,cfg,contracts=c.source(tree)
    new=json.loads(json.dumps(cfg))
    parent_code=(ROOT/'referenceCS/pa194CS.instructions.json').read_bytes()
    assert sha(parent_code)=='e2f74c0fad95734738788b98e76dc3e11748c0819ad7ef2b2998f81e0140da87'
    old=json.loads(parent_code)
    parent_sites=(ROOT/'referenceCS/pa194CS.sites.json').read_bytes()
    assert sha(parent_sites)=='8a79e70d5e806312b62d3a1b251b09de92096dd58673f0c74589ec4f42ff5ccd'
    oldsites=json.loads(parent_sites)
    newsites=[[''.join(map(str,p)),op,a]for p,op,a in sites]
    assert len(new)==3646 and len(contracts)==4746
    assert len(old)==len(new) and [i for i in range(len(new)) if old[i]!=new[i]]==[26]
    assert old[26]==['jump',34] and new[26]==['dec',6,34,27]
    assert [i for i in range(len(newsites)) if oldsites[i]!=newsites[i]]==[26]
    assert newsites[26]==[oldsites[26][0],'dec',6]
    a,z=closure(old),closure(new);assert a==z
    assert all(succ(old,pc,m)==succ(new,pc,m)for pc,m in a)
    masks=sorted(m for pc,m in a if pc==26);assert masks and all(m&64==0 for m in masks)
    enc=(json.dumps(sorted(a),separators=(',',':'))+'\n').encode()
    (OUT/'positivity_pairs.json').write_bytes(enc)
    invariant={'inductive_pairs':len(a),'contains_seed':True,'all_abstract_successors_closed':True,
      'concrete_seed':[25,[2,0,0,0,0,0,0,0,0]],'site26_masks':masks,'R6_zero_at26':True,
      'shared_abstract_transitions_equal':True,'closure_sha256':sha(enc)}
    print('joint invariant PASS',len(a),'masks at26',len(masks),flush=True)
    valid=c.validate(child,contracts);assert valid['ok'],valid
    rawvalid=c.validate(raw,contracts);assert rawvalid['ok'],rawvalid
    seed=b.startup(child,sites[25][0]);rawseed=b.startup(raw,sites[25][0])
    dense,labels=b.dense_table(child,194)
    for name,tab in [('pa194CSZ.native.tm',child),('pa194CSZ.tm',dense),('unfolded202CSZ.native.tm',raw)]:
        (OUT/name).write_text(b.table_text(tab))
    js(OUT/'pa194CSZ.labels.json',labels);js(OUT/'pa194CSZ.instructions.json',new);js(OUT/'pa194CSZ.sites.json',newsites)
    js(OUT/'folds.json',folds);js(OUT/'local_fold_cases.json',local);js(OUT/'invariant.json',invariant)
    receipt={'family':'PA194CSZ','status':'PASS','working_states':194,'transition_rows':388,
      'fixed_controls':135,'raw_readers':67,'folds':8,'source_sites':len(sites),'source_contracts':len(contracts),
      'source_edit':{'site':26,'before':old[26],'after':new[26]},'native_edit':{'row':[27,1],'before':parent[27,1],'after':child[27,1]},
      'invariant':invariant,'symbolic_validation':valid,'raw_symbolic_validation':rawvalid,'startup':seed,'raw_startup':rawseed,
      'local_fold_cases':len(local['cases']),'maximum_local_duration':max(x['duration']for x in local['cases']),
      'native_sha256':sha((OUT/'pa194CSZ.native.tm').read_bytes()),'dense_sha256':sha((OUT/'pa194CSZ.tm').read_bytes()),
      'seconds':round(time.monotonic()-started,6),'kernel_checked':False}
    js(OUT/'construction_receipt.json',receipt);print(json.dumps(receipt,indent=2),flush=True)
if __name__=='__main__':main()
