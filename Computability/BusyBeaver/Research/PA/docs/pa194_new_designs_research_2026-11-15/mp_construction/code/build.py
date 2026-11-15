#!/usr/bin/env python3
"""Reconstruct the exact PA194AX11HMP table, source, folds and blank startup."""
from pathlib import Path
import hashlib,json
from source import resolve
import support
ROOT=Path(__file__).resolve().parents[1]
R=ROOT/'reference'; C=ROOT/'candidate'; V=ROOT/'verification'
def sha(data):return hashlib.sha256(data).hexdigest()
def save(path,data):path.write_text(json.dumps(data,indent=2)+'\n')
def main():
    assert __debug__
    m=json.loads((R/'manifest.json').read_text())
    for item in m['files']+m['calibration_fragments']:
        assert sha((ROOT/item['path']).read_bytes())==item['sha256'],item['path']
    n=json.loads((R/'nodes.json').read_text());g=json.loads((R/'grammar.json').read_text())
    old_sites,old_ins=resolve(n,g)
    assert old_sites==json.loads((R/'sites.json').read_text())
    assert old_ins==json.loads((R/'instructions.json').read_text())
    assert n['node164']==['node162','node163']
    assert n['node162']==['node75','node37'] and n['node163']==['node6','node54']
    n['node164']=['node75',['node37',['node6','node54']]]
    sites,ins=resolve(n,g)
    assert len(sites)==3671 and ins==old_ins
    changed=[i for i,(a,b)in enumerate(zip(old_sites,sites))if a!=b]
    assert changed==list(range(3572,3659))
    C.mkdir(exist_ok=True);V.mkdir(exist_ok=True)
    for name,data in [('nodes.json',n),('grammar.json',g),('sites.json',sites),('instructions.json',ins)]:save(C/name,data)
    assert (C/'instructions.json').read_bytes()==(R/'instructions.json').read_bytes()
    raw_parent=support.read_table(R/'raw.native.tm');folds=json.loads((R/'folds.json').read_text())
    parent,_=support.apply_folds(raw_parent,folds)
    assert support.table_text(parent).encode()==(R/'machine.native.tm').read_bytes()
    dense_parent,_=support.dense_table(parent)
    assert support.table_text(dense_parent).encode()==(R/'machine.tm').read_bytes()
    raw=raw_parent.copy();edits={(100,0):213,(100,1):174,(174,0):28,(174,1):164}
    for key,target in edits.items():
        w,d,_=raw[key];raw[key]=w,d,target
    child,aliases=support.apply_folds(raw,folds)
    local=support.check_local_folds(raw,child,aliases,folds)
    dense,labels=support.dense_table(child)
    delta=[key for key in sorted(parent)if parent[key]!=child[key]]
    assert delta==sorted(edits)
    for name,rows in [('raw.native.tm',raw),('machine.native.tm',child),('machine.tm',dense)]:
        (C/name).write_text(support.table_text(rows))
    for name,data in [('folds.json',folds),('local_folds.json',local),('labels.json',labels)]:save(C/name,data)
    sa=support.startup(parent,tuple(map(int,old_sites[25][0])))
    sb=support.startup(child,tuple(map(int,sites[25][0])))
    assert sa['steps']==57922 and sb['steps']==58066
    save(C/'startup.json',sb);save(V/'parent_startup.json',sa)
    native=sha((C/'machine.native.tm').read_bytes());canonical=sha((C/'machine.tm').read_bytes())
    assert native=='e8e22523ae12c9b3ee1fe33a0b1697602584f58bfdf55b88b7a7f3c6e7ea9dfd'
    assert canonical=='b634f75f4969a68513c5460a2e6bf8fd9bb0a72ab1f3dd03ec88b348ce2c6272'
    result={'status':'PASS','name':'PA194AX11HMP','working_states':194,'transition_rows':388,
      'parent_native_sha256':sha((R/'machine.native.tm').read_bytes()),'native_sha256':native,'canonical_sha256':canonical,
      'raw_native_sha256':sha((C/'raw.native.tm').read_bytes()),'source_sites':3671,
      'changed_source_addresses':changed,'source_opcode_and_guarded_successor_identity':True,
      'instructions_sha256':sha((C/'instructions.json').read_bytes()),'sites_sha256':sha((C/'sites.json').read_bytes()),
      'changed_native_rows':[{'state':q,'read':b,'old':list(parent[q,b]),'new':list(child[q,b])}for q,b in delta],
      'direction_encoding':{'false':'L','true':'R'},'simultaneously_checked_folds':len(folds),'local_fold_cases':len(local['cases']),
      'parent_startup_steps':57922,'startup_steps':58066,'source_initial_site':25,
      'scope':'Exact finite reconstruction, source identity, simultaneous local folds and complete blank startup. Separate direct-runtime replay and relative mathematical iPRA proof establish unbounded simulation and calibration transfer.'}
    save(V/'build.json',result)
    print(json.dumps({k:v for k,v in result.items()if k not in('changed_source_addresses','changed_native_rows')},indent=2))
if __name__=='__main__':main()
