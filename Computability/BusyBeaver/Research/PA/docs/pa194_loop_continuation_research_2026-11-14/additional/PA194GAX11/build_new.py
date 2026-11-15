"""Reconstruct PA194GAX11 and verify its complete source splice.

Adapted from the PA194G and PA194AX11 builders; see PROVENANCE.json and
licenses/. Uses local frozen inputs and Python's standard library only.
"""
from pathlib import Path
import json,sys,hashlib
ROOT=Path(__file__).resolve().parent
import compiler as c
import support
def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
def dump(path,obj):path.write_text(json.dumps(obj,indent=2)+'\n')
def grammar_json(t):
    names={};rules={}
    def go(t):
        if not c.isnode(t):return t
        if t in names:return names[t]
        name='g'+str(len(names));names[t]=name;rules[name]=list(map(go,t));return name
    return {'root':go(t),'rules':rules}
def main(full=True):
    raw_path=ROOT/'baseline.raw.native.tm'
    assert hashlib.sha256(raw_path.read_bytes()).hexdigest()=='b25933d14de19f72709bdecf7a67a4e21c150f525cf61ec76c074ac577d6cc87'
    raw0=support.read_table(raw_path)
    raw0[164,1]=(1,True,114)
    nodes={k:tup(v)for k,v in json.loads((ROOT/'nodes.json').read_text()).items()}
    assert nodes['node163']==('node6','node54')
    c.machine=lambda:(raw0,[]);c.raw_nodes=lambda:nodes
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    def normal(t):
        if t=='node60':return inc,inc
        if t=='node61':return (inc,inc),(inc,inc)
        return tuple(map(normal,t))if c.isnode(t)else t
    old=normal(c.read_grammar(ROOT/'grammar.json'))
    def replace(t):
        if t==c.BREAK:return 'node49'
        return tuple(map(replace,t))if c.isnode(t)else t
    new=replace(old)
    oldsites,oldins,_=c.source(old)
    raw,index,shape=c.build(new)
    folds=json.loads((ROOT/'folds.json').read_text())
    rows,aliases=support.apply_folds(raw,folds)
    local=support.check_local_folds(raw,rows,aliases,folds)
    sites,ins,contracts=c.source(new)
    assert len(oldins)==3654 and len(ins)==3672
    changed=3553
    assert oldsites[changed][1:]==('breakTo',1)
    assert sites[changed][1:]==('dec',1)
    def relocate(i):return i if i<=changed else i+18
    for i,row in enumerate(oldins):
        if i==changed:continue
        n={'inc':2,'dec':2,'jump':1,'halt':1}[row[0]]
        assert row[:n]+tuple(relocate(t)for t in row[n:])==ins[relocate(i)]
    interiors=set(range(changed+1,changed+19))
    for i,row in enumerate(ins):
        if changed<=i<changed+19:continue
        n={'inc':2,'dec':2,'jump':1,'halt':1}[row[0]]
        assert not(set(row[n:])&interiors)
    startup=support.startup(rows,sites[25][0])
    dense,labels=support.dense_table(rows,len(rows)//2)
    result={'working_states':len(rows)//2,'raw_states':len(raw)//2,'AX_readers':len(shape),'folds':len(folds),'sites':len(sites),'contracts':len(contracts),'source_splice':{'parent_sites':len(oldins),'old_return_site':changed,'replacement_range':[changed,changed+19],'unchanged_relocated_instructions':len(oldins)-1,'no_external_edge_to_splice_interior':True},'startup':startup,'runtime':c.validate(rows,contracts) if full else None}
    for name,table in [('machine.tm',dense),('machine.native.tm',rows),('raw.native.tm',raw)]:
        (ROOT/name).write_text(support.table_text(table))
    for name,data in [('grammar.new.json',grammar_json(new)),('grammar.tree.json',new),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',ins),('labels.json',labels),('local.json',local)]:dump(ROOT/name,data)
    result['sha256']=hashlib.sha256((ROOT/'machine.tm').read_bytes()).hexdigest();dump(ROOT/'receipt.json',result);print(json.dumps(result,indent=2))
    assert result['sha256']=='7e1c6442816e5df05e961f2057719252a1976c9a195a786978bf1e2d3c8e466d'
if __name__=='__main__':main('--quick'not in sys.argv)
