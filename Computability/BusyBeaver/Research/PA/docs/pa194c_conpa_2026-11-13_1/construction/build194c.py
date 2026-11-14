#!/usr/bin/env python3
"""Construct the separated-head PA194C with the Combined command controller.

The decoder and seven simultaneous folds come from the supplied PA194.
Six literal rows and two source nodes install the already-proved Combined
command semantics. All physical source contracts are verified anew.
"""
from pathlib import Path
import hashlib, json, time
import build194 as p
import compiler as c

HERE=Path(__file__).resolve().parent
EDITS={
    (164,1):(1,True,130),
    (38,0):(0,True,11),
    (38,1):(1,True,122),
    (214,0):(0,True,312),
    (214,1):(1,True,20),
    (312,0):(0,True,188),
}

def bind_source(old,new):
    n=len(new)
    assert n==3649 and len(old)==n+24
    E,F,S=n-15,n-12,n-11
    oldF,oldS=len(old)-13,len(old)-12
    relocate={oldF:F,oldS:S}
    changed=[]
    for i in range(E):
        oi,ni=old[i],new[i]
        nargs=1 if oi[0]=='jump' else 2
        if oi[0]=='halt':
            assert oi==ni
            continue
        expected=oi[:nargs]+tuple(relocate.get(t,t) for t in oi[nargs:])
        assert expected==ni,(i,oi,ni,expected)
        if oi!=ni:changed.append([i,list(oi),list(ni)])
    expected=[
        ('dec',4,F,E+1),('inc',5,E+2),('jump',E),('jump',25),
        ('dec',1,S+2,S+1),('jump',S),
        ('dec',5,S+6,S+3),('inc',1,S+4),('inc',6,S+5),
        ('jump',S+2),('dec',6,S+9,S+7),('inc',5,S+8),
        ('jump',S+6),('inc',6,S+10),('jump',0),
    ]
    assert new[E:]==expected
    assert [x[0] for x in changed]==[48,n-96,n-16]
    return dict(old_sites=len(old),new_sites=n,prefix_length=E,
                mp_success_entry=E,fetch_return=F,shift_entry=S,
                old_fetch_return=oldF,old_shift_entry=oldS,
                relocated_rows=changed,exact_tail=expected)

def build():
    assert __debug__, 'Run with assertions enabled.'
    started=time.monotonic()
    parent,parent_sites,parent_cfg,parent_receipt=p.build(full=False)
    tree=c.read_grammar(HERE/'source/pa194.grammar.json')
    old_raw,old_index,old_shape=c.build(tree)
    old_machine,old_nodes=c.machine,c.raw_nodes
    def changed_machine():
        rows,labels=old_machine()
        rows.update(EDITS)
        return rows,labels
    def changed_nodes():
        nodes=old_nodes()
        nodes['node163']=('node6','node147')
        nodes['node170']=(('node36',('node167','node145')),'node57')
        return nodes
    c.machine,c.raw_nodes=changed_machine,changed_nodes
    raw,index,shape=c.build(tree)
    assert len(raw)==402 and len(shape)==67
    assert set(raw)==set(old_raw)
    assert {k:v for k,v in raw.items() if v!=old_raw[k]}==EDITS
    folds=json.loads((HERE/'source/pa194.folds.json').read_text())
    rows,aliases=p.apply_folds(raw,folds)
    assert len(rows)==388
    local=p.check_local_folds(raw,rows,aliases,folds)
    assert len(local['cases'])==28
    sites,cfg,contracts=c.source(tree)
    binding=bind_source(parent_cfg,cfg)
    reference=HERE.parent/'independent/reference_inputs/195C.instructions.json'
    assert hashlib.sha256(reference.read_bytes()).hexdigest()=='0afee1346c0931b3b91fea70571b01fd665a802ab9327409e4030f673412f5e3'
    assert json.loads(json.dumps(cfg))==json.loads(reference.read_text())
    binding['exact_complete_CFG_equal_to_prior_PA195C']=True
    binding['prior_PA195C_instruction_sha256']='0afee1346c0931b3b91fea70571b01fd665a802ab9327409e4030f673412f5e3'
    assert len(contracts)==4749
    assert all(rows[q,b]==parent[q,b] for q in c.BOXSTATES for b in (0,1))
    validation={}
    for name,tab in [('raw',raw),('folded',rows)]:
        validation[name]=c.validate(tab,contracts)
        assert validation[name]['ok'],(name,validation[name])
        print(name,'symbolic PASS',flush=True)
    blank=p.startup(rows,sites[25][0])
    assert blank['steps']==57922
    dense,labels=p.dense_table(rows)
    files={'pa194c.native.tm':p.table_text(rows),
           'pa194c.tm':p.table_text(dense),
           'pa194c.labels.json':json.dumps(labels)+'\n',
           'unfolded201c.native.tm':p.table_text(raw)}
    for name,text in files.items():(HERE/'tables'/name).write_text(text)
    for name,obj in [('sites',[[ ''.join(map(str,path)),op,arg] for path,op,arg in sites]),
                     ('instructions',cfg)]:
        (HERE/'source'/('pa194c.'+name+'.json')).write_text(json.dumps(obj)+'\n')
    (HERE/'source/pa194c.source.json').write_text(json.dumps([
        dict(ordinal=i,path=''.join(map(str,path)),op=op,arg=arg,instruction=cfg[i])
        for i,(path,op,arg) in enumerate(sites)])+'\n')
    receipt=dict(family='PA194C',status='PASS',working_states=194,rows=388,
        fixed_controls=134,raw_AX_readers=67,simultaneous_folds=7,
        local_cases=28,source_sites=len(sites),source_contracts=len(contracts),
        source_binding=binding,arithmetic_box_rows_unchanged=True,
        exact_native_edits=[[q,b,w,d,n] for (q,b),(w,d,n) in sorted(EDITS.items())],
        symbolic_runtime=validation,startup=blank,
        sha256={name:hashlib.sha256(txt.encode()).hexdigest() for name,txt in files.items()},
        parent_dense_sha256=parent_receipt['sha256']['dense'],
        kernel_checked=False)
    (HERE/'evidence/pa194c.verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (HERE/'evidence/pa194c.local_cases.json').write_text(json.dumps(local,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
    return rows,sites,cfg,receipt

if __name__=='__main__':build()
