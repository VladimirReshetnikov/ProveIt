#!/usr/bin/env python3
"""Single schema reparameterizations and adjacent AX-row exchanges.

Each schema's a,b,c parameters are permuted independently; u is fixed.
Every emitted scheme has exactly its previous numerical instance family.
Only the source target is certified here, not any literal machine.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
from generate_combined import load, DEFAULT

HERE=Path(__file__).resolve().parent

def rename(t, mapping):
    if isinstance(t,tuple):return tuple(rename(x,mapping) for x in t)
    return mapping.get(t,t)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--package',type=Path,default=DEFAULT)
    p.add_argument('--output',type=Path,default=HERE/'parameter_variants.json')
    a=p.parse_args()
    enc=a.package/'work/theory_encoding'
    v=load(enc/'check_dne_variants.py','param_dne')
    spec=v.load_spec()
    initial=spec['ax_rows']('a','old_cache','b','c','u')
    logical=initial[1:]
    old=spec['bundle']('a','b','c')
    bundle=v.normalize(old,{v.redexes(old)[5]})
    mapping=json.loads((enc/'macro_to_fine.json').read_text())
    records=[]
    seen=set()
    def add(name,rows,perm,changes,gen_label='a'):
        rows=[rows[i] for i in perm]
        key=gen_label,tuple(rows)
        if key in seen:return
        seen.add(key)
        gen=('all',gen_label,'old_cache')
        word=[166 if gen_label=='a' else 168,121,180,176]+[m for t in rows for m in v.emit(t)]+v.emit(bundle)+v.TAIL
        stack,events=v.execute_macros(word[:-5])
        assert stack==['old_top',gen,*rows,bundle]
        assert len(events)==2 and events[0]==(176,2) and events[1][0]==158
        assert word.count(158)==word.count(208)==1
        fine=''.join(mapping[str(m)] for m in word)
        assert len(fine)==1252
        records.append(dict(mask=20000+len(records),name=name,
            row_order=[8-i for i in perm],parameter_changes=changes,
            logical_rows=rows,bundle=bundle,word=word,fine_AX=fine,
            generalization_label=gen_label,
            fine_length=len(fine),fine_sha256=hashlib.sha256(fine.encode()).hexdigest(),
            input_events=events,proof='Independent bijective parameter renaming of complete schema families; output selectors adjusted to row order; unchanged DNE32 bundle'))
    add('control',logical,list(range(8)),[])
    for row in range(8):
        for perm in itertools.permutations('abc'):
            changes=dict(zip('abc',perm))
            changed=logical.copy()
            changed[row]=rename(changed[row],changes)
            add(f'row{8-row}_'+''.join(perm),changed,list(range(8)),[dict(row=8-row,map=changes)])
    for i in range(7):
        order=list(range(8));order[i],order[i+1]=order[i+1],order[i]
        add(f'swap{8-i}_{7-i}',logical,order,[])
    # c=ac-3 is independently arbitrary. Moving GEN's binder source from a
    # to c keeps its entire theorem-output family; select c=i for GEN_i.
    existing=list(records)
    for record in existing:
        rows=[v.freeze(x) for x in record['logical_rows']]
        add('genc_'+record['name'],rows,list(range(8)),record['parameter_changes'],'c')
        records[-1]['row_order']=record['row_order']
    a.output.write_text(json.dumps(dict(status='SOURCE_FAMILY_ONLY',variants=records),separators=(',',':'))+'\n')
    print(json.dumps(dict(variants=len(records),output=str(a.output))))

if __name__=='__main__':main()
