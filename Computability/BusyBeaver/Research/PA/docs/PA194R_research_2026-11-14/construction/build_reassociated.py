#!/usr/bin/env python3
"""Rebuild PA194R: a substantially reassociated194-state decoder.

The resolved source graph is exactly PA194F. This checker certifies all local
folds, universal source outcomes, and the complete blank startup tape.
Python3.10+, standard library, assertions enabled; no network is used.
"""
from pathlib import Path
import argparse,hashlib,json,time
import build as b
c=b.c
PACKAGE=Path(__file__).resolve().parent.parent
EXPECTED_NATIVE='24539448def6e974d636052dbcb56eeb61d8e06ad0e9924d734c3bd4f0e01aa8'
EXPECTED_DENSE='8a9a8a30773f73b638a7c51da1afca9c9921371aea819d6a21f02d742f673a4e'

def expanded(t):
    inc=('leaf','inc',1)
    if t=='node60':return inc,inc
    if t=='node61':return (inc,inc),(inc,inc)
    return tuple(expanded(x) for x in t) if c.isnode(t) else t

def word(t):return word(t[0])+word(t[1]) if c.isnode(t) else [t]
def subtrees(t):return {t}|subtrees(t[0])|subtrees(t[1]) if c.isnode(t) else set()
def sha(text):return hashlib.sha256(text.encode()).hexdigest()

def build(out,full=True):
    assert __debug__
    started=time.monotonic()
    c.raw_nodes=lambda:b.nodes()
    def fixed():
        rows,labels=b.ORIGINAL_MACHINE();rows.update(b.COMBINED);rows.update(b.SYMMETRIC)
        return rows,labels
    c.machine=fixed
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    c.MACROS[('leaf','dec',6)]=21
    parent_tree=b.final_zero(c.read_grammar(PACKAGE/'inputs/pa194.grammar.json'))
    parent_sites,parent_ins,parent_contracts=c.source(parent_tree)
    parent_raw,_,parent_shape=c.build(parent_tree)
    parent_folds=json.loads((PACKAGE/'inputs/pa194.folds.json').read_text())+[[41,330,[[0,False,31],[1,False,46]]]]
    parent,parent_alias=b.fold(parent_raw,parent_folds)
    b.check_folds(parent_raw,parent,parent_alias,parent_folds)
    parent_dense,parent_labels=b.dense(parent)
    tree=c.read_grammar(PACKAGE/'inputs/pa194R.grammar.json')
    assert word(expanded(tree))==word(expanded(parent_tree))
    assert len(word(expanded(tree)))==190
    sites,ins,contracts=c.source(tree)
    assert ins==parent_ins
    assert len(sites)==3646 and len(contracts)==4746
    changed_paths=sum(p!=old[0] for (p,op,arg),old in zip(sites,parent_sites))
    assert changed_paths==1111
    raw,index,shape=c.build(tree)
    assert len(shape)==67 and len(raw)==404
    folds=json.loads((PACKAGE/'inputs/pa194R.folds.json').read_text())
    assert len(folds)==8 and [41,330,[[0,False,31],[1,False,46]]] in folds
    child,aliases=b.fold(raw,folds)
    local=b.check_folds(raw,child,aliases,folds)
    original,_=b.ORIGINAL_MACHINE()
    assert all(child[q,bit]==original[q,bit] for q in c.BOXSTATES for bit in (0,1))
    runtime=c.validate(child,contracts) if full else {'performed':False}
    if full:assert runtime['ok'],runtime
    startup=b.startup(child,sites[25][0]);assert startup['steps']==57768
    dense,labels=b.dense(child)
    native_text,dense_text=b.table_text(child),b.table_text(dense)
    assert sha(native_text)==EXPECTED_NATIVE and sha(dense_text)==EXPECTED_DENSE
    old_types=subtrees(expanded(parent_tree))-set(c.MACROS)
    new_types=subtrees(expanded(tree))-set(c.MACROS)
    sharing={'parent_AX_reader_subtree_types':len(old_types),'new_AX_reader_subtree_types':len(new_types),
             'shared_AX_reader_subtree_types':len(old_types&new_types),'replaced_AX_reader_subtree_types':len(old_types-new_types),
             'introduced_AX_reader_subtree_types':len(new_types-old_types),
             'expanded_macro_tokens':190,'expanded_binary_node_occurrences':189,
             'source_sites':len(sites),'changed_source_paths':changed_paths,
             'parent_maximum_source_path_length':max(len(p) for p,op,arg in parent_sites),
             'new_maximum_source_path_length':max(len(p) for p,op,arg in sites)}
    assert (sharing['parent_AX_reader_subtree_types'],sharing['new_AX_reader_subtree_types'],sharing['shared_AX_reader_subtree_types'])==(67,67,23)
    common=set(parent)&set(child)
    difference={'shared_native_row_keys':len(common),'different_actions_at_shared_native_row_keys':sum(parent[k]!=child[k] for k in common),
                'parent_only_native_row_keys':len(set(parent)-set(child)),'new_only_native_row_keys':len(set(child)-set(parent)),
                'scope':'Literal comparison in the two compiler-native allocations; graph novelty is checked separately.'}
    receipt={'family':'PA194R','status':'PASS','working_states':194,'transition_rows':388,'raw_controls':202,
             'fixed_controls_before_quotient':135,'axiom_readers':67,'simultaneous_folds':8,'local_cases':local['case_count'],
             'source_sites':len(sites),'source_outcomes':len(contracts),'source_instruction_graph_equal_PA194F':True,
             'changed_source_paths':changed_paths,'universal_contracts':runtime,'startup':startup,
             'native_sha256':EXPECTED_NATIVE,'dense_sha256':EXPECTED_DENSE,
             'parent_PA194F_native_sha256':sha(b.table_text(parent)),'parent_PA194F_dense_sha256':sha(b.table_text(parent_dense)),
             'source_object_sha256':sha(json.dumps(ins,separators=(',',':'))),'sharing':sharing,'native_label_comparison':difference,
             'arithmetic_box_rows_unchanged':True,'kernel_checked':False,'elapsed_seconds':round(time.monotonic()-started,3)}
    out.mkdir(parents=True,exist_ok=True)
    (out/'machine.native.tm').write_text(native_text);(out/'machine.tm').write_text(dense_text)
    (out/'unfolded202.native.tm').write_text(b.table_text(raw))
    for filename,obj in [('labels.json',labels),('grammar.json',b.grammar_json(tree)),('folds.json',folds),
                         ('local_folds.json',local),('blank_seed.json',startup),('instructions.json',ins),
                         ('sites.json',[[''.join(map(str,p)),op,arg] for p,op,arg in sites]),
                         ('sharing.json',sharing),('construction_receipt.json',receipt)]:b.dump(out/filename,obj)
    print(json.dumps({k:v for k,v in receipt.items() if k!='startup'},indent=2),flush=True)
    return receipt

if __name__=='__main__':
    if not __debug__:raise SystemExit('Run without -O or PYTHONOPTIMIZE.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=PACKAGE/'machines/PA194R')
    args=ap.parse_args();build(args.output)
