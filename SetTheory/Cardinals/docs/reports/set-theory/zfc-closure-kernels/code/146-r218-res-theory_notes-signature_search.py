#!/usr/bin/env python3
"""Exact-tree emitter variants from equality and signature symmetries.

Only the source register arguments of 26-leaf parameter pushes change. All
primitive addresses, opcodes, and control-flow destinations remain fixed.
The output is a source screen with a conservative hardware lower bound, not
a validated Turing machine table.
"""
from pathlib import Path
import itertools
import json
import sys
import time

sys.path.insert(0,str(Path(__file__).resolve().parent))
import a10_source_search as a

ROOT=Path(__file__).resolve().parents[1]
z,s=a.z,a.s
source_rows=s.sites(a.old)
source_cfg=s.graph_arithmetic(source_rows)[0]
certificate=json.loads((ROOT/'k220_replay/parent_replay/baseline/K222_Construction_2026-10-20/portable/certificates/emitter222.json').read_text())
words=dict(z.WORDS)
words['seed']=certificate['macro_words']['new_seed_bundle']
intervals=dict(z.INTERVALS)
intervals['seed']=(2650,4563)
for name,word in words.items():
    lo,hi=intervals[name]
    assert sum((z.flat(z.MACRO[m])for m in word),())==z.flat(a.old)[lo:hi],name


def reverse_atoms(word,op):
    word=word.copy()
    for i,m in enumerate(word):
        if m==op:
            assert word[i-1] in (166,121,168) and word[i-2] in (166,121,168)
            word[i-2],word[i-1]=word[i-1],word[i-2]
    return word


def variant(eq_converse,rel_converse,g_exchange,g_conclusion,g_binder,eq3,eq5,perms=None):
    newwords={k:w.copy()for k,w in words.items()}
    g=newwords['G']
    if g_exchange:
        g[:6]=g[3:6]+g[:3]
    if g_conclusion:
        g[9],g[10]=g[10],g[9]
    if g_binder:
        g[6],g[7]=g[7],g[6]
    if eq3:newwords['rho3']=reverse_atoms(newwords['rho3'],182)
    if eq5:newwords['rho5']=reverse_atoms(newwords['rho5'],182)
    if eq_converse:
        for name in ('G','rho1','rho3','rho5'):
            newwords[name]=reverse_atoms(newwords[name],182)
    if rel_converse:
        for name in ('rho3','rho5','seed'):
            newwords[name]=reverse_atoms(newwords[name],181)
    for name,perm in (perms or {}).items():
        tr=dict(zip((166,121,168),perm))
        newwords[name]=[tr.get(m,m)for m in newwords[name]]
    rr=[r.copy()for r in source_rows]
    changed=[]
    for name,word in newwords.items():
        lo,hi=intervals[name]
        flat=sum((z.flat(z.MACRO[m])for m in word),())
        assert len(flat)==hi-lo
        for i,(op,arg)in enumerate(flat,lo):
            assert rr[i][1]==op
            if rr[i][2]!=arg:
                assert op in ('CD','CI') and rr[i][2]in(3,4,5) and arg in(3,4,5)
                changed.append((i,rr[i][2],arg))
                rr[i][2]=arg
    cfg=s.graph_arithmetic(rr)[0]
    assert [x[1]for x in cfg]==[x[1]for x in source_cfg]
    assert cfg==s.graph_intervals(rr)
    return s.tree(rr),newwords,changed


def main():
    out=ROOT/'theory_notes/signature_variants';out.mkdir(exist_ok=True)
    objective=a.hw.make(a.table,a.old)[0]
    results=[];best=999;start=time.monotonic()
    allvariants=[]
    for bits in itertools.product((0,1),repeat=7):
        tree,newwords,changed=variant(*bits)
        score=objective(tree)
        row=dict(flags=dict(zip(('equality_converse','membership_converse','G_antecedent_exchange','G_consequent_equality_reverse','G_binder_reverse','rho3_equality_reverse','rho5_equality_reverse'),bits)),hardware_lower_bound=score,metrics=s.metrics(tree),changed_leaves=len(changed))
        results.append(row)
        allvariants.append((score['cost_lower_bound'],row['metrics']['dag_nodes'],bits,tree))
        if score['cost_lower_bound']<best:
            best=score['cost_lower_bound'];print('BEST',json.dumps(row),flush=True)
        if score['cost_lower_bound']<=221:
            d=out/('v'+''.join(map(str,bits)));d.mkdir(exist_ok=True)
            (d/'sites.json').write_bytes(s.compact(s.sites(tree)))
            (d/'receipt.json').write_text(json.dumps(dict(**row,macro_words=newwords,changed_register_arguments=changed),indent=2)+'\n')
    (out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
    allvariants.sort(key=lambda x:x[:2])
    print('DONE',len(results),'best',best,'seconds',time.monotonic()-start,flush=True)
    print('TOP',[(c,d,bits)for c,d,bits,_ in allvariants[:15]],flush=True)


if __name__=='__main__':main()
