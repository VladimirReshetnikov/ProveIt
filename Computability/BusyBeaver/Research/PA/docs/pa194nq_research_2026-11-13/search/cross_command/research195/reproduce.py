#!/usr/bin/env python3
"""Check the frozen 195-state AX/MP sharing research candidate.

Uses the inherited construction runtime with imported arithmetic-block
contracts. This is not a new independent verifier or proof-assistant endpoint.
No search is needed. It writes no files.
"""
from pathlib import Path
import hashlib,json
import compiler as c
import baseline_tools as b

ROOT=Path(__file__).resolve().parent
DATA=ROOT/'machine'
ORIGINAL_NODES=c.raw_nodes
ORIGINAL_MACHINE=c.machine

def tuples(v):return tuple(tuples(x) for x in v) if isinstance(v,list) else v

def word(t):return word(t[0])+word(t[1]) if c.isnode(t) else [t]

def succ(code,pc,mask):
    z=code[pc]
    if z[0]=='jump':return [(z[1],mask)]
    if z[0]=='inc':return [(z[2],mask|(1<<z[1]))]
    if z[0]=='dec':
        bit=1<<z[1]
        return [(z[3],mask&~bit),(z[3],mask)] if mask&bit else [(z[2],mask)]
    return []

def closure(code):
    seen={(25,1)};todo=list(seen)
    for pc,mask in todo:
        for x in succ(code,pc,mask):
            assert 0<=x[0]<len(code)
            if x not in seen:seen.add(x);todo.append(x)
    return seen

def main():
    assert __debug__,'Run without Python -O.'
    saved=json.loads((DATA/'receipt.json').read_text())
    ep=tuples(saved['epilogue_tree'])
    assert word(ep)==['node55','node55','node55','node65',('leaf','inc',1),('leaf','inc',1)]
    # The exact free-constructor calculation of the new MP epilogue.
    B=('formula_parameter_b',);t=0;stack=[]
    for op in word(ep):
        if op=='node55':stack.append(t);t=B
        elif op=='node65':t=('imp',stack.pop(),t)
        else:t=('succ',t)
    assert t==('succ',('succ',('imp',B,B))) and stack==[0,B]
    
    def machine():
        rows,labels=ORIGINAL_MACHINE()
        rows.update({(38,0):(0,True,11),(38,1):(1,True,122),
            (214,0):(0,True,312),(214,1):(1,True,20),(312,0):(0,True,188),
            (27,1):(1,True,21)})
        return rows,labels
    def nodes(special=True):
        ns=ORIGINAL_NODES();ns['node163']=('node6',ep)
        ns['node170']=(('node36',('node167','node145')),'node57')
        if special:ns['node22']=(('leaf','dec',8),('leaf','dec',6))
        return ns
    c.machine=machine;c.raw_nodes=nodes
    inc=('leaf','inc',1)
    c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    c.MACROS[('leaf','dec',4)]=144
    ax=b.expanded(c.read_grammar(DATA/'axioms.grammar.json'))
    oldword=tuples(json.loads((ROOT/'reference/primary194_macro_word.json').read_text()))
    newword=word(ax)
    dif=[(i,a,z) for i,(a,z) in enumerate(zip(oldword,newword)) if a!=z]
    assert len(newword)==190 and dif==[(121,'node70','node55'),(122,'node70','node55'),
        (123,'node70','node55'),(189,('leaf','breakTo',1),('leaf','dec',4))]
    raw,index,shape=c.build(ax);raw[164,1]=(1,True,index[ep])
    assert len(raw)==406 and len(shape)==69
    folds=json.loads((DATA/'folds.json').read_text());assert len(folds)==8
    child,aliases=b.apply_folds(raw,folds)
    cases=b.check_local_folds(raw,child,aliases,folds)
    assert len(cases['cases'])==32
    assert raw==b.read_table(DATA/'raw.native.tm')
    assert child==b.read_table(DATA/'machine.native.tm')
    original,_=ORIGINAL_MACHINE()
    assert all(child[q,bit]==original[q,bit] for q in c.BOXSTATES for bit in (0,1))
    dense,labels=b.dense_table(child,195)
    assert b.table_text(dense)==(DATA/'machine.tm').read_text()
    assert labels==json.loads((DATA/'labels.json').read_text())
    digest=hashlib.sha256(b.table_text(dense).encode()).hexdigest()
    assert digest=='bc6137a920642ce7a83d00e7eb3d233843d46ae981b3ccfa520405933f34e9e7'
    sites,code,contracts=c.source(ax)
    assert json.loads(json.dumps(code))==json.loads((DATA/'instructions.json').read_text())
    assert [[''.join(map(str,p)),op,arg]for p,op,arg in sites]==json.loads((DATA/'sites.json').read_text())
    assert len(sites)==3753 and len(contracts)==4886
    valid=c.validate(child,contracts);assert valid['ok'] and valid==saved['construction_physical']
    startup=b.startup(child,sites[25][0]);assert startup==saved['startup'] and startup['steps']==58168
    def old_close(t):
        if c.isnode(t):return tuple(old_close(x)for x in t)
        return ('leaf','breakTo',1) if t==('leaf','dec',4) else t
    c.raw_nodes=lambda:nodes(False)
    _,oldcode,_=c.source(old_close(ax));c.raw_nodes=nodes
    changed=[i for i in range(len(code))if code[i]!=oldcode[i]]
    assert changed==[26,3553]
    reachable=closure(code);assert len(reachable)==264822
    assert all(succ(code,pc,m)==succ(oldcode,pc,m)for pc,m in reachable)
    assert all(x in reachable for pc,m in reachable for x in succ(oldcode,pc,m))
    print(json.dumps({'status':'PASS','working_states':195,'transitions':390,
        'raw_reader_states':69,'fixed_controls':134,'simultaneous_folds':8,
        'fold_cases':32,'source_sites':3753,'source_outcomes':4886,
        'physical':valid,'startup_steps':58168,'known_zero_pairs':264822,
        'machine_sha256':digest,'epilogue':'successful MP: (U(b,b),[b,0;w],b,0)',
        'scope':'Research candidate. Inherited universal construction checker, exact startup, source invariant; no new independent replay or end-to-end theorem.'},indent=2))

if __name__=='__main__':main()
