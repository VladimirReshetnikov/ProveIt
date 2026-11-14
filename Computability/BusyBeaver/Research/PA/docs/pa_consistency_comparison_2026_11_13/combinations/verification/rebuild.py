#!/usr/bin/env python3
"""Rebuild the exact diagonal199 source and table from frozen PA196 inputs.

Uses only the Python standard library. This independently checks source CFG
identity, the emitter word, compilation, and the four supplied quotient steps.
With --verify-stages, also replay every symbolic contract and exact startup at
each of the five intermediate tables. Run check.py for the final-table check.
"""
from pathlib import Path
from collections import defaultdict
import argparse,json
import symbolic as s
import check as checks

ROOT=Path(__file__).resolve().parents[1]
OLDTREE=s.TREE
OLDROWS=dict(s.rows)
MACROS=dict(zip(
    ('push','copyH','copyD','copyA','cons','incT','readH','readDCons',
     'copyGuard','compareGuard','close'),
    (s.NODES['node49'],s.NODES['node58'],s.NODES['node55'],s.NODES['node70'],
     s.NODES['node65'],('inc',1),s.NODES['node72'],s.NODES['node75'],
     s.NODES['node142'],s.NODES['node150'],('breakTo',1))))

def words(t):
    return [t] if isinstance(t,str) else words(t[0])+words(t[1])

def expand(t):
    return MACROS[t] if isinstance(t,str) else (expand(t[0]),expand(t[1]))

def replace(t,old,new):
    if t==old:return new
    if s.isleaf(t):return t
    return replace(t[0],old,new),replace(t[1],old,new)

def edge(M,q,p,b):
    tape={-1:1,**dict(enumerate(p+(b,)))}
    original=tape.copy();head=len(p)
    for _ in range(200):
        if head==len(p)+1:return q if tape==original else None
        if head not in tape or (q,tape[head]) not in M:return None
        w,d,q=M[q,tape[head]];tape[head]=w;head+=1 if d=='R' else -1
    return None

def decoder_map(M,tree):
    reps=defaultdict(set);occ=defaultdict(list)
    def visit(n,p,q):
        if s.isleaf(n):return
        reps[n].add(q);occ[n].append(p)
        for b,ch in enumerate(n):
            if not s.isleaf(ch):
                z=edge(M,q,p,b)
                assert z is not None,('invalid baseline decoder',p,q,b)
                visit(ch,p+(b,),z)
    visit(tree,(),84)
    return reps,occ

def reachable(M):
    todo=[74];seen={74}
    for q in todo:
        if q==254:continue
        for b in (0,1):
            z=M[q,b][2]
            if z not in seen:seen.add(z);todo.append(z)
    return {k:v for k,v in M.items() if k[0] in seen}

def graph(tree):
    checks.set_tree(tree);result=[]
    for p,(op,k) in s.SITES:
        if op=='halt':targets=()
        elif op=='inc':targets=(s.after(p),)
        elif op=='dec':targets=(s.after(s.cut(p,0,1)),s.after(p))
        elif op=='continueTo':targets=(s.lookup(s.cut(p,1,k)),)
        else:targets=(s.after(s.cut(p,0,k)),)
        result.append((op,k,targets))
    return result

def audit(tree,tokens,occ):
    old=graph(OLDTREE)
    start=s.lookup(occ[s.NODES['x67']][0]);end=start+s.size(s.NODES['x67'])
    blocks={}
    for name in set(tokens)-{'close','incT'}:
        n=MACROS[name];length=s.size(n);j=s.lookup(occ[n][0])
        block=[(op,k,tuple(z-j for z in targets)) for op,k,targets in old[j:j+length]]
        assert all(0<=z<=length for op,k,targets in block for z in targets)
        blocks[name]=block
    blocks['incT']=[('inc',1,(1,))]
    assert tokens[-1]=='close' and 'close' not in tokens[:-1]
    newlen=sum(s.size(MACROS[x]) for x in tokens);delta=newlen-(end-start)
    def relocate(z):
        if z<=start:return z
        if z>=end:return z+delta
        raise AssertionError(('outside edge enters AX interior',z))
    expected=[(op,k,tuple(relocate(z) for z in targets)) for op,k,targets in old[:start]]
    for name in tokens[:-1]:
        j=len(expected)
        expected.extend((op,k,tuple(j+z for z in targets)) for op,k,targets in blocks[name])
    op,k,targets=old[end-1];assert (op,k)==('breakTo',1)
    expected.append((op,k,tuple(relocate(z) for z in targets)))
    expected.extend((op,k,tuple(relocate(z) for z in targets)) for op,k,targets in old[end:])
    actual=graph(tree)
    assert expected==actual,'changed macro or outer control flow'
    return {'old_AX_range':[start,end],'new_AX_range':[start,start+newlen],
            'source_instruction_count':len(actual),'macro_word_length':len(tokens),
            'macro_CFG_exact':True,'outer_CFG_relocation_exact':True}

def compile_tree(ax,reps):
    new=expand(ax);tree=replace(OLDTREE,s.NODES['x67'],new)
    table={(q,b):v for (q,b),v in OLDROWS.items() if q<1300}
    states={q for q,b in table};mapped={};fresh=[]
    for n,qs in reps.items():
        available=qs&states
        if available:mapped[n]=min(available)
    incq=min(reps[(('inc',1),('inc',1))])
    leafact={(('inc',1),b):OLDROWS[incq,b] for b in (0,1)}
    cp=min(reps[s.NODES['x65']]);leafact[(('breakTo',1),1)]=OLDROWS[cp,1]
    def get(n):
        if n in mapped:return mapped[n]
        assert not s.isleaf(n)
        q=5000+len(fresh);fresh.append(n);mapped[n]=q
        for b,ch in enumerate(n):
            table[q,b]=leafact[ch,b] if s.isleaf(ch) else (b,'R',get(ch))
        return q
    table[101,1]=(1,'R',get(new))
    return reachable(table),tree,len(fresh)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--verify-stages',action='store_true')
    args=parser.parse_args();folder=ROOT/'diagonal199'
    data=json.loads((folder/'ax_macro_tree.json').read_text())
    ax=checks.tuplify(data['tree']);tokens=words(ax)
    assert tokens==data['tokens']
    import check_emitter as emitter
    assert tokens==emitter.new,'macro word is not the calibrated emitter'
    reps,occ=decoder_map(OLDROWS,OLDTREE)
    M,tree,fresh=compile_tree(ax,reps)
    assert fresh==69 and len(M)==406
    assert tree==checks.tuplify(json.loads((folder/'source.tree.json').read_text()))
    result=audit(tree,tokens,occ);result['initial_states']=len(M)//2
    if args.verify_stages:checks.run('initial203',M,tree)
    counts=[]
    for f in json.loads((folder/'folds.json').read_text()):
        a,z=f['keep'],f['drop']
        M={(q,b):(w,d,a if n==z else n) for (q,b),(w,d,n) in M.items() if q!=z}
        for b,(w,d,n) in enumerate(f['rows']):M[a,b]=(w,d,a if n==z else n)
        M=reachable(M);counts.append(len(M)//2)
        assert len(M)//2==f['states']
        if args.verify_stages:checks.run('fold'+str(len(counts)),M,tree)
    assert M==checks.parse(folder/'machine.native.tm'),'literal compiled table differs'
    checks.dense_check(folder,M)
    result.update({'fresh_readers':fresh,'fold_state_counts':counts,'final_states':len(M)//2,
                   'literal_native_table_equal':True,'dense_conjugacy':True,
                   'all_stages_runtime_checked':args.verify_stages})
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
