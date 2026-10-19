#!/usr/bin/env python3
"""Compile the new KSP source into the same routed interpreter and audit it.

This intentionally has its own new-source correspondence check.  The
production original-program audit is not called or weakened: that theorem
does not apply after changing the logical basis.  Every other routing role
and all register operations remain inherited and explicitly accounted for.
"""
from collections import Counter
from functools import cache
import hashlib
import json
from pathlib import Path
import sys
from time import monotonic

import basis_experiment as b
import prepare_basis_routing as r

sys.path.insert(0,str(r.P/'code'))
import build_routing_machine as inherited
import parametric_prefix_affine as affine
from review_affine_source import full_inc,full_strip

def freeze(x):return tuple(freeze(y) for y in x) if isinstance(x,list) else x
def write(path,x):path.write_text(json.dumps(x,indent=2)+'\n')
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def all_cases(table,sites,padding):
    """Generic inherited affine test applied to every NEW instruction site.

    Compared with the old fixed-size wrapper, only the expected number of
    cases changes to the literal new list's instruction/branch count.
    """
    affine.PADDING=padding
    assert padding>=max(len(p) for p,op,arg in sites)
    expected=sum(2 if op=='CD' else 1 for p,op,arg in sites)
    counts,rules_count=Counter(),Counter()
    n=0
    for p,op,arg in sites:
        for zero in ((True,False) if op=='CD' else (None,)):
            branch=(arg,zero) if op=='CD' else None
            effect=None;extra=0;overflow=False
            if op=='CI':successor,overflow=full_inc(p);effect=('inc',arg)
            elif op=='CD' and not zero:successor,overflow=full_inc(p);effect=('dec',arg);extra=1
            elif op=='CD':successor,overflow=full_inc(full_strip(p,'0',1))
            elif op=='CB':successor,overflow=full_inc(full_strip(p,'0',arg))
            elif op=='CC':successor=full_strip(p,'1',arg)
            else:assert op=='CH';successor=''
            gap=padding+extra+int(overflow)-len(successor)
            assert gap>=0
            right=[('b',int(z)) for z in successor]+[('r',0,1,gap),('b',1),('box',('plain',effect))]
            rules,literal=affine.run(table,p,branch,affine.canon([('b',1)],right),halt=(op=='CH'),fuel=1000)
            assert literal>0
            counts[op+('/zero' if zero else '/positive') if op=='CD' else op]+=1
            rules_count.update(rules)
            n+=1
        if n%1000==0:print('AFFINE',n,'/',expected,flush=True)
    assert n==expected
    return dict(status='PASS',new_program_cases=n,by_operation=dict(counts),padding=padding,
                inherited_affine_engine_sha256=sha(Path(affine.__file__)),rules=dict(rules_count))

def main():
    began=monotonic()
    folder=b.OUT/'routing_KSP_best'
    out=folder/'machine'
    out.mkdir(exist_ok=True)
    meta=json.loads((folder/'new_source.json').read_text())
    gram=json.loads((folder/'search45.json').read_text())
    basis_desc=json.loads((folder/'basis_ast.json').read_text())
    basis=freeze(basis_desc['basis_ast'])
    words=dict(r.NAMES)
    words[76]=meta['new_AX_word']
    rules={w:(a,c) for w,a,c in gram['rules']}
    assert len(rules)==gram['rules_count']
    for w,(a,c) in rules.items():
        assert w==a+c
        for bit,ch in enumerate((a,c)):
            assert ch in rules if len(ch)>1 else ch in r.SYMBOLS and r.PERMIT[ch]&(1<<bit)
    sequences=set(r.SOURCE['sequence_states'])
    erased={177,74}
    routes={(x['source'],x['read']):x['word'] for x in gram['routes']}
    alloc={words[q]:q for q in sequences if words[q] in rules}
    available=sorted((sequences|erased)-set(alloc.values()))
    fresh=256
    while len(available)<len(rules)-len(alloc):
        if fresh not in alloc.values() and fresh not in available:available.append(fresh)
        fresh+=1
    for word in sorted(set(rules)-set(alloc)):alloc[word]=available.pop(0)
    assert alloc[words[96]]==96
    original,start=inherited.rebuild.read_table(inherited.TABLE)
    assert start==95
    table={key:row for key,row in original.items() if key[0] not in sequences|erased}
    for key,(w,d,t) in list(table.items()):
        if key==(58,0):table[key]=(0,'L',84)
        elif key in routes:table[key]=(w,d,alloc[routes[key]])
        elif t in sequences:table[key]=(w,d,alloc[words[t]])
        else:assert t not in erased
    def destination(w):return r.SOURCE['atoms'][r.SYMBOLS[w]]['state'] if len(w)==1 else alloc[w]
    for word,(left,right) in rules.items():
        table[alloc[word],0]=(0,'R',destination(left))
        table[alloc[word],1]=(1,'R',destination(right))
    states={q for q,bit in table}
    assert len(table)==2*len(states)
    assert len(states)==117+len(rules)
    assert {t for w,d,t in table.values()}-states=={254}
    oldfile=out/'ksp_old_labels.tm'
    oldfile.write_text(inherited.rebuild.encode(table,95))
    order=[95]+sorted(states-{95})
    mapping={q:i for i,q in enumerate(order)}|{254:len(states)}
    canonical={(mapping[q],bit):(w,d,mapping[t]) for(q,bit),(w,d,t) in table.items()}
    tm=out/('ksp_'+str(len(states))+'.tm')
    tm.write_text(inherited.rebuild.encode(canonical,0))
    write(out/'renumbering.json',mapping)

    by_ast={int(i):words[int(q)] for q,i in r.SOURCE['sequence_ast_roots'].items()}
    @cache
    def changed(i):
        if i in by_ast and by_ast[i] in rules:return expand(by_ast[i])
        row=r.SOURCE['ast_dag'][i]
        return ('L',tuple(row[1])) if row[0]=='L' else ('N',changed(row[1]),changed(row[2]))
    @cache
    def expand(word):
        if len(word)==1:return changed(r.SOURCE['atoms'][r.SYMBOLS[word]]['ast'])
        return ('N',*(expand(x) for x in rules[word]))
    new_tree=changed(r.SOURCE['original_ast'])

    # Independent new source: emit its literal RPN from the independently
    # reconstructed original Wade DAG, before any semantic-word spelling.
    program=b.prefix+[m for row in list(basis)+b.old_rows[1:] for m in b.tb.emit(row)]+b.tb.emit(b.bundle)+b.tb.TAIL
    rows,_=b.tb.symbolic(program)
    assert rows==['old_top',b.spec['wal']('a','h')]+list(basis)+b.old_rows[1:]+[b.bundle]
    raw=''.join(b.macro_words[m] for m in program)
    assert b.expansion(raw)==b.expansion(words[76])
    builder=b.recovery.builder_from_dag(b.backend,b.nodes,b.names)
    builder.sequence_lookup={s.seq:i for i,s in enumerate(builder.sequences)}
    b.tb.lower_program(builder,b.nodes,program,'KSP_best',shared=True)
    @cache
    def source_tree(i):
        if isinstance(i,int):return ('N',*(source_tree(x) for x in builder.sequences[i].seq))
        if i=='halt':return ('L',('halt',))
        if i.startswith('_'):name,n=i[1:].split('.');return ('L',('brk' if name=='break' else 'cont',int(n)))
        _,reg,op=i.split('.')
        return ('L',('inc' if op=='inc' else 'dec',b.recovery.REGISTERS.index(reg)))
    wanted=source_tree(0)
    print('BUILT',len(states),'states; proving new-source register correspondence',flush=True)
    entries=inherited.rmpath.certificate(wanted,new_tree)
    correspondence=inherited.check_bisimulation(wanted,new_tree,entries)
    bits=lambda xs:''.join('1' if x else '0' for x in xs)
    write(out/'new_source_bisimulation.json',dict(start_pair=0,entries=[[bits(a),bits(c),nz,z] for a,c,nz,z in entries]))
    opcodes=dict(inc='CI',dec='CD',brk='CB',cont='CC',halt='CH')
    sites=[]
    for path,edge in inherited.paths(new_tree):
        op=opcodes[edge[0]]
        arg=edge[1] if len(edge)>1 else None
        if op in ('CI','CD'):arg=inherited.rebuild.PHYSICAL[arg]
        sites.append([path,op,arg])
    write(out/'new_source_sites_physical.json',sites)
    audit=all_cases({(str(q),bit):(w,d,str(t)) for(q,bit),(w,d,t) in table.items()},sites,64)
    print('AFFINE PASS; checking blank bootstrap',flush=True)
    boot=inherited.sparse_boot(table,500000,minimum_gap=64)
    write(out/'blank_boot.json',boot)
    result=dict(status='PASS_NEW_SOURCE_AFFINE_AND_BOOT' if boot['status']=='PASS' else 'BOOT_UNRESOLVED',
                working_states=len(states),grammar_states=len(rules),framework_states=117,
                literal_transition_rows=len(table),canonical_table_sha256=sha(tm),
                new_source_register_bisimulation=correspondence,
                new_source_instruction_leaves=len(sites),new_source_maximum_depth=max(len(x[0]) for x in sites),
                affine_instruction_audit=audit,
                blank_boot={k:v for k,v in boot.items() if k not in ('used_rows','all_one_positions','spare_values')},
                seconds=monotonic()-began,
                logical_status='Complete K/S/Peirce basis; code-level row and macro comparison described separately',
                kernel_checked_endpoint=False,
                scope='New source correspondence and inherited affine register contracts; no original-source bisimulation claimed')
    write(out/'new_source_machine_audit.json',result)
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
