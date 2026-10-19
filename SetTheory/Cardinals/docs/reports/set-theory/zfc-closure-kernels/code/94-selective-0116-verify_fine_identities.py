#!/usr/bin/env python3
"""Independently check exact fine-atom identities and a normalized grammar.

Only the Python standard library is used. No search engine is imported. This
checks source/grammar facts and a fixed-lock obstruction, not a TM simulation
theorem or a global lower bound on the number of states.
"""
import argparse,hashlib,json
from functools import cache
from pathlib import Path

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def verify(package,candidate=None,identities=None):
    source_path=package/'inputs/closed-sequence-grammar-next22.json'
    symbol_path=package/'inputs/semantic-symbols.json'
    source=json.loads(source_path.read_text())
    symbols=json.loads(symbol_path.read_text());encode={name:c for c,name in symbols.items()}
    ast=source['ast_dag']
    assert len(ast)==226
    @cache
    def bounds(i):
        row=ast[i]
        if row[0]=='L':
            op,*arg=row[1]
            if op=='dec':return 1,0
            if op=='brk':return arg[0],0
            if op=='cont':return 0,arg[0]
            return 0,0
        x,y=bounds(row[1]),bounds(row[2])
        return max(x[0]-1,y[0],0),max(x[1],y[1]-1,0)
    @cache
    def finest(i):
        row=ast[i]
        if row[0]=='N' and bounds(row[1])==bounds(row[2])==(0,0):
            return finest(row[1])+finest(row[2])
        return (i,)
    assert all(bounds(source['atoms'][name]['ast'])==(0,0)for name in symbols.values())
    atom_ids={c:finest(source['atoms'][name]['ast'])for c,name in symbols.items()}
    singles={ids[0]:c for c,ids in atom_ids.items()if len(ids)==1}
    all_ids={i for ids in atom_ids.values()for i in ids}
    assert len(singles)==len(all_ids)==30 and set(singles)==all_ids
    expansions={c:''.join(singles[i]for i in ids)for c,ids in atom_ids.items()}
    assert len(expansions)==len(set(expansions.values()))==44
    if identities:
        supplied=json.loads(identities.read_text())
        assert supplied['expansions']==expansions
        assert supplied['ast_ids']=={c:list(v)for c,v in atom_ids.items()}
    def norm(w):return ''.join(expansions[c]for c in w)
    raw_names={int(q):''.join(encode[t]for t in tokens)for q,tokens in source['flattened_semantic_words'].items()}
    names={q:norm(w)for q,w in raw_names.items()}
    assert len(set(names.values()))==len(names)==127
    terminals={expansions[c]:c for c in expansions}
    assert not set(names.values())&set(terminals)
    ax=raw_names[76]
    assert len(ax)==702 and len(norm(ax))==1270
    assert tuple(source['atoms'][symbols[c]]['ast']for c in norm(ax))==finest(source['sequence_ast_roots']['76'])
    # Derive all 54 frozen equations directly from the delivered text.
    lock_path=package/'inputs/state_reduction/bootstrap-lock54.txt'
    lock_lines=lock_path.read_text().splitlines()
    lock_rows=[line.split()for line in lock_lines[1:]]
    assert int(lock_lines[0])==len(lock_rows)==54
    locked={(w,int(b)):t for w,b,t in lock_rows}
    assert len(locked)==54
    chain=['eijkKCqkjGeU','eijkKCqkjGe','eijkKCqkjG','eijkKC','eijk','e']
    assert all(locked[w,0]==child for w,child in zip(chain,chain[1:]))
    leaf_ast=source['atoms'][symbols['e']]['ast']
    assert ast[leaf_ast][0]=='N'
    left_leaf=ast[leaf_ast][1]
    assert ast[left_leaf][0]=='L'
    assert raw_names[172]==chain[0] and source['sequence_ast_roots']['172']==221
    # The sixth zero enters the literal left instruction of atom e. The five
    # preceding zeros are forced by the above bootstrap equations.
    j_ast=source['atoms'][symbols['J']]['ast']
    assert ast[j_ast]==['N',218,221]
    assert raw_names[96]=='AEFIEFCJ' and source['original_ast']==source['sequence_ast_roots']['96']
    prefix_words=['AEFIEFCJ','EFIEFCJ','EFCJ','J']
    assert all(locked[w,1]==child for w,child in zip(prefix_words,prefix_words[1:]))
    locked_zero_witness=dict(word=chain[0],old_state=172,ast=221,word_chain=chain,atom='e',atom_ast=leaf_ast,atom_left_leaf=left_leaf,source_suffix='000000',full_source_path='1111000000',fixed_right_prefix=prefix_words,forced_leading_zeros=6,scope='Any grammar retaining these frozen equations and the fixed implementations of atoms J and e has the displayed source instruction path and cannot have maximum source zero run below six.')
    base=json.loads((package/'grammar.json').read_text())
    if candidate:
        d=json.loads(candidate.read_text())
        grammar={w:(a,b)for w,a,b in d['rules']}
    else:
        d=dict(base,rules=[[norm(w),norm(a),norm(b)]for w,a,b in base['rules']],roots=list(map(norm,base['roots'])),routes=[dict(r,word=norm(r['word']))for r in base['routes']],properties=None)
        grammar={w:(a,b)for w,a,b in d['rules']}
    assert len(grammar)==len(d['rules'])==d['rules_count']
    lines=(package/'inputs/state_reduction/route-grammar.txt').read_text().splitlines()
    n,nr,na=map(int,lines[0].split())
    expected_roots={norm(w)for w in lines[n+1:n+1+nr]}|{norm(w)for w,b in locked}
    assert set(d['roots'])==expected_roots
    assert d['erase177'] is True and d['retarget']==-2 and d['framework_states']==118
    allowed={expansions[c]:int(mask)for c,mask in map(str.split,lines[n+nr+1:])}
    for w,(a,b)in grammar.items():
        assert w==a+b and w not in terminals
        for bit,child in enumerate((a,b)):
            assert child in terminals or child in grammar
            if child in terminals:assert allowed[child]&(1<<bit)
    for (w,b),t in locked.items():assert grammar[norm(w)][b]==norm(t)
    routes={(r['source'],r['read']):r['word']for r in d['routes']}
    assert len(routes)==len(d['routes'])==11
    def project(w,p):
        for b in p:w=grammar[w][int(b)]
        return w
    projections=0
    for c in source['left_entry_projection_constraints']:
        reason=c['reason'];q=reason['source'];b=reason['read'];p=c['prefix']
        if reason.get('via')==177:p=str(reason['previous'])+p
        target=norm(''.join(encode[x]for x in c['word']))
        assert project(routes[q,b],p)==target
        projections+=1
    assert projections==22
    roots=set(d['roots'])|set(routes.values());seen=set()
    def visit(w):
        if w in terminals or w in seen:return
        seen.add(w)
        for child in grammar[w]:visit(child)
    for w in roots:visit(w)
    assert seen==set(grammar)
    # Independently expand the immutable AST, replacing exactly those pure
    # sequence words for which the proposed grammar supplies a production.
    by_ast={int(i):names[int(q)]for q,i in source['sequence_ast_roots'].items()}
    active=set()
    @cache
    def changed(i):
        key=('ast',i);assert key not in active;active.add(key)
        if i in by_ast and by_ast[i]in grammar:result=expand(by_ast[i])
        else:
            row=ast[i]
            result=('L',tuple(row[1]))if row[0]=='L' else ('N',changed(row[1]),changed(row[2]))
        active.remove(key);return result
    @cache
    def expand(w):
        key=('word',w);assert key not in active;active.add(key)
        if w in terminals:result=changed(source['atoms'][symbols[terminals[w]]]['ast'])
        else:
            a,b=grammar[w];result=('N',expand(a),expand(b))
        active.remove(key);return result
    @cache
    def original(i):
        row=ast[i]
        return ('L',tuple(row[1]))if row[0]=='L' else ('N',original(row[1]),original(row[2]))
    def paths(tree,p=''):
        if tree[0]=='L':return [(p,tree[1])]
        return paths(tree[1],p+'0')+paths(tree[2],p+'1')
    before=paths(original(source['original_ast']));after=paths(changed(source['original_ast']))
    assert len(before)==len(after)==6460
    assert [op for p,op in before]==[op for p,op in after]
    assert dict(after)['1111000000']==tuple(ast[left_leaf][1])
    zero=max(len(run)for p,op in after for run in p.split('1'))
    depth=max(len(p)for p,op in after)
    assert zero<=6 and depth<=64
    lead=len(after[0][0])-len(after[0][0].lstrip('0'))
    if d.get('properties'):assert d['properties'][:3]==[lead,zero,depth]
    return dict(status='PASS',source_sha256=digest(source_path),symbols_sha256=digest(symbol_path),candidate_sha256=digest(candidate)if candidate else None,closed_atoms=44,singleton_fine_atoms=30,compound_zero_extra_state_atoms=14,atom_normal_forms_unique=True,original_sequence_normal_forms_unique=True,original_sequence_atom_collisions=0,AX_original_spelling_length=702,AX_exact_fine_length=1270,normalization_identities=expansions,normalized_rules=len(grammar),reachable_rules=len(seen),route_groups=len(routes),exact_projections=projections,bootstrap_equations=len(locked),ordered_source_leaves=len(after),ordered_source_instructions_unchanged=True,maximum_zero_run=zero,maximum_source_depth=depth,locked_zero_witness=locked_zero_witness,scope='Exact normalization and bounded grammar invariants. This does not certify a new TM, a state lower bound, a complete binary simulation, or Con(ZFC).')

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--package',type=Path,required=True);p.add_argument('--candidate',type=Path);p.add_argument('--identities',type=Path);p.add_argument('--output',type=Path);a=p.parse_args()
    if not __debug__:p.error('Assertions must remain enabled.')
    result=verify(a.package,a.candidate,a.identities)
    text=json.dumps(result,indent=2)+'\n'
    if a.output:a.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
