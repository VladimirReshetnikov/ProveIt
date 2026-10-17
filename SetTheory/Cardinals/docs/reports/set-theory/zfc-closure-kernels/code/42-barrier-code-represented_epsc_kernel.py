#!/usr/bin/env python3
"""Emit a finite represented-EPSC kernel; all metrics are syntax, not TM states.

This is a new finite presentation built from Friedman's assignment/class
machinery and ProveIt's previously calibrated full equality-free EPSC.
The fifteen clauses are a satisfiability-preserving Skolemization with a
Boolean branch marker.  It is not a verified binary compiler.
"""
import argparse
import json
from pathlib import Path

FUNCTIONS = {'o': 0, 'V': 2, 'C': 3, 'N': 2, 'A': 2, 'Q': 2,
             'W': 3, 'G': 2, 'F': 2, 'H': 2, 'U': 3, 'Z': 3,
             'D': 1, 'S': 3}
PREDICATES = {'E': 2, 'P': 2, 'eq': 2}

def v(x):
    return '?' + x

def f(name, *args):
    assert name in FUNCTIONS and len(args) == FUNCTIONS[name]
    return [name, *args]

def lit(positive, predicate, *args):
    assert predicate in PREDICATES and len(args) == PREDICATES[predicate]
    return {'positive': positive, 'predicate': predicate, 'args': list(args)}

def E(x, y, positive=True):
    return lit(positive, 'E', x, y)

def P(x, y, positive=True):
    return lit(positive, 'P', x, y)

def eq(x, y, positive=True):
    return lit(positive, 'eq', x, y)

def relation(b, t, x, y, positive=True):
    return P(f('C', f('C', b, f('o'), x), f('N', f('o'), f('o')), y), t, positive)

def kernel():
    s, j, z, k, a, b, t, d, x, y = map(v, ('s','j','z','k','a','b','t','d','x','y'))
    clauses = []
    def add(name, *literals):
        clauses.append({'name': name, 'literals': list(literals)})
    add('change_same', eq(f('V', f('C',s,j,z),j), z))
    add('change_other', eq(k,j), eq(f('V',f('C',s,j,z),k),f('V',s,k)))
    add('nand_not_both', P(s,f('N',a,b),False), P(s,a,False), P(s,b,False))
    add('nand_left', P(s,f('N',a,b)), P(s,a))
    add('nand_right', P(s,f('N',a,b)), P(s,b))
    add('atom_forward', P(s,f('A',j,k),False), E(f('V',s,j),f('V',s,k)))
    add('atom_backward', P(s,f('A',j,k)), E(f('V',s,j),f('V',s,k),False))
    add('exists_forward', P(f('C',s,j,z),a,False), P(s,f('Q',j,a)))
    add('exists_backward', P(s,f('Q',j,a),False), P(f('C',s,j,f('W',s,j,a)),a))
    flag = f('G',b,t)
    source = f('F',b,t)
    hull = f('H',b,t)
    output = f('U',b,t,d)
    member = f('Z',b,t,d)
    add('unbounded_output', eq(flag,f('o'),False), relation(b,t,source,output))
    add('unbounded_member', eq(flag,f('o'),False), E(member,output))
    add('unbounded_escape', eq(flag,f('o'),False), E(member,d,False))
    add('empty_closure', eq(flag,f('o')), E(f('D',x),x),
        relation(b,t,x,y,False), E(y,hull))
    add('member_closure', eq(flag,f('o')), E(x,hull,False),
        relation(b,t,x,y,False), E(y,hull))
    add('support', eq(flag,f('o')), E(y,hull,False),
        relation(b,t,f('S',b,t,y),y))
    return {'name':'FAK5 represented-EPSC kernel', 'functions':FUNCTIONS,
            'predicates':PREDICATES,
            'equality':'eq denotes genuine equality; equality inference/axioms must be supplied by the checker',
            'clauses':clauses}

def shared_kernel():
    """Share witnesses whose obligations occur in disjoint gate branches."""
    data = kernel()
    def tr(t):
        if isinstance(t,str): return t
        name = t[0]
        args = [tr(a) for a in t[1:]]
        if name in ('F','H'): name='K'
        elif name=='S': name='U'
        elif name=='Z': name='T'
        elif name=='D':
            name='T'
            args=[v('b'),v('t'),*args]
        return [name,*args]
    for c in data['clauses']:
        for l in c['literals']: l['args']=[tr(t) for t in l['args']]
    data['name']='FAK5 represented-EPSC kernel with conditional witness sharing'
    data['functions']={'o':0,'V':2,'C':3,'N':2,'A':2,'Q':2,'W':3,'G':2,'K':2,'U':3,'T':3}
    return data

def selector_term(index, selector='term'):
    """Ground coordinates from Change/NAND; named mode also assumes q != o."""
    assert index>=0
    o=f('o')
    if selector not in ('term','named'):
        raise ValueError('selector must be term or named')
    q=f('N',o,o) if selector=='term' else ['q']
    if index==0: return o
    if index==1: return q
    oo=f('V',o,o)
    qq=f('V',q,q)
    c=f('C',f('C',o,o,f('N',oo,oo)),q,f('N',qq,qq))
    result=o
    for _ in range(index-1): result=f('C',c,c,result)
    return result

def named_selector_kernel():
    """Safe definitional extension naming the four repeated N(o,o) terms."""
    data=shared_kernel()
    target=['N',['o'],['o']]
    def tr(t):
        if t==target: return ['q']
        return t if isinstance(t,str) else [t[0],*(tr(a) for a in t[1:])]
    for c in data['clauses']:
        for l in c['literals']: l['args']=[tr(t) for t in l['args']]
    data['functions']={**data['functions'],'q':0}
    data['clauses'].append({'name':'selector_definition','literals':[eq(['q'],target)]})
    data['name']='FAK5 shared witnesses with a named second selector'
    return data

def predicate_gate_kernel(selector='term'):
    """Native branch predicate; optionally an independent distinct selector.

    selector='term': q is N(o,o), fifteen clauses.
    selector='defined': constant q with equation q=N(o,o), sixteen clauses.
    selector='distinct': constant q with q!=o, sixteen clauses.
    """
    assert selector in ('term','defined','distinct')
    data=shared_kernel() if selector=='term' else named_selector_kernel()
    for c in data['clauses']:
        for l in c['literals']:
            if l['predicate']=='eq' and l['args']==[['G','?b','?t'],['o']]:
                l['predicate']='B'
                l['args']=['?b','?t']
    data['functions']={name:arity for name,arity in data['functions'].items() if name!='G'}
    data['predicates']={**data['predicates'],'B':2}
    if selector=='distinct':
        data['clauses'][-1]={'name':'distinct_selectors','literals':[eq(['q'],['o'],False)]}
    data['name']='FEC native predicate branch, selector '+selector
    return data

def commutative_nand_kernel(selector='distinct'):
    """Calibrated stronger constructor choice: N is commutative.

    Canonical external class codes give the upper model.  The missing second
    positive NAND clause follows from the first by symmetry and equality.
    """
    data=predicate_gate_kernel(selector)
    for index,clause in enumerate(data['clauses']):
        if clause['name']=='nand_right':
            data['clauses'][index]={'name':'nand_commutative',
                'literals':[eq(['N','?a','?b'],['N','?b','?a'])]}
            break
    data['name']=f'FEC native predicate branch, {selector} selector, commutative NAND'
    return data

def term_nodes(t):
    return 1 if isinstance(t,str) else 1+sum(term_nodes(x) for x in t[1:])

def term_depth(t):
    return 0 if isinstance(t,str) or len(t)==1 else 1+max(term_depth(x) for x in t[1:])

def term_vars(t):
    return {t} if isinstance(t,str) else set().union(*(term_vars(x) for x in t[1:]))

def validate(payload):
    def check_term(t):
        if isinstance(t,str):
            assert t.startswith('?') and len(t)>1
            return
        assert isinstance(t,list) and t and t[0] in payload['functions']
        assert len(t)-1 == payload['functions'][t[0]]
        for a in t[1:]: check_term(a)
    names = set()
    for c in payload['clauses']:
        assert c['name'] not in names
        names.add(c['name'])
        for l in c['literals']:
            assert type(l['positive']) is bool
            assert l['predicate'] in payload['predicates']
            assert len(l['args']) == payload['predicates'][l['predicate']]
            for a in l['args']: check_term(a)

def metrics(payload):
    validate(payload)
    literals = [l for c in payload['clauses'] for l in c['literals']]
    terms = [t for l in literals for t in l['args']]
    proper = [a for a in payload['functions'].values() if a]
    return {'clauses':len(payload['clauses']), 'literal_occurrences':len(literals),
            'term_node_occurrences':sum(map(term_nodes,terms)),
            'maximum_term_depth':max(map(term_depth,terms)),
            'maximum_clause_variables':max(len(set().union(*(term_vars(t) for l in c['literals'] for t in l['args']))) for c in payload['clauses']),
            'constants':sum(a==0 for a in payload['functions'].values()),
            'proper_function_symbols':len(proper),
            'proper_function_arities':{str(a):proper.count(a) for a in sorted(set(proper))},
            'proper_relation_symbols':len(payload['predicates'])-1,
            'equality_is_additional':True,
            'compact_json_bytes':len(json.dumps(payload,separators=(',',':')).encode())}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out',type=Path,default=Path(__file__).with_name('fak5_clauses.json'))
    args = ap.parse_args()
    data = kernel()
    args.out.write_text(json.dumps(data,indent=2)+'\n')
    measured=metrics(data)
    args.out.with_name('fak5_metrics.json').write_text(json.dumps(measured,indent=2)+'\n')
    shared=shared_kernel()
    args.out.with_name('fak5_shared_clauses.json').write_text(json.dumps(shared,indent=2)+'\n')
    args.out.with_name('fak5_shared_metrics.json').write_text(json.dumps(metrics(shared),indent=2)+'\n')
    named=named_selector_kernel()
    args.out.with_name('fak5_named_selector_clauses.json').write_text(json.dumps(named,indent=2)+'\n')
    args.out.with_name('fak5_named_selector_metrics.json').write_text(json.dumps(metrics(named),indent=2)+'\n')
    for selector in ('term','defined','distinct'):
        candidate=predicate_gate_kernel(selector)
        stem='fec_predicate_gate_'+selector
        args.out.with_name(stem+'_clauses.json').write_text(json.dumps(candidate,indent=2)+'\n')
        args.out.with_name(stem+'_metrics.json').write_text(json.dumps(metrics(candidate),indent=2)+'\n')
    commutative=commutative_nand_kernel()
    args.out.with_name('fec16b_compressed_clauses.json').write_text(json.dumps(commutative,indent=2)+'\n')
    args.out.with_name('fec16b_compressed_metrics.json').write_text(json.dumps(metrics(commutative),indent=2)+'\n')
    termcomm=commutative_nand_kernel('term')
    termcomm['name']='FEC native predicate branch, term selector, commutative NAND'
    args.out.with_name('fec15b_compressed_clauses.json').write_text(json.dumps(termcomm,indent=2)+'\n')
    args.out.with_name('fec15b_compressed_metrics.json').write_text(json.dumps(metrics(termcomm),indent=2)+'\n')
    print(json.dumps(measured,indent=2))
    print(json.dumps(metrics(shared),indent=2))
    print(json.dumps(metrics(named),indent=2))

if __name__ == '__main__': main()
