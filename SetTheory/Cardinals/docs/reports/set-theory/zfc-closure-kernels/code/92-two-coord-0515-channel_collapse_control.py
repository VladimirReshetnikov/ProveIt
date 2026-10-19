#!/usr/bin/env python3
"""Measured, rejected three-function encoding direction; proof sketch only.

I,A,U are replaced by tagged coordinate reads from F outputs.  The count is
exact, but this file is not an additional claimed consistency-certified target.
It records why reducing the proper-function count to three is unhelpful for
these literal tree and shared-template formats.
"""
from __future__ import annotations
import json
from pathlib import Path
import frozen_kernel as K
import named_selector as Q
import shared_template_codec as S

FUNCS = [('V',2),('C',3),('F',2)]


def f(name,*children):
    return (name,)+children


def pair(a,b):
    return f('C',f('C',K.d,K.d,a),Q.Q,b)


TAGS = {'I':pair(K.d,K.d),'A':pair(K.d,Q.Q),'U':pair(Q.Q,K.d)}


def convert(tree):
    if isinstance(tree,str) or len(tree) == 1:
        return tree
    children = tuple(convert(t) for t in tree[1:])
    if tree[0] in TAGS:
        return f('V',f('F',pair(TAGS[tree[0]],pair(*children)),K.d),K.d)
    return (tree[0],)+children


def main():
    directory = Path(__file__).parent
    result = {'scope':'exact negative payload experiment; upper-model argument only sketched, no new consistency target or state claim',
              'functions':FUNCS,'metrics':{}}
    for extensional in (False,True):
        native = [[(s,p,convert(a),convert(b)) for s,p,a,b in c]
                  for c in Q.source_clauses(extensional,False)]
        for complete in (False,True):
            name = ('three_function_extensional' if extensional else 'three_function_raw')+('_complete' if complete else '_native')
            clauses = native+(K.equality_clauses(FUNCS) if complete else [])
            canonical,_,_ = S.renamed(clauses,'lexical')
            flat = S.flat_encode(canonical,FUNCS,K.PREDICATES,Q.CONSTANTS)
            grammar,stats = S.choose_macros(canonical,FUNCS,K.PREDICATES,Q.CONSTANTS)
            assert S.flat_decode(flat,FUNCS,K.PREDICATES,Q.CONSTANTS) == canonical
            assert S.grammar_decode(grammar,FUNCS,K.PREDICATES,Q.CONSTANTS) == canonical
            for decoder,payload in ((S.flat_decode,flat),(S.grammar_decode,grammar)):
                for bad in (payload[:-1],payload+'0'):
                    try:
                        decoder(bad,FUNCS,K.PREDICATES,Q.CONSTANTS)
                    except ValueError:
                        pass
                    else:
                        raise AssertionError('malformed channel-control payload accepted')
            result['metrics'][name] = {'clauses':len(clauses),'literals':sum(map(len,clauses)),
                                      'term_nodes':sum(K.term_nodes(t) for c in clauses for l in c for t in l[2:]),
                                      'depth':max(K.term_depth(t) for c in clauses for l in c for t in l[2:]),
                                      'flat_bits':len(flat),'lexical_grammar_bits':len(grammar),
                                      'macro_records':stats['macro_records']}
            (directory/(name+'.json')).write_text(json.dumps(clauses,indent=2)+'\n')
            (directory/(name+'.bits')).write_text(flat+'\n')
            (directory/(name+'.grammar.bits')).write_text(grammar+'\n')
    (directory/'channel-collapse-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
