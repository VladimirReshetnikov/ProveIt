#!/usr/bin/env python3
"""FC14Q/Qd and FC15Q/Qd: name the distinguished true selector q.

Both start from Boolean-normalized B.  Q adds Inc(s,q); Qd instead adds
q=I(d,d), a literal definitional extension.  The former has native model
transports using I'(d,d)=q, justified in the mathematical note.  This script
prices, parses, and grounds the exact two-constant signatures without treating
the added constant as a free decoder convention.  No machine bound is claimed.
"""
from __future__ import annotations
import argparse
from itertools import islice, product
import json
from pathlib import Path
import boolean_class_control as B
import frozen_kernel as K
import frozen_frontend as F
import linear_ground_codec as L
import shared_template_codec as S

CONSTANTS = ('d','q')
FUNCS = F.FUNCS
SYMBOLS = [('d',0),('q',0)]+FUNCS
Q = ('q',)


def replace_selector(term, old_selector=K.q):
    if term == old_selector:
        return Q
    if isinstance(term,str):
        return term
    return (term[0],)+tuple(replace_selector(x, old_selector) for x in term[1:])


def source_clauses(extensional=False, definitional=True):
    clauses = [[(s,p,replace_selector(a),replace_selector(b)) for s,p,a,b in clause]
               for clause in B.source_clauses(extensional)]
    # Add the original selector expression only after replacement, so that
    # q=I(d,d) is a genuine definition rather than the vacuous q=q.
    clauses.append([K.eq(Q,K.q)] if definitional else [K.inc('s',Q)])
    return clauses


class NumericCodec:
    """Padded radix-eight Cantor comparator with two explicit constants."""
    @staticmethod
    def encode(tree):
        if tree == K.d:
            return 0
        if tree == Q:
            return 1
        tag = F.TAGS[tree[0]] if tree[0] in F.TAGS else int(tree[0][4:])
        return 2+tag+8*F.tuple_code(tuple(NumericCodec.encode(x) for x in tree[1:]))

    @staticmethod
    def decode(number):
        if number < 2:
            return K.d if number == 0 else Q
        tag, payload = (number-2)%8, (number-2)//8
        name, arity = FUNCS[tag] if tag < len(FUNCS) else ('junk'+str(tag),1)
        children = F.tuple_decode(payload,arity)
        assert all(0 <= x < number for x in children)
        return (name,)+tuple(NumericCodec.decode(x) for x in children)

    @staticmethod
    def instantiate(tree, environment):
        if isinstance(tree,str):
            return environment[tree]
        if tree == K.d:
            return 0
        if tree == Q:
            return 1
        return 2+F.TAGS[tree[0]]+8*F.tuple_code(tuple(NumericCodec.instantiate(x,environment) for x in tree[1:]))


def check_codec():
    checks = 0
    for length in range(1,6):
        for tags in product(range(8), repeat=length):
            bits = ''.join(format(t,'03b') for t in tags)
            valid = L.valid_tag_word(tags,SYMBOLS)
            try:
                tree = L.decode(bits,SYMBOLS)
            except ValueError:
                assert not valid
            else:
                assert valid and L.encode(tree,SYMBOLS) == bits
            checks += 1
    for number in range(4096):
        assert NumericCodec.encode(NumericCodec.decode(number)) == number
    assert list(islice(L.terms(SYMBOLS),2)) == [K.d,Q]
    return {'all_tag_words_through_five_tokens':checks,
            'two_constant_radix8_roundtrips':4096,
            'first_prefix_frontier':['d','q']}


def metrics(clauses):
    canonical,_,_ = S.renamed(clauses,'lexical')
    flat = S.flat_encode(canonical,FUNCS,K.PREDICATES,CONSTANTS)
    assert S.flat_decode(flat,FUNCS,K.PREDICATES,CONSTANTS) == canonical
    result = {'clauses':len(clauses),'literals':sum(map(len,clauses)),
              'term_nodes':sum(K.term_nodes(t) for c in clauses for l in c for t in l[2:]),
              'max_term_depth':max(K.term_depth(t) for c in clauses for l in c for t in l[2:]),
              'max_variables':max(len(K.clause_vars(c)) for c in clauses),
              'constant_count':2,'proper_function_count':6,'flat_opcode_width':4,
              'flat_bits':len(flat)}
    return result,flat


def shared_metrics(name, clauses, functions=FUNCS, predicates=K.PREDICATES, variable_slots=6):
    directory = Path(__file__).parent
    data = {}
    for policy in ('lexical','first_occurrence','greedy_dag'):
        canonical,maps,examined = S.renamed(clauses,policy)
        flat = S.flat_encode(canonical,functions,predicates,CONSTANTS,variable_slots)
        dag,dstats = S.dag_encode(canonical,functions,predicates,CONSTANTS,variable_slots)
        grammar,gstats = S.choose_macros(canonical,functions,predicates,CONSTANTS,variable_slots)
        for decoder,payload in ((S.flat_decode,flat),(S.dag_decode,dag),(S.grammar_decode,grammar)):
            assert decoder(payload,functions,predicates,CONSTANTS,variable_slots) == canonical
            for bad in (payload[:-1],payload+'0'):
                try:
                    decoder(bad,functions,predicates,CONSTANTS,variable_slots)
                except ValueError:
                    pass
                else:
                    raise AssertionError('malformed payload accepted')
        data[policy] = {'flat_bits':len(flat),'dag_bits':len(dag),'grammar_bits':len(grammar),
                        'variable_maps_examined':examined,
                        'dag':dstats,'grammar':{k:v for k,v in gstats.items() if k != 'macro_trees'}}
        key = name+'__'+policy
        audit = {'theory':name,'renaming_policy':policy,'functions':functions,
                 'predicates':predicates,'constants':CONSTANTS,'variable_slots':variable_slots,
                 'variable_maps':maps,'renamed_clauses':canonical,'macro_trees':gstats['macro_trees']}
        (directory/(key+'.shared.json')).write_text(json.dumps(audit,indent=2)+'\n')
        (directory/(key+'.dag.bits')).write_text(dag+'\n')
        (directory/(key+'.grammar.bits')).write_text(grammar+'\n')
    return data


def old_definition_controls():
    results = {}
    for name,(clauses,functions,predicates,old_bits) in S.load_inputs().items():
        if not name.startswith(('FC15star_','FC16star_')):
            continue
        old_q = ('N',K.d,K.d)
        named = [[(s,p,replace_selector(a,old_q),replace_selector(b,old_q))
                  for s,p,a,b in c] for c in clauses]+[[(True,'Eq',Q,old_q)]]
        native = name.endswith('_native')
        for slots in ([6,4] if native else [6]):
            label = name+'_Qd_slots'+str(slots)
            assert max(len(K.clause_vars(c)) for c in named) <= slots
            results[label] = {'source_flat_bits':old_bits,'variable_slots':slots,
                             'term_opcode_width':S.width(slots+2+len(functions)),
                             'metrics':shared_metrics(label,named,functions,predicates,slots)}
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--whole-search',action='store_true')
    ap.add_argument('--truth-only',action='store_true')
    ap.add_argument('--extensional',action='store_true')
    ap.add_argument('--output',type=Path,default=Path(__file__).with_name('named-selector-results.json'))
    args = ap.parse_args()
    if args.whole_search:
        clauses = source_clauses(args.extensional,not args.truth_only)+K.equality_clauses(FUNCS)
        stats = L.whole_search(args.extensional,clauses,SYMBOLS)
        result = {'result':'UNSAT','stage':stats,
                  'scope':'exact ideal prefix-ground refuter; no compiled TM or state claim'}
        args.output.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result,indent=2))
        return
    result = {'scope':'two explicitly charged constants; exact syntax and ground reference, no machine bound',
              'regressions':check_codec(),'metrics':{},'shared_metrics':{},'ground_comparisons':{}}
    for extensional in (False,True):
        for definitional in (False,True):
            name = ('FC15Q' if extensional else 'FC14Q')+('d' if definitional else '')
            for complete in (False,True):
                label = name+('_complete' if complete else '_native')
                clauses = source_clauses(extensional,definitional)+(K.equality_clauses(FUNCS) if complete else [])
                result['metrics'][label],flat = metrics(clauses)
                args.output.with_name(label+'.json').write_text(json.dumps(clauses,indent=2)+'\n')
                args.output.with_name(label+'.bits').write_text(flat+'\n')
                result['shared_metrics'][label] = shared_metrics(label,clauses)
            clauses = source_clauses(extensional,definitional)+K.equality_clauses(FUNCS)
            comparisons = {}
            for label,frontier in [('common_d_Vdd',[K.d,('V',K.d,K.d)]),
                                   ('own_first_two_d_q',[K.d,Q])]:
                ground,stats = L.ground_stage(frontier,extensional,True,clauses,SYMBOLS,NumericCodec)
                valuation = F.decide(ground)
                assert valuation is not None and F.check_valuation(ground,valuation)
                stats['result'] = 'SAT'; stats['witness_literals'] = len(valuation)
                comparisons[label] = stats
            result['ground_comparisons'][name] = comparisons
    result['source44_named_selector_controls'] = old_definition_controls()
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'metrics':result['metrics'],'ground_comparisons':result['ground_comparisons']},indent=2))


if __name__ == '__main__':
    main()
