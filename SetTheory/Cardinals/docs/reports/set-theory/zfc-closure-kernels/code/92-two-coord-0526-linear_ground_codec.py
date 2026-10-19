#!/usr/bin/env python3
"""Linear-size ground-term names for FC13S/14S; no machine-state claim.

The six retained functions and d have fixed three-bit tags.  A prefix word
is parsed using the arities of those tags; no Cantor pairing is used.  The
optional ideal search enumerates well-formed words fairly and applies the
existing exact finite-ground-clause SAT decision.  Malformed words are skipped,
never treated as refutations.  Resource exceptions propagate.
"""
from __future__ import annotations
import argparse
from itertools import islice, product
import json
from pathlib import Path
import frozen_kernel as K
import frozen_frontend as F

SYMBOLS = [('d', 0)] + F.FUNCS
TAGS = {name: i for i, (name, _) in enumerate(SYMBOLS)}
WIDTH = (len(SYMBOLS)-1).bit_length()


def encode(tree, symbols=SYMBOLS):
    """An arity-delimited word, with exactly WIDTH bits per tree node."""
    out = []
    tags = {name:i for i,(name,_) in enumerate(symbols)}
    node_width = (len(symbols)-1).bit_length()
    pending = [tree]
    while pending:
        term = pending.pop()
        if not isinstance(term, tuple) or term[0] not in tags:
            raise ValueError('not a retained-signature ground term')
        tag = tags[term[0]]
        if len(term)-1 != symbols[tag][1]:
            raise ValueError('wrong arity')
        out.append(format(tag, '0'+str(node_width)+'b'))
        pending.extend(reversed(term[1:]))
    return ''.join(out)


def decode(bits, symbols=SYMBOLS):
    """Independent iterative parser; reject padding, truncation, and suffixes."""
    node_width = (len(symbols)-1).bit_length()
    if not bits or len(bits) % node_width or any(c not in '01' for c in bits):
        raise ValueError('invalid token word')
    frames = []
    root = None
    for pos in range(0, len(bits), node_width):
        if root is not None:
            raise ValueError('trailing tokens')
        tag = int(bits[pos:pos+node_width], 2)
        if tag >= len(symbols):
            raise ValueError('padding opcode')
        name, arity = symbols[tag]
        if arity:
            frames.append((name, arity, []))
            continue
        term = (name,)
        while frames:
            fname, farity, children = frames[-1]
            children.append(term)
            if len(children) < farity:
                break
            frames.pop()
            term = (fname,)+tuple(children)
        else:
            root = term
    if root is None or frames:
        raise ValueError('truncated tree')
    return root


def valid_tag_word(tags, symbols=SYMBOLS):
    """A shape check independent of decode; one pending child slot initially."""
    slots = 1
    for tag in tags:
        if slots == 0 or not 0 <= tag < len(symbols):
            return False
        slots += symbols[tag][1]-1
    return slots == 0


def terms(symbols=SYMBOLS):
    """All retained ground terms, once each, by token length then tag lex order.

    Filtering an explicitly finite block cannot conceal any later valid word.
    This is deliberately a simple reference enumeration, not a fast algorithm.
    """
    length = 1
    node_width = (len(symbols)-1).bit_length()
    while True:
        for tags in product(range(len(symbols)), repeat=length):
            if valid_tag_word(tags, symbols):
                bits = ''.join(format(t, '0'+str(node_width)+'b') for t in tags)
                yield decode(bits, symbols)
        length += 1


def instantiate(tree, environment):
    if isinstance(tree, str):
        return environment[tree]
    return (tree[0],)+tuple(instantiate(t, environment) for t in tree[1:])


def ground_stage(frontier, extensional=False, compare_cantor=False, clauses=None,
                 symbols=SYMBOLS, numeric_codec=F):
    """Substitute every frontier tuple; retain endpoints outside the frontier."""
    if clauses is None:
        clauses = K.reduced_witness_clauses(extensional, True)+K.equality_clauses(F.FUNCS)
    atoms = {}
    node_width = (len(symbols)-1).bit_length()
    cantor_atoms = {}
    result = []
    cantor_result = []
    max_nodes = max_depth = max_prefix_bits = max_cantor_bits = 0
    checked_endpoints = 0
    for clause in clauses:
        names = K.clause_vars(clause)
        for values in product(frontier, repeat=len(names)):
            environment = dict(zip(names, values))
            numeric_environment = {v:numeric_codec.encode(t) for v,t in environment.items()} if compare_cantor else None
            literals = []
            numeric_literals = []
            for sign, predicate, left, right in clause:
                endpoint_names = []
                numeric_names = []
                for source in (left, right):
                    tree = instantiate(source, environment)
                    bits = encode(tree, symbols)
                    assert decode(bits, symbols) == tree
                    assert len(bits) == node_width*K.term_nodes(tree)
                    max_nodes = max(max_nodes, K.term_nodes(tree))
                    max_depth = max(max_depth, K.term_depth(tree))
                    max_prefix_bits = max(max_prefix_bits, len(bits))
                    endpoint_names.append(bits)
                    if compare_cantor:
                        number = numeric_codec.instantiate(source, numeric_environment)
                        assert numeric_codec.encode(tree) == number
                        assert numeric_codec.decode(number) == tree
                        numeric_names.append(number)
                        max_cantor_bits = max(max_cantor_bits, number.bit_length())
                    checked_endpoints += 1
                atom = (predicate, *endpoint_names)
                if atom not in atoms:
                    atoms[atom] = len(atoms)+1
                literals.append(atoms[atom] if sign else -atoms[atom])
                if compare_cantor:
                    numeric_atom = (predicate, *numeric_names)
                    if numeric_atom not in cantor_atoms:
                        cantor_atoms[numeric_atom] = len(cantor_atoms)+1
                    numeric_literals.append(cantor_atoms[numeric_atom] if sign else -cantor_atoms[numeric_atom])
            result.append(frozenset(literals))
            if compare_cantor:
                cantor_result.append(frozenset(numeric_literals))
    if compare_cantor:
        assert result == cantor_result
    stats = {'frontier_terms':len(frontier), 'ground_clauses':len(result),
             'ground_atoms':len(atoms), 'maximum_endpoint_tree_nodes':max_nodes,
             'maximum_endpoint_depth':max_depth, 'maximum_prefix_word_bits':max_prefix_bits,
             'maximum_integer_name_bits_with_leading_one':max_prefix_bits+1,
             'checked_endpoint_occurrences':checked_endpoints}
    if compare_cantor:
        stats['maximum_cantor_endpoint_bits'] = max_cantor_bits
        stats['identical_numbered_CNF_after_atom_renaming'] = True
    return tuple(result), stats


def regressions():
    checks = 0
    for length in range(1, 6):
        for tags in product(range(8), repeat=length):
            bits = ''.join(format(t, '03b') for t in tags)
            valid = valid_tag_word(tags)
            try:
                tree = decode(bits)
            except ValueError:
                assert not valid
            else:
                assert valid
                assert encode(tree) == bits
            checks += 1
    frontier = list(islice(terms(), 2))
    assert frontier == [('d',), ('V', ('d',), ('d',))]
    assert frontier == [F.decode(0), F.decode(1)]
    return {'all_tag_words_through_five_tokens':checks,
            'first_two_terms_match_radix8_codes_0_1':True}


def whole_search(extensional=False, clauses=None, symbols=SYMBOLS):
    frontier = []
    for tree in terms(symbols):
        frontier.append(tree)
        ground, stats = ground_stage(frontier, extensional, clauses=clauses, symbols=symbols)
        if F.decide(ground) is None:
            return stats


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--whole-search', action='store_true')
    ap.add_argument('--extensional', action='store_true')
    ap.add_argument('--boolean-normalized', action='store_true')
    ap.add_argument('--output', type=Path, default=Path(__file__).with_name('linear-ground-results.json'))
    args = ap.parse_args()
    if args.boolean_normalized:
        import boolean_class_control as B
        build_clauses = lambda ext:B.source_clauses(ext)+K.equality_clauses(F.FUNCS)
    else:
        build_clauses = lambda ext:K.reduced_witness_clauses(ext,True)+K.equality_clauses(F.FUNCS)
    data = {'scope':'exact symbolic ground-term encoding and reference search; no binary TM state estimate',
            'codec':{'symbols':SYMBOLS, 'bits_per_node':WIDTH,
                     'integer_name':'one leading 1 followed by the prefix word'},
            'regressions':regressions()}
    data['variant'] = 'B' if args.boolean_normalized else 'S'
    if args.whole_search:
        data['result'] = 'UNSAT'
        data['stage'] = whole_search(args.extensional, build_clauses(args.extensional))
    else:
        data['comparison'] = {}
        frontier = list(islice(terms(), 2))
        for extensional in (False, True):
            clauses, stats = ground_stage(frontier, extensional, True, build_clauses(extensional))
            if not args.boolean_normalized:
                old_clauses, old_stats = F.ground_stage(1, extensional)
                assert clauses == old_clauses
                assert stats['maximum_cantor_endpoint_bits'] == old_stats['largest_endpoint_bits']
            valuation = F.decide(clauses)
            assert valuation is not None and F.check_valuation(clauses, valuation)
            stats['result'] = 'SAT'
            stats['witness_literals'] = len(valuation)
            data['comparison'][('FC14' if extensional else 'FC13')+data['variant']] = stats
    args.output.write_text(json.dumps(data, indent=2)+'\n')
    print(json.dumps(data, indent=2))


if __name__ == '__main__':
    main()
