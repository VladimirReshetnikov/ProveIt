#!/usr/bin/env python3
"""Identical, explicitly charged non-flat codecs for four finite theories.

These are syntactic template encodings, with fixed known signatures as in the
source44 flat format.  Dictionary entries are macros with local-variable slots,
not new function symbols or semantic axioms.  No TM state conversion is made.
"""
from __future__ import annotations
from collections import Counter
from itertools import permutations
import json
from pathlib import Path
import frozen_kernel as K
import boolean_class_control as B


def width(count):
    assert count >= 1
    return (count-1).bit_length()


def binary(value, size):
    assert 0 <= value < 1 << size
    return format(value, '0'+str(size)+'b') if size else ''


def gamma(value):
    assert value >= 1
    bits = bin(value)[2:]
    return '0'*(len(bits)-1)+bits


class Reader:
    def __init__(self, bits):
        if any(c not in '01' for c in bits):
            raise ValueError('nonbinary payload')
        self.bits = bits
        self.pos = 0

    def take(self, size):
        if self.pos+size > len(self.bits):
            raise ValueError('truncated payload')
        value = int(self.bits[self.pos:self.pos+size], 2) if size else 0
        self.pos += size
        return value

    def gamma(self):
        zeros = 0
        while self.take(1) == 0:
            zeros += 1
        return (1 << zeros)+self.take(zeros)

    def finish(self):
        if self.pos != len(self.bits):
            raise ValueError('trailing payload bits')


def map_clause(clause, rename):
    def term(t):
        return rename[t] if isinstance(t, str) else (t[0],)+tuple(term(x) for x in t[1:])
    return [(s,p,term(a),term(b)) for s,p,a,b in clause]


def first_occurrence_variables(clause):
    seen = []
    def visit(t):
        if isinstance(t, str):
            if t not in seen:
                seen.append(t)
        else:
            for child in t[1:]:
                visit(child)
    for literal in clause:
        visit(literal[2]); visit(literal[3])
    return seen


def constructors(clauses):
    counts = Counter()
    def visit(t):
        if isinstance(t, str) or len(t) == 1:
            return
        counts[t] += 1
        for child in t[1:]:
            visit(child)
    for clause in clauses:
        for literal in clause:
            visit(literal[2]); visit(literal[3])
    return counts


def renamed(clauses, policy):
    """Only independent, bijective, local universal-variable renamings.

    greedy_dag chooses each clause's permutation to minimize the size of the
    union of constructor subtrees already emitted plus that clause.  It is one
    forward pass; all n! maps onto v0,...,v(n-1) are considered, lexical ties.
    No literal or clause is reordered.  This is not a global optimum search.
    """
    out, maps = [], []
    existing = set()
    examined = 0
    for clause in clauses:
        names = K.clause_vars(clause)
        if policy == 'lexical':
            choices = [dict(zip(names, ('v'+str(i) for i in range(len(names)))))]
        elif policy == 'first_occurrence':
            ordered = first_occurrence_variables(clause)
            choices = [dict(zip(ordered, ('v'+str(i) for i in range(len(names)))))]
        elif policy == 'greedy_dag':
            choices = (dict(zip(names, ('v'+str(i) for i in perm)))
                       for perm in permutations(range(len(names))))
        else:
            raise ValueError('unknown renaming policy')
        best = None
        for rename in choices:
            candidate = map_clause(clause, rename)
            terms = set(constructors([candidate]))
            score = len(existing | terms)
            examined += 1
            if best is None or score < best[0]:
                best = (score, candidate, rename, terms)
        _, candidate, rename, new_terms = best
        # The independently stored inverse mapping restores the exact input.
        # It is audit metadata, not encoded payload: local alpha-renaming is
        # part of the syntax selected for the equivalent universal theory.
        inverse = {v:k for k,v in rename.items()}
        assert map_clause(candidate, inverse) == clause
        out.append(candidate); maps.append(rename); existing |= new_terms
    return out, maps, examined


def setup(functions, constants=('d',), variable_slots=6):
    offset = variable_slots+len(constants)
    return {name:offset+i for i,(name,_) in enumerate(functions)}


def flat_encode(clauses, functions, predicates, constants=('d',), variable_slots=6):
    tags = setup(functions, constants, variable_slots)
    constant_tags = {name:variable_slots+i for i,name in enumerate(constants)}
    node_width = width(variable_slots+len(constants)+len(functions))
    def term(t):
        if isinstance(t, str):
            return binary(int(t[1:]), node_width)
        return binary(constant_tags[t[0]] if len(t) == 1 else tags[t[0]], node_width)+''.join(term(x) for x in t[1:])
    return clause_encode(clauses, predicates, term)


def flat_decode(bits, functions, predicates, constants=('d',), variable_slots=6):
    reader = Reader(bits)
    leaves = variable_slots+len(constants)
    node_width = width(leaves+len(functions))
    def term():
        tag = reader.take(node_width)
        if tag < variable_slots:
            return 'v'+str(tag)
        if tag < leaves:
            return (constants[tag-variable_slots],)
        if tag-leaves >= len(functions):
            raise ValueError('invalid term opcode')
        name, arity = functions[tag-leaves]
        return (name,)+tuple(term() for _ in range(arity))
    return clause_decode(reader, predicates, term)


def clause_encode(clauses, predicates, term):
    out = []
    for clause in clauses:
        assert 1 <= len(clause) <= 7
        out.append(binary(len(clause), 3))
        for sign, predicate, left, right in clause:
            out.extend([str(int(sign)), binary(predicates.index(predicate), 2),
                        term(left), term(right)])
    return ''.join(out)+'000'


def clause_decode(reader, predicates, term):
    clauses = []
    while True:
        size = reader.take(3)
        if not size:
            reader.finish()
            return clauses
        clause = []
        for _ in range(size):
            sign, pred = bool(reader.take(1)), reader.take(2)
            if pred >= len(predicates):
                raise ValueError('invalid predicate tag')
            clause.append((sign, predicates[pred], term(), term()))
        clauses.append(clause)


def sorted_terms(terms):
    # Proper subtrees have strictly smaller depth.  repr breaks same-depth
    # ties deterministically; no source-file or Python object identity matters.
    return sorted(terms, key=lambda t:(K.term_depth(t), repr(t)))


def dag_encode(clauses, functions, predicates, constants=('d',), variable_slots=6):
    tags = setup(functions, constants, variable_slots)
    leaves = variable_slots+len(constants)
    node_width = width(leaves+len(functions))
    nodes = sorted_terms(constructors(clauses))
    refs = {'v'+str(i):i for i in range(variable_slots)}
    refs.update({(name,):variable_slots+i for i,name in enumerate(constants)})
    out = [gamma(len(nodes)+1)]
    dictionary_bits = 0
    for index, tree in enumerate(nodes):
        size = width(leaves+index)
        record = binary(tags[tree[0]], node_width)+''.join(binary(refs[t], size) for t in tree[1:])
        out.append(record); dictionary_bits += len(record)
        refs[tree] = leaves+index
    size = width(leaves+len(nodes))
    body = clause_encode(clauses, predicates, lambda t:binary(refs[t], size))
    out.append(body)
    return ''.join(out), {'constructor_records':len(nodes), 'header_bits':len(out[0]),
                         'dictionary_bits':dictionary_bits, 'clause_body_bits':len(body),
                         'final_reference_width':size}


def dag_decode(bits, functions, predicates, constants=('d',), variable_slots=6):
    reader = Reader(bits)
    count = reader.gamma()-1
    leaves = variable_slots+len(constants)
    node_width = width(leaves+len(functions))
    values = ['v'+str(i) for i in range(variable_slots)]+[(name,) for name in constants]
    for index in range(count):
        tag = reader.take(node_width)-leaves
        if not 0 <= tag < len(functions):
            raise ValueError('not a constructor opcode')
        name, arity = functions[tag]
        size = width(len(values))
        children = []
        for _ in range(arity):
            ref = reader.take(size)
            if ref >= len(values):
                raise ValueError('forward or invalid dictionary reference')
            children.append(values[ref])
        values.append((name,)+tuple(children))
    size = width(len(values))
    def term():
        ref = reader.take(size)
        if ref >= len(values):
            raise ValueError('invalid root reference')
        return values[ref]
    return clause_decode(reader, predicates, term)


def grammar_encode(clauses, functions, predicates, macros, constants=('d',), variable_slots=6):
    """Sparse shared-subtree grammar with exact headers and escape costs.

    For the ordinary four-bit alphabet, opcodes 0..14 stay unchanged.  Opcode
    15 followed by 0 denotes old opcode 15 (if present); opcode 15 followed by
    1 denotes a macro reference.  Thus the nine-function theory's H costs five
    opcode bits; all others cost four.  More generally the minimum fixed width
    covering variables, constants and functions determines the all-ones escape
    opcode.  This same rule handles the 17-opcode source44 two-constant control.
    A reference into k already defined macros uses ceil(log2(k)) index bits.
    A macro reference is selected only when strictly cheaper than expansion.
    """
    tags = setup(functions, constants, variable_slots)
    constant_tags = {name:variable_slots+i for i,name in enumerate(constants)}
    node_width = width(variable_slots+len(constants)+len(functions))
    escape = '1'*node_width
    escape_tag = (1 << node_width)-1
    ordered = sorted_terms(macros)
    known = {}
    def term(t):
        if isinstance(t, str):
            return binary(int(t[1:]), node_width)
        tag = constant_tags[t[0]] if len(t) == 1 else tags[t[0]]
        direct = (escape+'0' if tag == escape_tag else binary(tag, node_width))+''.join(term(x) for x in t[1:])
        if t in known:
            reference = escape+'1'+binary(known[t], width(len(known)))
            if len(reference) < len(direct):
                return reference
        return direct
    out = [gamma(len(ordered)+1)]
    for index, tree in enumerate(ordered):
        out.append(term(tree))
        known[tree] = index
    dictionary_bits = sum(len(part) for part in out[1:])
    body = clause_encode(clauses, predicates, term)
    out.append(body)
    return ''.join(out), {'macro_records':len(ordered), 'header_bits':len(out[0]),
                         'dictionary_bits':dictionary_bits, 'clause_body_bits':len(body),
                         'final_reference_width':width(len(ordered)) if ordered else 0,
                         'macro_trees':ordered}


def grammar_decode(bits, functions, predicates, constants=('d',), variable_slots=6):
    reader = Reader(bits)
    count = reader.gamma()-1
    known = []
    leaves = variable_slots+len(constants)
    node_width = width(leaves+len(functions))
    escape_tag = (1 << node_width)-1
    def term():
        tag = reader.take(node_width)
        if tag == escape_tag:
            if reader.take(1):
                if not known:
                    raise ValueError('macro reference before any definition')
                ref = reader.take(width(len(known)))
                if ref >= len(known):
                    raise ValueError('invalid macro reference')
                return known[ref]
        if tag < variable_slots:
            return 'v'+str(tag)
        if tag < leaves:
            return (constants[tag-variable_slots],)
        if not 0 <= tag-leaves < len(functions):
            raise ValueError('invalid constructor tag')
        name, arity = functions[tag-leaves]
        return (name,)+tuple(term() for _ in range(arity))
    for _ in range(count):
        known.append(term())
    return clause_decode(reader, predicates, term)


def choose_macros(clauses, functions, predicates, constants=('d',), variable_slots=6):
    candidates = sorted_terms(t for t,n in constructors(clauses).items() if n >= 2)
    chosen = set()
    payload, stats = grammar_encode(clauses, functions, predicates, chosen, constants, variable_slots)
    evaluations = 1
    steps = 0
    while True:
        best = None
        # Try every single add/remove move and accept the best strict bit gain.
        # Ties follow the fixed depth/repr ordering.  This terminates because
        # integer bit length strictly decreases; no global optimum is claimed.
        for candidate in candidates:
            trial = chosen ^ {candidate}
            bits, trial_stats = grammar_encode(clauses, functions, predicates, trial, constants, variable_slots)
            evaluations += 1
            if len(bits) < len(payload) and (best is None or len(bits) < len(best[1])):
                best = (trial, bits, trial_stats)
        if best is None:
            break
        chosen, payload, stats = best
        steps += 1
    stats['candidate_subtrees'] = len(candidates)
    stats['accepted_single_macro_moves'] = steps
    stats['payload_cost_evaluations'] = evaluations
    return payload, stats


def load_inputs():
    snapshot = json.loads(Path(__file__).with_name('source44-encoding-snapshot.json').read_text())
    def tuples(value):
        return tuple(tuples(x) for x in value) if isinstance(value, list) else value
    inputs = {}
    for name, data in snapshot['theories'].items():
        clauses = [[tuples(literal) for literal in clause] for clause in data['clauses']]
        inputs[name] = (clauses, snapshot['functions'], snapshot['predicates'], data['flat_bits'])
    functions = [f for f in K.FUNCS if f[0] != 'W']
    for extensional in (False, True):
        for complete in (False, True):
            name = ('FC14S' if extensional else 'FC13S')+('_complete' if complete else '_native')
            clauses = K.reduced_witness_clauses(extensional, True)+(K.equality_clauses(functions) if complete else [])
            inputs[name] = (clauses, functions, K.PREDICATES, len(K.pack(clauses)))
            name = ('FC14B' if extensional else 'FC13B')+('_complete' if complete else '_native')
            clauses = B.source_clauses(extensional)+(K.equality_clauses(functions) if complete else [])
            inputs[name] = (clauses, functions, K.PREDICATES, len(K.pack(clauses)))
    return inputs


def main():
    directory = Path(__file__).parent
    result = {'scope':'fully charged syntax codecs with known signatures; no compiled TM or state estimate',
              'renaming':'local bijections; reconstructed payload is alpha-equivalent to original clauses; audit maps outside payload',
              'search':'one forward exhaustive local renaming pass; sparse grammar strict single-macro coordinate descent',
              'metrics':{}}
    for name, (source, functions, predicates, expected_flat) in load_inputs().items():
        for policy in ('lexical', 'first_occurrence', 'greedy_dag'):
            clauses, maps, examined = renamed(source, policy)
            flat = flat_encode(clauses, functions, predicates)
            assert len(flat) == expected_flat
            assert flat_decode(flat, functions, predicates) == clauses
            dag, dstats = dag_encode(clauses, functions, predicates)
            grammar, gstats = choose_macros(clauses, functions, predicates)
            assert dag_decode(dag, functions, predicates) == clauses
            assert grammar_decode(grammar, functions, predicates) == clauses
            for decode, bits in ((dag_decode, dag), (grammar_decode, grammar)):
                for bad in (bits[:-1], bits+'0'):
                    try:
                        decode(bad, functions, predicates)
                    except ValueError:
                        pass
                    else:
                        raise AssertionError('malformed stream accepted')
            key = name+'__'+policy
            result['metrics'][key] = {'flat_bits':len(flat), 'dag_bits':len(dag),
                                      'grammar_bits':len(grammar), 'dag':dstats,
                                      'grammar':{k:v for k,v in gstats.items() if k != 'macro_trees'},
                                      'variable_maps_examined':examined}
            artifact = {'theory':name, 'renaming_policy':policy, 'functions':functions,
                        'predicates':predicates, 'variable_maps':maps,
                        'renamed_clauses':clauses, 'macro_trees':gstats['macro_trees']}
            (directory/(key+'.shared.json')).write_text(json.dumps(artifact, indent=2)+'\n')
            (directory/(key+'.dag.bits')).write_text(dag+'\n')
            (directory/(key+'.grammar.bits')).write_text(grammar+'\n')
    (directory/'shared-template-results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key:{k:data[k] for k in ('flat_bits','dag_bits','grammar_bits')}
                      for key,data in result['metrics'].items()}, indent=2))


if __name__ == '__main__':
    main()
