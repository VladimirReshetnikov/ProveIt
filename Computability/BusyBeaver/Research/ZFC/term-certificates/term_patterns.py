"""Top-down fixed-pattern verifier for exact C254 term certificates.

Trusted finite circuits encode the pattern DAG; per-certificate constructor IDs
and per-row constructor values arrays are absent. The iterative matcher expands
shared trusted pattern nodes as needed. Candidate data never supplies a pattern.
No term denotation arithmetic, global arena uniqueness or constructor search.
"""
import term_circuits as C

FORMAT = 'term-c254-pattern-v1'
ARITY = C.ARITY
load_templates = C.load_templates


def match_pattern(nodes, out, args, pattern, stats):
    """Compare a root with one trusted DAG pattern using an explicit work stack.

    Slots below arity are exact parameter IDs; slot arity is literal Z. A zero
    actual node at an expected tag0 is the virtual normalized B0(0,0). Positive
    expected tags reject Z. Fixed circuits have backward wires, so every call
    terminates independently of candidate denotation size and depth.
    """
    pending = [(pattern.root, out)]
    while pending:
        stats['max_pending_obligations'] = max(stats['max_pending_obligations'], len(pending))
        expected, actual = pending.pop()
        stats['pattern_visits'] += 1
        if expected < pattern.arity:
            stats['parameter_checks'] += 1
            if actual != args[expected]:
                return False
        elif expected == pattern.arity:
            stats['literal_zero_checks'] += 1
            if actual != 0:
                return False
        else:
            tag, left, right = pattern.steps[expected-pattern.arity-1]
            stats['pattern_constructor_checks'] += 1
            if actual == 0:
                if tag != 0:
                    return False
                stats['virtual_zero_constructors'] += 1
                actual_left = actual_right = 0
            else:
                record = nodes[actual]
                if record[1] != tag:
                    return False
                actual_left, actual_right = record[2], record[3]
            pending.append((right, actual_right))
            pending.append((left, actual_left))
    return True


def verify_certificate(cert, templates, goal=None, *, stats=None):
    """All12 exact rules, both path gates; default endpoint is fixed falsity.

    templates and optional positive-control goal are trusted caller resources.
    Input constructor_ids are rejected; neither they nor a values array occurs
    in this protocol. Resource exceptions propagate, not logical rejection.
    """
    if stats is None:
        stats = {}
    stats.update(node_records=0, constructor_checks=0, pattern_visits=0,
                 pattern_constructor_checks=0, parameter_checks=0,
                 literal_zero_checks=0, virtual_zero_constructors=0,
                 max_pending_obligations=0, path_edges=0, proof_rows=0,
                 template_searches=0, arena_uniqueness_comparisons=0, reason=None)
    try:
        C.require(type(cert) is dict and cert.get('format') == FORMAT, 'format')
        nodes = cert['nodes']
        C.validate_nodes(nodes, stats)
        if goal is not None:
            C.require(type(goal) is int and 0 <= goal < len(nodes), 'control_goal')
        rows = cert['proof_rows']
        C.require(type(rows) is list, 'proof_list')
        formulas = []
        for i, row in enumerate(rows):
            stats['proof_rows'] += 1
            C.require(type(row) is dict, 'proof_row')
            tag, args, children, out = row['tag'], row['args'], row['children'], row['formula']
            C.require(type(tag) is int and 0 <= tag < 12, 'proof_tag')
            fields = {'tag','args','children','formula'}
            if tag == 11:
                fields.add('gate_paths')
            C.require(set(row) == fields, 'row_fields')
            C.require(type(args) is list and len(args) == ARITY[tag], 'proof_arity')
            C.require(all(type(j) is int and 0 <= j < len(nodes) for j in args), 'argument')
            C.require(type(out) is int and 0 <= out < len(nodes), 'claimed_formula')
            C.require(type(children) is list and len(children) ==
                      (2 if tag == 1 else 1 if tag == 2 else 0), 'premise_arity')
            C.require(all(type(j) is int and 0 <= j < i for j in children), 'premise_reference')
            if tag == 0:
                C.require(out == 0, 'truth')
            elif tag == 1:
                C.require(out == args[0], 'mp_conclusion')
                C.require(C.constructor(nodes, formulas[children[1]], 0,
                                        formulas[children[0]], out, stats), 'mp_major')
            elif tag == 2:
                C.require(C.constructor(nodes, out, 2, args[0], formulas[children[0]], stats), 'gen')
            else:
                if tag == 11:
                    paths = row['gate_paths']
                    C.require(type(paths) is list and len(paths) == 2, 'gate_witness_arity')
                    C.require(C.distinguish(nodes, args[2], args[0], paths[0], stats), 'bundle_gate_1')
                    C.require(C.distinguish(nodes, args[2], args[1], paths[1], stats), 'bundle_gate_2')
                C.require(match_pattern(nodes, out, args, templates[tag], stats), 'fixed_pattern')
            formulas.append(out)
        C.require(bool(formulas), 'empty_proof')
        C.require(formulas[-1] == goal if goal is not None else C.is_falsity(nodes, formulas[-1]),
                  'fixed_or_control_endpoint')
        return True
    except (C.Invalid, ValueError, TypeError, KeyError, IndexError) as error:
        stats['reason'] = str(error)
        return False
