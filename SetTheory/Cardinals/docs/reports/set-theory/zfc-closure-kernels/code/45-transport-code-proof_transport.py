#!/usr/bin/env python3
"""Translate source-28 certificates to the two-operation complete kernel.

This is an OFF-MACHINE completeness witness. The target proof checker never
computes a live set and does not execute this compiler. It enumerates/checks
the resulting primitive up/fused_down lines directly.
"""
from __future__ import annotations

from copy import deepcopy

import name_transport as transport
import two_kernel as new
from vendor import four_kernel as old

OLD_TO_LETTER = {'up': 's', 'down': 'S', 'swap': 't', 'contract': 'k'}
LETTER_TO_NEW = {'u': 'up', 'w': 'fused_down'}


def translate(certificate: dict, theory=()):
    """Return a checked equivalent certificate and its line correspondence.

    In the full expanded proof, the exact formula at each old line equals
    the formula at its corresponding new line, including names and binders.
    Closed formulas need no identity instruction: an old identity renaming
    can point to its earlier unchanged line.
    """
    theory = tuple(theory)
    old_lines = old.check_certificate(certificate, theory)
    instructions, line_map, trace = [], [], []
    for index, instruction in enumerate(certificate['instructions']):
        op = instruction['op']
        if op in OLD_TO_LETTER:
            source = instruction['line']
            live = old.free_names(old_lines[source])
            word3 = transport.compile_four(OLD_TO_LETTER[op], live)
            word2 = transport.compile_three_to_two(word3, live)
            current = line_map[source]
            for letter in word2:
                instructions.append({'op': LETTER_TO_NEW[letter], 'line': current})
                current = len(instructions) - 1
            line_map.append(current)
            trace.append({'old_line': index, 'old_op': op,
                          'live': sorted(live), 'new_word': word2,
                          'new_line': current})
        else:
            copied = deepcopy(instruction)
            keys = ('line',) if op == 'gen' else ('implication', 'antecedent') if op == 'mp' else ()
            for key in keys:
                copied[key] = line_map[copied[key]]
            instructions.append(copied)
            line_map.append(len(instructions) - 1)

    result = {'instructions': instructions}
    # A final identity renaming can correspond to a nonfinal target line.
    # Truncation is valid because all line references are strictly backward.
    if old_lines:
        result['instructions'] = instructions[:line_map[-1] + 1]
        result['conclusion'] = old_lines[-1]
    new_lines = new.check_certificate({'instructions': instructions}, theory)
    for i, target in enumerate(line_map):
        if old_lines[i] != new_lines[target]:
            raise AssertionError('proof transport changed an exact formula')
    new.check_certificate(result, theory)
    return result, {'old_lines': len(old_lines),
                    'expanded_lines': len(instructions),
                    'new_lines': len(result['instructions']),
                    'line_map_scope': 'full expanded proof, before final truncation',
                    'line_map': line_map, 'renaming_trace': trace}


def reverse_translate(certificate: dict, theory=()):
    """Translate new certificates back to the old four-map kernel.

    This supplies the reverse finite syntactic witness, independent of a
    semantic soundness invocation. Its support calculation also occurs only
    in this off-machine proof transformer.
    """
    theory = tuple(theory)
    source_lines = new.check_certificate(certificate, theory)
    instructions, correspondence = [], []
    for instruction in certificate['instructions']:
        op = instruction['op']
        if op in new.RENAMINGS:
            source = instruction['line']
            live = new.free_names(source_lines[source])
            word = (['up'] if op == 'up' else old.factor_on_support(
                {x: new.name_step(op, x) for x in live}))
            current = correspondence[source]
            for letter in word:
                instructions.append({'op': letter, 'line': current})
                current = len(instructions) - 1
            correspondence.append(current)
        else:
            copied = deepcopy(instruction)
            keys = ('line',) if op == 'gen' else ('implication', 'antecedent') if op == 'mp' else ()
            for key in keys:
                copied[key] = correspondence[copied[key]]
            instructions.append(copied)
            correspondence.append(len(instructions) - 1)
    expanded = old.check_certificate({'instructions': instructions}, theory)
    require = all(source_lines[i] == expanded[j] for i, j in enumerate(correspondence))
    if not require:
        raise AssertionError('reverse proof transport changed an exact formula')
    result = {'instructions': instructions}
    if source_lines:
        result['instructions'] = instructions[:correspondence[-1] + 1]
        result['conclusion'] = source_lines[-1]
    old.check_certificate(result, theory)
    return result


if __name__ == '__main__':
    import json
    old_cert = old.make_ui_certificate(old.source19_body(), 0)
    cert, audit = translate(old_cert)
    print(json.dumps({'certificate': cert, 'audit': audit}, indent=2))
