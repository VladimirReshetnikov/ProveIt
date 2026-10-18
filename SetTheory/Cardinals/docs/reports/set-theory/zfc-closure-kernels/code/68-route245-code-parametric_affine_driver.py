#!/usr/bin/env python3
"""Generalize only the uniform frame padding of the inherited affine audit.

The complete-path arithmetic, guards, rule counts, target construction, and
all 8391 obligations are preserved.  Matching source and target affine gaps
are n + padding - len(path), with the same universally quantified n >= 0.
"""
from collections import Counter
from review_affine_source import full_inc, full_strip


def check_sites(affine, table, sites, padding):
    assert type(padding) is int and padding >= max(len(p) for p,op,r in sites)
    assert affine.PADDING == padding
    case_counts, rule_counts = Counter(), Counter()
    minimum = 10**9
    full_path_cases, max_rules, overflow_cases = 0, 0, 0
    for p, op, r in sites:
        assert len(p) <= padding
        for zero in ((True, False) if op == "CD" else (None,)):
            branch = (r, zero) if op == "CD" else None
            extra, effect, overflow = 0, None, False
            if op == "CI":
                successor, overflow = full_inc(p)
                effect = "inc", r
            elif op == "CD" and not zero:
                successor, overflow = full_inc(p)
                effect, extra = ("dec", r), 1
            elif op == "CD":
                successor, overflow = full_inc(full_strip(p, "0", 1))
            elif op == "CB":
                successor, overflow = full_inc(full_strip(p, "0", r))
            elif op == "CC":
                successor = full_strip(p, "1", r)
            else:
                assert op == "CH"
                successor = ""
            constant_gap = padding + extra + int(overflow) - len(successor)
            assert constant_gap >= 0
            right = ([('b', int(b)) for b in successor] +
                     [('r', 0, 1, constant_gap), ('b', 1),
                      ('box', ('plain', effect))])
            rules, literal = affine.run(table, p, branch,
                affine.canon([('b', 1)], right), halt=(op == "CH"), fuel=1000)
            assert literal > 0
            key = op + ("/zero" if zero else "/positive") if op == "CD" else op
            case_counts[key] += 1
            rule_counts.update(rules)
            minimum, max_rules = min(minimum, literal), max(max_rules, sum(rules.values()))
            full_path_cases += 1
            overflow_cases += int(overflow)
    assert full_path_cases == 8391
    return dict(padding=padding, cases=full_path_cases, by_operation=dict(case_counts),
                target_paths_keep_all_overflow_and_trailing_zero_cells=True,
                overflow_cases=overflow_cases, minimum_literal_steps=minimum,
                max_rules=max_rules, rule_counts=dict(rule_counts))
