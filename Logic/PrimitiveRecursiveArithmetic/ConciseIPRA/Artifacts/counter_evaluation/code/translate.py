"""Checked finite proof translations between the matched counter calculi.

Forward replaces successor computation and one-term transport by CounterEval.
Reverse replaces CounterEval by successor computation and one-term transport.
Both translations preserve the end sequent literally, including open contexts.
This module is not a dependency of either standalone acceptance module.

Command line: python3 translate.py forward|reverse INPUT.json OUTPUT.json
"""
from __future__ import annotations
import importlib.util
import json
from pathlib import Path
import sys

from proof_macros import (R, S, P, proof, refl, computation, transport, lift)

HERE = Path(__file__).resolve().parent
CODE = HERE if (HERE / 'counter_eval.py').exists() else HERE.parent / 'counter_candidate'


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


new = load('counter_evaluation_translator_target', CODE / 'counter_eval.py')
old = load('counter_transport_translator_source', CODE / 'control_counter_transport.py')


def old_refl(a):
    step = ['r', a, 0, 2]
    return ['x', 1, step, step]


def old_symmetry(p, source):
    return ['x', 1, old_refl(source), p]


def old_transitivity(p, q, source):
    return ['x', 1, q, old_symmetry(p, source)]


def walk(p, context, scope, forward):
    source = old if forward else new
    tag = p[0]
    if tag == 'r':
        return computation(*p[1:])[1] if forward else old_refl(p[1])
    if forward and tag == 'x':
        h, major, minor = p[1:]
        q = proof(old.derive(major, context, scope), walk(major, context, scope, True))
        r = proof(old.derive(minor, context, scope), walk(minor, context, scope, True))
        return transport(h, q, r)[1]
    if not forward and tag == 'v':
        major, minor = p[1:]
        s, t = new.derive(major, context, scope)
        b, r = new.derive(minor, context, scope)
        counter, a, h = b
        if counter != S(s):
            raise ValueError('invalid CounterEval source')
        q = walk(major, context, scope, False)
        v = walk(minor, context, scope, False)
        template = R(S(1), lift(a, 1), lift(h, 1, 2))
        replace_counter = ['x', template, q, v]
        compute = ['r', t, a, h]
        return old_transitivity(replace_counter, compute, r)
    if tag == 'u':
        return ['u', p[1], p[2], walk(p[3], context, scope, forward)]
    if tag in ('e', 'i'):
        goal, data, branch = p[1:]
        fresh = -scope - 1
        if tag == 'e':
            paired = source.derive(data, context, scope)
            body = source.opening(paired[0], fresh, 1)
            clause = (source.opening(body, 0), body)
            data_new = walk(data, context, scope, forward)
        else:
            body = source.opening(goal[0], data, 1)
            eta = fresh if len(goal[0]) == 2 and data == 0 else 0
            clause = ([0, 0], source.opening(body, eta))
            data_new = data
        return [tag, goal, data_new, walk(branch, context + [clause], scope + 1, forward)]
    raise ValueError('unknown source rule')


def translate_proof(p, context=(), scope=0, forward=True):
    """Check and translate an open proof tree under the supplied same context."""
    source, target = (old, new) if forward else (new, old)
    end = source.derive(p, list(context), scope)
    converted = walk(p, list(context), scope, forward)
    if target.derive(converted, list(context), scope) != end:
        raise ValueError('translation changed the end sequent')
    return converted


def translate(certificate, forward=True):
    """Translate one closed public certificate after checking both endpoints."""
    source, target = (old, new) if forward else (new, old)
    source.verify(certificate)
    result = {'goal': certificate['goal'],
              'proof': translate_proof(certificate['proof'], forward=forward)}
    target.verify(result)
    return result


if __name__ == '__main__':
    if len(sys.argv) != 4 or sys.argv[1] not in ('forward', 'reverse'):
        raise SystemExit('usage: translate.py forward|reverse INPUT.json OUTPUT.json')
    data = json.loads(Path(sys.argv[2]).read_text())
    result = translate(data, sys.argv[1] == 'forward')
    Path(sys.argv[3]).write_text(json.dumps(result, indent=2) + '\n')
