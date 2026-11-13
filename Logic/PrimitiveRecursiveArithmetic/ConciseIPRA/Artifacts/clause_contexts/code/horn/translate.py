"""Untrusted translations between the pinned Step calculus and Horn contexts.

Both public entry points validate the input and the output independently.
The recursive routines carry the kind of each introduced source clause:
True denotes a discharged ordinary assumption, False a D-elimination clause.
The Horn target additionally has a fixed initial reflexivity clause at index 0.
"""
import importlib.util
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


control = load('pinned_step', ROOT / 'reference' / 'control.py')
horn = load('horn_step', ROOT / 'checker.py')


def forward(proof, kinds=()):
    match proof:
        case ['r', term]:
            return ['u', 0, term, []]
        case ['x', major, minor]:
            return ['x', forward(major, kinds), forward(minor, kinds)]
        case ['u', index, witness, premise]:
            premises = [] if kinds[index] else [forward(premise, kinds)]
            return ['u', index + 1, witness, premises]
        case ['e', goal, major, branch]:
            return ['e', goal, forward(major, kinds), forward(branch, kinds + (False,))]
        case ['i', goal, witness, branch]:
            return ['i', goal, witness, forward(branch, kinds + (True,))]
    raise ValueError('Malformed source proof')


def backward(proof, kinds=()):
    match proof:
        case ['u', 0, witness, []]:
            return ['r', witness]
        case ['x', major, minor]:
            return ['x', backward(major, kinds), backward(minor, kinds)]
        case ['u', index, witness, premises]:
            premise = ['r', 0] if kinds[index - 1] else backward(premises[0], kinds)
            return ['u', index - 1, witness, premise]
        case ['e', goal, major, branch]:
            return ['e', goal, backward(major, kinds), backward(branch, kinds + (False,))]
        case ['i', goal, witness, branch]:
            return ['i', goal, witness, backward(branch, kinds + (True,))]
    raise ValueError('Malformed Horn proof')


def to_horn(certificate):
    control.verify(certificate)
    result = {'goal': certificate['goal'], 'proof': forward(certificate['proof'])}
    horn.verify(result)
    return result


def to_control(certificate):
    horn.verify(certificate)
    result = {'goal': certificate['goal'], 'proof': backward(certificate['proof'])}
    control.verify(result)
    return result


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in ('forward', 'backward'):
        raise SystemExit('usage: python translate.py forward|backward < certificate.json')
    translated = (to_horn if sys.argv[1] == 'forward' else to_control)(json.load(sys.stdin))
    json.dump(translated, sys.stdout, separators=(',', ':'))
    print()
