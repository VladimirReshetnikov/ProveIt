"""Independent bounded audit of the strict kernels and proof translations."""
import importlib.util
import json
import pathlib
import sys
from copy import deepcopy

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'code'))
import strict_old
import strict_q
from translate import counts, map_proof, translate

Z = ['z']
V = lambda n: ['v', n]
S = lambda a: ['s', a]
E = lambda a, b: ['e', a, b]
Q = lambda a: ['q', a]
D = lambda a: ['d', a]
rejected = 0
translations = 0


def reject(module, document):
    global rejected
    try:
        module.check(document)
    except (ValueError, TypeError, IndexError, KeyError):
        rejected += 1
    else:
        raise RuntimeError('Invalid input accepted: ' + repr(document))


def cert(module, proof, scope=0, context=None):
    context = [] if context is None else context
    return dict(parameters=scope, context=context,
                goal=module.derive(proof, context, scope), proof=proof)


for module in (strict_old, strict_q):
    basic = cert(module, ['zero', S(Z), V(0)])
    for bad in (False, True, -1, 0.0, None, [], {}, '0'):
        d = deepcopy(basic)
        d['parameters'] = bad
        reject(module, d)
    for bad in (None, False, 0, {}, 'context'):
        d = deepcopy(basic)
        d['context'] = bad
        reject(module, d)
    for bad in (False, True, -1, 0.0, None, [], {}, '0', 100):
        d = deepcopy(basic)
        d['proof'][2] = V(bad)
        reject(module, d)
    for bad in (None, False, True, -1, 0.0, [], {}, 'unknown'):
        d = deepcopy(basic)
        d['proof'][0] = bad
        reject(module, d)
    for bad in ([], ['z', 0], ['s'], ['s', Z, Z], ['i', Z, Z],
                ['i', Z, Z, V(0), Z], ['e', Z, Z], ['q', E(Z,Z)],
                [True], ['v', 0], ['v', False], ['v', 0, 0]):
        d = deepcopy(basic)
        d['proof'][1] = bad
        reject(module, d)
    for bad in ([], ['e', Z], ['e', Z, Z, Z], ['q', E(Z,Z), E(Z,Z)],
                ['d', E(Z,Z), E(Z,Z)], ['v', 0], Z, ['s', Z],
                ['e', ['v', 0], Z], ['e', ['v', False], Z]):
        d = deepcopy(basic)
        d['context'] = [bad]
        reject(module, d)
    for bad in (False, True, -1, 0.0, None, [], {}, 1):
        d = dict(parameters=0, context=[E(Z,Z)], goal=E(Z,Z), proof=['hyp', bad])
        reject(module, d)
    for proof in (['zero'], ['zero', Z], ['zero', Z, Z, Z],
                  ['succ', Z, Z], ['succ', Z, Z, Z, Z], ['hyp', 0, 0],
                  ['tr'], ['qe'], ['de'], ['case'], ['prog']):
        d = deepcopy(basic)
        d['proof'] = proof
        reject(module, d)

# Explicit freshness attacks: witness cannot use the new branch parameter;
# a preexisting parameter hypothesis cannot become the fresh induction one.
for module in (strict_old, strict_q):
    reject(module, dict(parameters=0, context=[], goal=D(E(V(0), V(0))),
                        proof=['case', E(V(0),V(0)), V(0), ['hyp',0]]))
reject(strict_q, dict(parameters=1, context=[E(V(0), Z)], goal=Q(E(V(0),Z)),
                       proof=['prog', E(V(0),Z), ['hyp',1]]))

# Round trips under nested case/DE/transport contexts, using proofs with a
# free parameter so that every weakening must adjust indices correctly.
files = [
    ('old', 'old_parameter_progress_old.json'),
    ('q', 'q_progress_with_context_q.json'),
]
for label, filename in files:
    source = strict_old if label == 'old' else strict_q
    target = strict_q if label == 'old' else strict_old
    direction = 'old-to-q' if label == 'old' else 'q-to-old'
    inverse = 'q-to-old' if label == 'old' else 'old-to-q'
    original = json.loads((ROOT / 'tests/certificates' / filename).read_text())
    proof, scope, context = original['proof'], original['parameters'], original['context']
    for depth in range(9):
        document = cert(source, proof, scope, context)
        source.check(document)
        converted = translate(document, direction)
        target.check(converted)
        roundtrip = translate(converted, inverse)
        source.check(roundtrip)
        n, r = counts(proof)
        n2, _ = counts(converted['proof'])
        assert n2 == n + (3 if label == 'old' else 2) * r
        assert converted['goal'] == document['goal'] == roundtrip['goal']
        translations += 2
        goal = document['goal']
        weakened = map_proof(proof, lambda n: V(n+1), lambda n: n+1)
        matrix = source.shift(goal, 2)
        paired = ['case', matrix, Z, weakened]
        # The major's fresh closure is actually consumed by QE.
        branch = ['qe', Z, ['hyp',0], weakened]
        proof = ['de', goal, paired, branch]

receipt = dict(malformed_and_scope_rejections=rejected,
               nested_translation_and_roundtrip_checks=translations,
               failures=0,
               scope='Bounded independent tests; not formal verification.')
(ROOT / 'evidence/strict_malformed_audit.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
