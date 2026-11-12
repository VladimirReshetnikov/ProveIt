"""Untrusted named-proof compiler for the public zero alias.

No proof checker imports this file.  The named producer and zero-source
normalizer are attributed, pinned upstream files under ref/source_dispatch.
"""
from pathlib import Path
import copy
import importlib.util
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.setrecursionlimit(20000)

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module

P = load('native_producer', ROOT / 'ref/source_dispatch/tests/native_producer.py')
N = load('alias_normalizer', ROOT / 'ref/source_dispatch/tests/normalizer.py')
CNAME = '_PUBLIC_ZERO_ALIAS_'
C = P.V(CNAME)
AXIOM = P.Eq(C, 0)

_old_zero_symmetry = N.zero_symmetry
def zero_symmetry(proof):
    # This is a proof under a stated hypothesis, not an unchecked new rule.
    if proof['goal'] == P.Eq(0, C):
        return P.hyp(AXIOM)
    return _old_zero_symmetry(proof)
N.zero_symmetry = zero_symmetry

def replace_zero(tree, value):
    """Replace the numerical constant only; leave binder names intact."""
    if tree == 0:
        return value
    tag = tree[0]
    if tag == 'v':
        return tree
    if tag == 's':
        return P.S(replace_zero(tree[1], value))
    if tag == 'i':
        _, n, a, u, h = tree
        return P.I(replace_zero(n, value), replace_zero(a, value), u,
                   replace_zero(h, value))
    if tag == 'eq':
        return P.Eq(replace_zero(tree[1], value), replace_zero(tree[2], value))
    if tag == 'q':
        return P.Q(tree[1], replace_zero(tree[2], value))
    if tag == 'd':
        return P.D(tree[1], tree[2], replace_zero(tree[3], value))
    raise ValueError(tag)

def alias_proof(proof):
    """Compile formula Leibniz, including both binders, using c=0."""
    hole = N.fresh('_alias_template')
    motive = replace_zero(proof['goal'], P.V(hole))
    reverse = P.symmetry(P.hyp(AXIOM), N.fresh('_alias_reverse'))
    translated = N.full_transport(reverse, hole, motive, proof)
    translated = N.eliminate_zero_sources(translated)
    if translated['goal'] != replace_zero(proof['goal'], C):
        raise AssertionError('Wrong public goal')
    audit = N.audit(translated)
    if audit['forbidden_zero_sources']:
        raise AssertionError(audit)
    return translated

class AliasEmitter(P.Emitter):
    def __init__(self):
        super().__init__()
        self.parameters[CNAME] = 1

    def packet(self, proof):
        proof = P.expand_proof(proof)
        goal = self.formula(proof['goal'])
        self.emit(proof, [0, [1, 0]])
        instructions = copy.deepcopy(self.instructions)
        for packet in instructions:
            if packet[0] == []:
                packet[0] = 0
            for j, item in enumerate(packet):
                if item is None:
                    packet[j] = 0
        return list(reversed(instructions)) + [goal]

def nested_reflexivity():
    x, y, z, w, u = '_nx', '_ny', '_nz', '_nw', '_nu'
    e, f = '_ne', '_nf'
    t = P.I(P.V(y), 0, u, P.V(x))
    goal = P.D(x, y, P.D(z, w, P.Eq(t, t)))
    inner = P.substitute(P.substitute(goal[3], x, 0), y, P.S(P.V(e)))
    term = inner[3][1]
    inner_proof = P.introduction(inner, 0, f, 'progress',
                                 P.reflexivity(term, '_nested_refl'))
    return P.introduction(goal, 0, e, 'case', inner_proof)

def build():
    u = '_state'
    seeds = [
        ('zero_computation', P.compute(P.I(0, P.TWO, u, P.S(P.V(u))))),
        ('successor_computation', P.compute(P.I(P.ONE, P.ONE, u, P.S(P.V(u))))),
        ('reflexivity', P.reflexivity(P.TWO, '_refl')),
        ('induction_uses_hypothesis', P.identity_closure('_ind')['major']),
        ('nested_D_transport', nested_reflexivity()),
        ('nonvacuous_witness', P.nonvacuous_elimination()),
    ]
    out = ROOT / 'fixtures' / 'generated'
    out.mkdir(parents=True, exist_ok=True)
    manifest = []
    for name, original in seeds:
        proof = alias_proof(original)
        emitter = AliasEmitter()
        packet = emitter.packet(proof)
        path = out / (name + '.json')
        path.write_text(json.dumps(packet, separators=(',', ':')) + '\n')
        manifest.append(dict(name=name, file=str(path.relative_to(ROOT)),
                             expected=True, instructions=len(packet)-1,
                             original_goal=original['goal'],
                             public_goal=proof['goal'],
                             proof_audit=N.audit(proof)))
    # This proof is built directly with c as the numerical term.
    direct = P.reflexivity(C, '_constant_refl')
    packet = AliasEmitter().packet(direct)
    path = out / 'public_zero_reflexivity.json'
    path.write_text(json.dumps(packet, separators=(',', ':')) + '\n')
    manifest.append(dict(name='public_zero_reflexivity',
                         file=str(path.relative_to(ROOT)), expected=True,
                         instructions=len(packet)-1, public_goal=direct['goal']))
    (ROOT / 'generated_cases.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps([{k: v for k, v in row.items() if k not in
                      ('original_goal', 'public_goal', 'proof_audit')}
                     for row in manifest], indent=2))

if __name__ == '__main__':
    build()
