"""Finite prototype checks; not a formal soundness or completeness proof."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parents[1] / 'tests/producer.py'
spec = importlib.util.spec_from_file_location('upstream_producer', SOURCE)
p = importlib.util.module_from_spec(spec)
sys.dont_write_bytecode = True
spec.loader.exec_module(p)

class Emitter(p.Emitter):
    def emit(self, proof, context):
        goal = self.formula(proof['goal'])
        if goal in context:
            self.instructions.append(context.index(goal))
            return
        rule = proof['rule']
        old = self.floor
        if rule == 'Computation':
            _, source, rhs = proof['goal']
            counter, seed, update = self.term(source)
            self.instructions.append([0, counter[0] if counter else 0, seed, update])
        elif rule in ('Tr', 'QE'):
            template = self.formula(proof['motive'], hole=proof['variable']) if rule == 'Tr' else 0
            target = self.term(proof['target']) if rule == 'QE' else 0
            self.instructions.append([1, 0, target, template])
            self.emit(proof['major'], context)
            self.emit(proof['minor'], context)
        elif rule == 'DI':
            self.instructions.append([0 if proof['mode'] == 'progress' else [], goal, 0, self.term(proof['witness'])])
            self.allocate(proof['eigen'])
            _, x, y, body = proof['goal']
            opened = p.substitute(body, x, proof['witness'])
            local = p.substitute(opened, y, p.V(proof['eigen']) if proof['mode'] == 'progress' else 0)
            self.emit(proof['premise'], context + [self.formula(local)])
            del self.parameters[proof['eigen']]
        elif rule == 'DE':
            self.instructions.append([1, 0, 0, 0])
            self.emit(proof['major'], context)
            self.allocate(proof['eigen'])
            _, x, y, body = proof['major']['goal']
            local = p.Q(y, p.substitute(body, x, p.V(proof['eigen'])))
            self.emit(proof['continuation'], context + [self.formula(local)])
            del self.parameters[proof['eigen']]
        else:
            raise ValueError(rule)
        self.floor = old

    def packet(self, proof):
        proof = p.expand_proof(proof)
        goal = self.formula(proof['goal'])
        self.emit(proof, [])
        return list(reversed(self.instructions)) + [goal]

proofs = [
    ('I0_one', p.compute(p.I(0, p.ONE, 'u', 0))),
    ('I0_zero_repaired', p.compute(p.I(0, 0, 'u', 0))),
    ('IS_update', p.compute(p.I(p.TWO, p.ONE, 'u', p.S(p.V('u'))))),
    ('reflexivity_zero', p.reflexivity(0)),
    ('reflexivity_iterator', p.reflexivity(p.I(p.TWO, p.ONE, 'u', p.S(p.V('u'))))),
    ('identity_closure', p.identity_closure()),
    ('nested_identity_closure', p.nested_identity_closure()),
    ('nonvacuous_elimination', p.nonvacuous_elimination()),
]
cases = [dict(name=n, packet=Emitter().packet(proof), accept=True) for n, proof in proofs]
for row in cases[:]:
    cases.append(dict(name='false_goal_' + row['name'], packet=row['packet'][:-1] + [[0, [0]]], accept=False))
cases += [
    dict(name='unallocated_goal', packet=[[-1, -1]], accept=False),
    dict(name='unproved_major', packet=[[1,0,0,0], [0, [0]]], accept=False),
    dict(name='bad_hypothesis', packet=[0, [0, [0]]], accept=False),
]
results = []
for checker in ('synth_checker.py', 'synth_compact.py'):
    for optimized in (False, True):
        for case in cases:
            command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT/checker)]
            run = subprocess.run(command, input=json.dumps(case['packet']), text=True, capture_output=True, timeout=5)
            accepted = run.returncode == 0 and run.stdout == 'ACCEPT\n'
            results.append(dict(checker=checker, optimized=optimized, name=case['name'], expected=case['accept'], actual=accepted, passed=accepted==case['accept'], error=run.stderr[-500:] if accepted!=case['accept'] else None))
output = dict(cases=cases, checks=len(results), failures=[r for r in results if not r['passed']], results=results, scope='Finite prototype checks only, not certified checker equivalence.')
(ROOT/'prototype_receipt.json').write_text(json.dumps(output, indent=2)+'\n')
print(json.dumps({k:v for k,v in output.items() if k not in ('cases','results')},indent=2))

if output['failures']:
    raise SystemExit(1)
