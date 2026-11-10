"""Untrusted lexical-scope adapter for the inherited named derivation producer.

No checker imports this module.  The inherited numerical syntax, proof-tree
constructors, and positive/negative mathematical examples are preserved in
reference_producer.py, copied verbatim with attribution in provenance.json.
The only serialization change is lexical allocation: a major premise returns
to its caller's parameter scope.  Canonical contexts gain exactly one entry
at each continuation, hence the active floor is minus the context length.
"""
import json
from pathlib import Path
import reference_producer as inherited


class LexicalEmitter(inherited.Emitter):
    def __init__(self, allow_forbidden_compound_progress=False):
        super().__init__(allow_forbidden_compound_progress)
        self.maximum_depth = 0

    def allocate(self, name=None):
        super().allocate(name)
        self.maximum_depth = max(self.maximum_depth, -self.floor)

    def emit(self, proof, context):
        saved_floor, saved_parameters = self.floor, self.parameters.copy()
        self.floor = -len(context)
        try:
            return super().emit(proof, context)
        finally:
            self.floor, self.parameters = saved_floor, saved_parameters


def cases():
    inherited.Emitter = LexicalEmitter
    result = inherited.build_cases() + inherited.witness_boundary_cases()
    for case in result:
        case.pop('allocations', None)
        case['source'] = 'Inherited named derivation, re-emitted with lexical scope'
    # The formula below says that all positive numbers have one common value:
    # D(x,y).(I(y,0;u.S(x)) = y).  Its base is true, and its universal
    # conclusion is false in the standard model.  A forged witness that is
    # the as-yet-unallocated step parameter must therefore be rejected.
    result.append({
        'name': 'DI_fresh_witness_cannot_depend_on_step_parameter',
        'accept': False,
        'meaning': 'Reject a false paired formula obtained by choosing x=z in the y=S(z) subproof.',
        'packet': [[0, [[-1], 0, [-1]], 0, 0], [[], 0, 0, -1],
                   [0, 0, [[5, 0, [9]], 1]]],
        'source': 'New targeted freshness counterexample',
    })
    result.append({
        'name': 'free_numerical_parameter_in_computation_goal',
        'accept': False,
        'meaning': 'An undeclared parameter cannot occur in the public closed goal.',
        'packet': [[0, [0, -1, 0], 0, 0], [[0, -1, 0], -1]],
        'source': 'New targeted scope boundary',
    })
    return result


if __name__ == '__main__':
    output = {
        'format': 'Four-field generated-assumption packets with lexical scope',
        'scope': 'Examples and an untrusted serializer, not a formal verification',
        'cases': cases(),
    }
    path = Path(__file__).with_name('cases.json')
    path.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps({'cases': len(output['cases']),
                      'positive': sum(x['accept'] for x in output['cases'])}))
