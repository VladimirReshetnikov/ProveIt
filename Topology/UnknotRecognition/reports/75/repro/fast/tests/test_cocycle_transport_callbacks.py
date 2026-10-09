"""Every callback position preserves validation-like cancellation objects."""
import unittest

from fastunknot.cocycle_transport import (
    cocycle_collapse_candidates, descend_cocycle, transport_cocycle,
)
from fastunknot.cocycle_transport_verify import verify_cocycle_transport
from fastunknot.normal_cocycle import rank_one_cocycle_seed, CocycleLimit
from fastunknot.normal_surface_geometry import NormalOrbitError
from fastunknot.pachner23 import pachner_23
from normal_orbit_research.fixtures import layered_torus


class CocycleCallbackTests(unittest.TestCase):
    def test_same_exception_object_at_every_callback_position(self):
        raw, _ = layered_torus(2)
        heights = rank_one_cocycle_seed(raw)['heights']
        move = pachner_23(raw, 0, 0)
        after = move['triangulation']
        result = transport_cocycle(raw, heights, after, move['certificate'])
        operations = [
            lambda check: verify_cocycle_transport(raw, heights, after, result['certificate'], check=check),
            lambda check: transport_cocycle(raw, heights, after, move['certificate'], check=check),
            lambda check: cocycle_collapse_candidates(after, result['heights'], check=check),
            lambda check: descend_cocycle(after, result['heights'], check=check),
        ]
        for operation in operations:
            count = [0]

            def tick():
                count[0] += 1

            operation(tick)
            total = count[0]
            for exception_type in (NormalOrbitError, ValueError, CocycleLimit, RuntimeError):
                for stop in range(1, total+1):
                    count[0] = 0
                    original = exception_type('cancelled at callback '+str(stop))

                    def cancel():
                        tick()
                        if count[0] == stop:
                            raise original

                    with self.assertRaises(exception_type) as caught:
                        operation(cancel)
                    self.assertIs(caught.exception, original)


if __name__ == '__main__':
    unittest.main()
