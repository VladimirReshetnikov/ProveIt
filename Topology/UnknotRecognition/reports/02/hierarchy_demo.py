"""Demonstrate the implemented hierarchy components, not a full hierarchy."""
import json
from unknotlab.normal import one_tetrahedron_solid_torus
from unknotlab.pattern import BallPattern
from unknotlab.potential import HierarchyBudget

t = one_tetrahedron_solid_torus()
c = t.rational_cohomology_basis()[0]
p = BallPattern.from_dual_triangles([(0, 2, 1), (0, 1, 3), (0, 3, 2), (1, 2, 3)])
b = HierarchyBudget(2, 2)
print(json.dumps({'surface': t.dual_surface(c).as_json(),
                  'ball_pattern': p.test_essential().as_json(),
                  'potential_example': {'before': [1, 0], 'after': [0, 2],
                                        'base': b.base,
                                        'drop': b.verify_replacement([1, 0], [0, 2], 0)},
                  'full_hierarchy_implemented': False}, indent=2))
