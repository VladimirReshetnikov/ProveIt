"""Focused final checks: source-wrapper cancellation and unit recurrence.

The all-t Fibonacci proof is symbolic in research/geometry_candidates.md;
the one fixture here checks its final implementation boundary.
"""

from pathlib import Path
import json
import sys

FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))

from fastunknot.diagram import Diagram, DiagramError
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_support_diagram import verify_diagram_ray_disk_certificate
from fastunknot.normal_surface_geometry import NormalOrbitError, _prepare, _coordinates
from fastunknot.normal_support_peeling import peel_support_ray
from fastunknot.normal_support_peeling_verify import verify_support_ray
from fastunknot.normal_ray_blocks import _primitive_peeling_rows
from fastunknot.normal_ray_blocks_verify import _rebuild_unit_primitive
from normal_orbit_research.fixtures import layered_torus


def exterior_cancellation():
    diagram = Diagram.from_braid(2, [1])
    raw = diagram_exterior(diagram)
    # The disc fields will not be reached: cancellation occurs in the
    # exterior check's row-validation loop, after its first callback.
    certificate = dict(schema="diagram-ray-disks-v1",
        input_pd=[list(row) for row in diagram.pd], triangulation=raw,
        coordinates=[], disc_certificate={})
    result = []
    for exception_type in (DiagramError, NormalOrbitError, ValueError):
        marker = exception_type("cancel inside exterior row validation")
        reached = [False]

        def check():
            frame = sys._getframe(1)
            while frame:
                if (frame.f_code.co_name == "verify_diagram_exterior"
                        and "row" in frame.f_locals):
                    reached[0] = True
                    raise marker
                frame = frame.f_back

        try:
            verify_diagram_ray_disk_certificate(diagram, certificate, check=check)
        except BaseException as exc:
            assert exc is marker
        else:
            raise AssertionError("source-wrapper cancellation did not propagate")
        assert reached[0]
        result.append(exception_type.__name__)
    return result


def unit_recurrence():
    raw, primitive = layered_torus(5)
    scalar = 2**4097 + 17
    source = [[scalar * value for value in row] for row in primitive]
    prepared = _prepare(raw, lambda: None)
    analysed = _coordinates(prepared, source, lambda: None)
    proof = peel_support_ray(prepared, analysed)
    assert proof is not None and verify_support_ray(prepared, analysed, proof)
    assert len(proof["steps"]) == 3 * len(primitive) - 1
    assert [value for row in source for value in row][proof["seed"]] == scalar
    assert _primitive_peeling_rows(prepared, analysed, proof) == primitive
    assert _rebuild_unit_primitive(prepared,
        [value for row in source for value in row], proof, lambda: None) == primitive
    return dict(tetrahedra=5, common_scalar_bits=scalar.bit_length(),
                steps=len(proof["steps"]), recovered_primitive_exactly=True)


if __name__ == "__main__":
    print(json.dumps(dict(status="PASS", exterior_cancellation=exterior_cancellation(),
                         unit_recurrence=unit_recurrence()), indent=2))
