"""Binary transport, bounded work and exact ordered-point cover comparison."""
from contextlib import redirect_stdout, redirect_stderr
import copy
import io
import json
from pathlib import Path
import tempfile
import unittest

from cover_research.audit_markings import audit
from fastunknot.integer_codec import encoded_integer, json_safe
from fastunknot.surface_cover import CoverIndex, classify_cover, main


def example(n, maps, *, orientable=True, genus=0):
    return dict(surface=dict(orientable=orientable, genus=genus,
                             boundary_components=len(maps)-(2*genus if orientable else genus)+1),
                sheets=n, monodromy=[dict(sign=s, shift=a) for s, a in maps])


class SurfaceCoverProductionTests(unittest.TestCase):
    def test_all_small_markings_against_literal_bijections(self):
        result = audit()
        self.assertEqual(result['presentations'], 364)
        self.assertGreater(result['marked_comparisons'], 100000)
        print('Independent marked-cover audit:', json.dumps(result, sort_keys=True))

    def test_huge_sheets_marks_and_transport_without_expansion(self):
        d, m = 1 << 16000, (1 << 8000)+1
        n = d*m
        index = CoverIndex(example(n, [(1,d),(-1,0)]))
        summary = index.summary
        self.assertEqual(summary['component_count'], d//2+1)
        self.assertEqual(summary['cover_isomorphism_type_count'], 2)
        self.assertEqual(len(summary['families']), 3)
        # Distinct exceptional components are isomorphic when m is odd.
        shift = n//2
        marks = (0, d, 123*d, d)
        translated = tuple((x+shift) % n for x in marks)
        self.assertEqual(index.marked_signature(0, marks),
                         index.marked_signature(shift, translated))
        for x, y in zip(marks, translated):
            self.assertEqual(index.transport_sheet(0, shift, x), y)
        # A generic orbit has two residue classes and admits arbitrary anchors.
        generic = (1, n-1, 1+2*d, n-1-3*d)
        moved = tuple(index.transport_sheet(1, 7, x) for x in generic)
        self.assertEqual(index.marked_signature(1, generic), index.marked_signature(7, moved))

    def test_marking_orbits_are_not_bounded_by_three(self):
        n = 31
        index = CoverIndex(example(n, [(1,1)]))
        self.assertEqual(index.summary['cover_isomorphism_type_count'], 1)
        signatures = {index.marked_signature(0, (0,j)) for j in range(n)}
        self.assertEqual(len(signatures), n)
        self.assertEqual(index.marked_signature(0, (5,8)), index.marked_signature(0, (11,14)))
        self.assertNotEqual(index.marked_signature(0, (5,8)), index.marked_signature(0, (8,5)))
        # A point on a reflection-fixed component need not move arbitrarily.
        fixed = CoverIndex(example(12, [(1,2),(-1,0)]))
        self.assertIsNone(fixed.transport_sheet(0, 2, 0))
        self.assertEqual(fixed.transport_sheet(0, 6, 2), 8)

    def test_identity_is_bound_to_normalized_input_and_summary_is_defensive(self):
        raw = example(12, [(1,4),(-1,0)])
        index = CoverIndex(raw)
        expected = index.marked_signature(1, (1,11))
        altered = copy.deepcopy(raw)
        altered['monodromy'][0]['shift'] += 120
        self.assertEqual(expected, CoverIndex(altered).marked_signature(1, (1,11)))
        altered['surface'] = dict(orientable=True, genus=1, boundary_components=1)
        self.assertNotEqual(expected, CoverIndex(altered).marked_signature(1, (1,11)))
        raw['monodromy'][0]['shift'] = 1
        summary = index.summary
        summary['translation_divisor'] = 1
        summary['generator_monodromy'][0]['shift'] = 1
        summary['families'].clear()
        self.assertEqual(expected, index.marked_signature(1, (1,11)))

    def test_invalid_markings_and_query_domains(self):
        index = CoverIndex(example(12, [(1,4),(-1,0)]))
        for marks in ([True], [1.0], ['1'], [-1], [12], [0], iter([1])):
            with self.assertRaises(ValueError):
                index.marked_signature(1, marks)
        with self.assertRaises(ValueError):
            index.transport_sheet(1, 3, 0)
        with self.assertRaises(ValueError):
            index.transport_sheet(1, 12, 1)
        with self.assertRaises(ValueError):
            CoverIndex(example(12, [(1,1)]), check=3)

    def test_cancellation_during_preparation_and_queries(self):
        class Cancelled(Exception):
            pass
        calls = 0
        cap = 0
        def check():
            nonlocal calls
            calls += 1
            if calls > cap:
                raise Cancelled
        raw = example(1 << 200, [(1,7),(-1,0)])
        for cap in (0, 5, 14):
            calls = 0
            with self.assertRaises(Cancelled):
                CoverIndex(raw, check=check)
        cap = 100000
        index = CoverIndex(raw, check=check)
        calls, cap = 0, 5
        with self.assertRaises(Cancelled):
            index.marked_signature(0, [0]*100)
        calls, cap = 0, 0
        with self.assertRaises(Cancelled):
            index.summary
        with self.assertRaises(Cancelled):
            index.boundary_lift_key(0, 0)

    def test_hexadecimal_json_and_cli_beyond_decimal_digit_limit(self):
        n = 1 << 24000
        raw = example(n, [(-1,0)], orientable=False, genus=1)
        encoded = json.loads(json.dumps(json_safe(raw)))
        index = CoverIndex(encoded)
        self.assertEqual(index.summary['sheets'], n)
        self.assertEqual(index.component_key(hex(n-1)), (1,n-1))
        self.assertEqual(index.boundary_lift_key('0x0',hex(n-1))['covering_degree'], 1)
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)/'cover.json'
            p.write_text(json.dumps(encoded))
            output = io.StringIO()
            with redirect_stdout(output):
                self.assertEqual(main([str(p),'--component','1','--mark','1',
                                       '--mark',hex(n-1)]),0)
            result = json.loads(output.getvalue())
            self.assertEqual(encoded_integer(result['sheets']), n)
            self.assertIn('marked_signature', result)
            for args in (['--seconds','0'], ['--seconds','nan'], ['--mark','1']):
                with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
                    main([str(p),*args])
                self.assertEqual(error.exception.code, 2)


if __name__ == '__main__':
    unittest.main()
