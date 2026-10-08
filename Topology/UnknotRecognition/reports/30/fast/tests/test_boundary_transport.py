"""Boundary-circle constraints, literal equivariance and binary-size scaling."""

from collections import deque
from contextlib import redirect_stderr, redirect_stdout
import io
import json
from math import gcd
from pathlib import Path
import tempfile
import unittest

from fastunknot.boundary_transport import BoundaryTransportIndex, main
from fastunknot.integer_codec import encoded_integer, json_safe


def example(n, maps, *, orientable=True, genus=0):
    return {'surface': {'orientable': orientable, 'genus': genus,
                        'boundary_components': len(maps)-(2*genus if orientable else genus)+1},
            'sheets': n,
            'monodromy': [{'sign': sign, 'shift': shift} for sign, shift in maps]}


def root_images(result):
    return {item['first']+j*item['step'] for item in result['root_progressions']
            for j in range(item['count'])}


def literal_component(generators, root):
    component = {root}
    pending = deque([root])
    while pending:
        for permutation in generators:
            y = permutation[pending[0]]
            if y not in component:
                component.add(y)
                pending.append(y)
        pending.popleft()
    return component


def literal_maps(generators, source, target):
    """Propagate equivariance in finite permutation graphs, without affine formulas."""
    if len(source) != len(target):
        return []
    result = []
    for image in target:
        mapping = {min(source): image}
        pending = deque([min(source)])
        valid = True
        while pending and valid:
            x = pending.popleft()
            for permutation in generators:
                y, z = permutation[x], permutation[mapping[x]]
                if y in mapping:
                    if mapping[y] != z:
                        valid = False
                        break
                else:
                    mapping[y] = z
                    pending.append(y)
        if valid and set(mapping.values()) == target:
            result.append(mapping)
    return result


class BoundaryTransportTests(unittest.TestCase):
    def test_literal_boundary_and_point_constraints(self):
        comparisons = 0
        for n in range(1,11):
            for shift in range(n):
                for reflection in range(n):
                    raw = example(n, [(1,shift),(-1,reflection)])
                    index = BoundaryTransportIndex(raw)
                    generators = [tuple((sign*x+a) % n for x in range(n))
                                  for sign,a in [(1,shift),(-1,reflection)]]
                    for x in range(n):
                        source = literal_component(generators,x)
                        for y in range(n):
                            target = literal_component(generators,y)
                            maps = literal_maps(generators,source,target)
                            target_circle = literal_component([generators[1]],y)
                            result = index.transports(x,y,boundary_pairs=[(1,x,y)])
                            expected = {f[min(source)] for f in maps if f[x] in target_circle}
                            self.assertEqual(root_images(result),expected)
                            comparisons += 1
                            pinned = index.transports(x,y,point_pairs=[(x,y)],
                                                      boundary_pairs=[(1,x,y)])
                            self.assertEqual(root_images(pinned),
                                             {f[min(source)] for f in maps if f[x] == y})
                            comparisons += 1
        self.assertEqual(comparisons,50666)

    def test_boundary_circle_is_unparameterized_and_selector_is_unmarked(self):
        index = BoundaryTransportIndex(example(35,[(1,1)]))
        full = index.transports(12,30,boundary_pairs=[(0,7,19),(1,4,22)])
        self.assertEqual(full['source_root'],0)
        self.assertEqual(full['isomorphism_count'],35)
        self.assertEqual(root_images(full),set(range(35)))
        pinned = index.transports(12,30,point_pairs=[(7,19)],
                                  boundary_pairs=[(0,7,19),(1,4,22)])
        self.assertEqual(root_images(pinned),{12})

    def test_generalized_crt_detects_consistency_with_shared_factors(self):
        index = BoundaryTransportIndex(example(360,[(1,1),(1,12),(1,18)]))
        good = index.transports(0,0,boundary_pairs=[(1,0,5),(2,0,11)])
        self.assertEqual(root_images(good),set(range(29,360,36)))
        self.assertEqual(good['isomorphism_count'],10)
        bad = index.transports(0,0,boundary_pairs=[(1,0,5),(2,0,10)])
        self.assertEqual(bad['root_progressions'],[])
        self.assertIsNone(bad['witness_target_anchor'])

    def test_huge_binary_cover_returns_all_maps_without_enumeration(self):
        exponent = 12000
        a,b,c = 2**exponent,3**exponent,5**exponent
        index = BoundaryTransportIndex(example(a*b*c,[(1,1),(1,a),(1,b)]))
        result = index.transports(0,0,boundary_pairs=[(1,0,17),(2,0,17)])
        self.assertEqual(result['root_progressions'],[{'first':17,'step':a*b,'count':c}])
        self.assertEqual(result['isomorphism_count'],c)
        pinned = index.transports(0,0,point_pairs=[(29,46)],
                                  boundary_pairs=[(1,0,17),(2,0,17)])
        self.assertEqual(pinned['isomorphism_count'],1)
        self.assertEqual(pinned['witness_target_anchor'],17)

    def test_paired_and_fixed_reflection_components(self):
        d,m = 1 << 6000,(1 << 4000)+1
        n = d*m
        index = BoundaryTransportIndex(example(n,[(1,d),(-1,0)]))
        unmarked = index.transports(1,3)
        self.assertEqual(unmarked['isomorphism_count'],2*m)
        self.assertEqual(len(unmarked['root_progressions']),2)
        circle = index.transports(1,3,boundary_pairs=[(1,1,3)])
        self.assertEqual(circle['isomorphism_count'],2)
        self.assertEqual(root_images(circle),{3,n-3})
        one = index.transports(1,3,boundary_pairs=[(1,1,3),(0,1,3)])
        self.assertEqual(root_images(one),{3})
        fixed = index.transports(0,d//2,boundary_pairs=[(1,0,n//2)])
        self.assertEqual(root_images(fixed),{n//2})
        even = BoundaryTransportIndex(example(24,[(1,4),(-1,0)]))
        self.assertEqual(even.transports(0,2)['isomorphism_count'],0)
        self.assertEqual(root_images(even.transports(0,0,boundary_pairs=[(1,4,4)])),{0})

    def test_two_boundary_marks_still_have_exponentially_many_types(self):
        h = 23
        index = BoundaryTransportIndex(example(2*h,[(1,1),(1,h),(1,h)]))
        for j in range(h):
            for k in range(h):
                result = index.transports(0,0,boundary_pairs=[(1,0,0),(2,j,k)])
                self.assertEqual(result['isomorphism_count'],2 if j == k else 0)

    def test_cyclic_canonical_signatures_and_exact_orbit_count(self):
        for n in range(1,11):
            for a in range(n):
                for b in range(n):
                    index = BoundaryTransportIndex(example(n,[(1,1),(1,a),(1,b)]))
                    q1,q2 = gcd(n,a),gcd(n,b)
                    classes = set()
                    for x in range(q1):
                        for y in range(q2):
                            answer = index.cyclic_marked_signature(0,
                                        boundary_marks=[(1,x),(2,y)])
                            signature = answer['signature']
                            classes.add(signature)
                            phase = answer['canonical_root_image']
                            self.assertEqual(signature[-1],((x+phase) % q1,(y+phase) % q2))
                            self.assertEqual(answer['marking_type_count'],gcd(q1,q2))
                            self.assertEqual(answer['isomorphism_count_to_canonical'],
                                             n//(q1*q2//gcd(q1,q2)))
                            self.assertEqual(signature,index.cyclic_marked_signature(0,
                                boundary_marks=[(1,(x+1) % n),(2,(y+1) % n)])['signature'])
                    self.assertEqual(len(classes),gcd(q1,q2))
        index = BoundaryTransportIndex(example(48,[(1,4),(1,12)]))
        left = index.cyclic_marked_signature(1,point_marks=[1,9],boundary_marks=[(1,5)])
        right = index.cyclic_marked_signature(2,point_marks=[6,14],boundary_marks=[(1,10)])
        self.assertEqual(left['signature'],right['signature'])
        self.assertEqual(left['isomorphism_count_to_canonical'],1)
        self.assertEqual(index.cyclic_marked_signature(1)['marking_type_count'],1)
        with self.assertRaises(ValueError):
            BoundaryTransportIndex(example(12,[(1,4),(-1,0)])).cyclic_marked_signature(1)
        for kwargs in ({'point_marks':[True]}, {'point_marks':[0]},
                       {'boundary_marks':[(3,1)]}, {'boundary_marks':[(1,0)]},
                       {'boundary_marks':iter([(1,1)])}):
            with self.assertRaises(ValueError):
                index.cyclic_marked_signature(1,**kwargs)

    def test_validation_and_cooperative_cancellation(self):
        index = BoundaryTransportIndex(example(12,[(1,4),(-1,0)]))
        for query in ({'point_pairs':[(True,1)]}, {'point_pairs':[(1,1,1)]},
                      {'point_pairs':iter([(1,1)])}, {'point_pairs':[(0,1)]},
                      {'boundary_pairs':[(3,1,1)]}, {'boundary_pairs':[(0,1,12)]},
                      {'boundary_pairs':[(0,1,0)]}, {'boundary_pairs':[(0,1.0,1)]}):
            with self.assertRaises(ValueError):
                index.transports(1,1,**query)
        calls,limit = 0,10000
        class Cancelled(Exception):
            pass
        def check():
            nonlocal calls
            calls += 1
            if calls > limit:
                raise Cancelled
        index = BoundaryTransportIndex(example(1 << 500,[(1,1),(1,2)]),check=check)
        calls,limit = 0,20
        with self.assertRaises(Cancelled):
            index.transports(0,0,boundary_pairs=[(1,0,0)]*100)

    def test_hexadecimal_json_cli_and_malformed_queries(self):
        n = 1 << 24000
        raw = {'cover':example(n,[(1,1)]),
               'query':{'source_component':0,'target_component':0,
                        'boundary_pairs':[(0,0,n-1)]}}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'query.json'
            path.write_text(json.dumps(json_safe(raw)))
            output = io.StringIO()
            with redirect_stdout(output):
                self.assertEqual(main([str(path)]),0)
            result = json.loads(output.getvalue())
            self.assertEqual(encoded_integer(result['isomorphism_count']),n)
            self.assertEqual(encoded_integer(result['root_progressions'][0]['count']),n)
            for arguments in (['--seconds','0'],['--seconds','nan']):
                with redirect_stderr(io.StringIO()),self.assertRaises(SystemExit) as error:
                    main([str(path),*arguments])
                self.assertEqual(error.exception.code,2)
            raw['query']['unrecognized'] = 0
            path.write_text(json.dumps(json_safe(raw)))
            with redirect_stderr(io.StringIO()),self.assertRaises(SystemExit) as error:
                main([str(path)])
            self.assertEqual(error.exception.code,2)


if __name__ == '__main__':
    unittest.main()
