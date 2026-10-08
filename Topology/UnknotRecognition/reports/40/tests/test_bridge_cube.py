import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import unittest
from types import SimpleNamespace
from portkh import gf2
from portkh.complexes import analyze, expand
from portkh.explicit import from_dense, from_closed_fastscan
from cube_oracle import cube,homology,components

class BridgeCube(unittest.TestCase):
    def test_known_small_knots(self):
        for strands,word,expected in [(1,[],2),(2,[1],2),(3,[1,2],2),
                (2,[1,1,1],6),(2,[-1,-1,-1],6),(3,[1,-2,1,-2],10),
                (2,[],4),(2,[1,1],4)]:
            rows,degrees=cube(strands,word)
            h=homology(rows,degrees)
            self.assertEqual(sum(h.values()),expected)
            c=from_dense(rows,degrees)
            self.assertEqual(expand(c)[0],rows)
            self.assertEqual(analyze(c)['homology_dimension'],expected)

    def test_braid_relations(self):
        for strands,v,w in [(3,[1,2,1],[2,1,2]),(3,[-1,-2,-1],[-2,-1,-2]),
                             (4,[1,3],[3,1]),(3,[1,2,2,-2],[1,2])]:
            self.assertEqual(homology(*cube(strands,v)),homology(*cube(strands,w)))

    def test_stabilization(self):
        for s,w in [(2,[1,1,1]),(3,[1,-2,1,-2]),(2,[1])]:
            h=homology(*cube(s,w))
            for g in (s,-s): self.assertEqual(h,homology(*cube(s+1,w+[g])))

    def test_fixture_adapter(self):
        rows,degrees=cube(2,[1,1,1]);n=len(rows)
        out=[{} for _ in rows]
        for t,row in enumerate(rows):
            for s in gf2.bits(row):out[s][t]=1
        fixture=SimpleNamespace(points=frozenset(),mid=[0]*n,deg=degrees,out=out,live=n)
        self.assertEqual(analyze(from_closed_fastscan(fixture))['homology_dimension'],6)
        fixture.points=frozenset({1,2})
        with self.assertRaises(ValueError):from_closed_fastscan(fixture)
        fixture.points=frozenset();fixture.live=n-1
        with self.assertRaises(ValueError):from_closed_fastscan(fixture)
        fixture.live=n;fixture.out[0][0]=3
        with self.assertRaises(ValueError):from_closed_fastscan(fixture)

    def test_input_caps(self):
        with self.assertRaises(ValueError):cube(2,[2])
        with self.assertRaises(ValueError):cube(2,[1]*13)
        with self.assertRaises(ValueError):cube(2,[1],max_dimension=1)
        with self.assertRaises(ValueError):from_dense([1],[0])

    def test_component_count(self):
        self.assertEqual(components(3,[1,2]),1)
        self.assertEqual(components(3,[]),3)

if __name__=='__main__':unittest.main()
