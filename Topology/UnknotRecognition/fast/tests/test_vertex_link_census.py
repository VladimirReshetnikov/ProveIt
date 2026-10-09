"""Independent literal vertex links, including loop ends and ideal vertices."""
from copy import deepcopy
import random
import unittest
from fastunknot import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_surface_geometry import _prepare,NormalOrbitError
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_surface_orbits import relabel


def literal_links(raw):
    rows=raw['tetrahedra'];corners={};ends={};sides={}
    for t,row in enumerate(rows):
        for v in range(4):
            corners[t,v]=set()
            for w in range(4):
                if v!=w:ends[t,v,w]=set();sides[t,v,w]=set()
    for t,row in enumerate(rows):
        for f,r in enumerate(row):
            if r is None:continue
            u,p=r['tetrahedron'],r['permutation']
            for v in range(4):
                if v==f:continue
                corners[t,v].add((u,p[v]))
                sides[t,v,f].add((u,p[v],p[f]))
                for w in range(4):
                    if w not in (v,f):ends[t,v,w].add((u,p[v],p[w]))
    def components(graph):
        labels={};parts=[]
        for start in graph:
            if start in labels:continue
            label=len(parts);queue=[start];labels[start]=label
            for vertex in queue:
                for other in graph[vertex]:
                    if other not in labels:labels[other]=label;queue.append(other)
            parts.append(queue)
        return labels,parts
    _,vertices=components(corners);end_labels,_=components(ends);side_labels,_=components(sides)
    answer=[]
    for part in vertices:
        darts=[(t,v,w) for t,v in part for w in range(4) if w!=v]
        V=len({end_labels[d] for d in darts});E=len({side_labels[d] for d in darts});F=len(part)
        B=sum(rows[t][w] is None for t,v,w in darts)
        answer.append(dict(vertices=V,edges=E,faces=F,boundary=B,euler=V-E+F))
    return answer


class VertexLinkCensusTests(unittest.TestCase):
    def test_literal_links_with_loop_edges_and_interior_vertices(self):
        rng=random.Random(261009481)
        fixtures=[layered_torus(n)[0] for n in (1,2,7,25)]
        fixtures += [diagram_exterior(Diagram.from_braid(2,[1,1,1]),subdivision=s) for s in ('pulling','centred')]
        for raw in fixtures:
            for _ in range(5):
                changed,_=relabel(raw,[[0]*7 for _ in raw['tetrahedra']],rng)
                p=_prepare(changed,lambda:None);links=literal_links(changed)
                self.assertEqual(p['vertices'],len(links))
                self.assertEqual(sum(r['vertices'] for r in links),2*p['edges'])
                for r in links:self.assertEqual(r['euler'],1 if r['boundary'] else 2)
        one=_prepare(fixtures[0],lambda:None)
        self.assertEqual(one['vertices'],1)
        self.assertTrue(all(a==b for a,b in one['endpoints'].values()))
        self.assertEqual(literal_links(fixtures[0])[0]['vertices'],2*one['edges'])

    def test_ideal_torus_vertex_is_still_rejected(self):
        permutations=[[1,3,0,2],[2,0,3,1],[0,3,2,1],[2,1,0,3]]
        ideal=dict(tetrahedra=[[dict(tetrahedron=1-t,permutation=p[:]) for p in permutations] for t in range(2)])
        links=literal_links(ideal)
        self.assertEqual(len(links),1);self.assertEqual(links[0]['euler'],0)
        self.assertEqual(links[0]['boundary'],0)
        with self.assertRaisesRegex(NormalOrbitError,'vertex link is not a sphere or a disc'):
            _prepare(ideal,lambda:None)

    def test_cancellation_and_input_immutability(self):
        raw=diagram_exterior(Diagram.from_braid(2,[1]));saved=deepcopy(raw);calls=[0]
        def tick():calls[0]+=1
        _prepare(raw,tick);total=calls[0]
        for stop in (1,total//2,total):
            calls[0]=0
            def cancel():
                tick()
                if calls[0]==stop:raise RuntimeError('cancelled')
            with self.assertRaisesRegex(RuntimeError,'cancelled'):_prepare(raw,cancel)
        self.assertEqual(raw,saved)
