import copy
import unittest
from itertools import product
from span_excess import minimize_edge_then_span, replay_edge_then_span
from span_excess.geometry import product_solid_torus, expand_surface
from test_span_excess import interval_model

class LexicographicTests(unittest.TestCase):
    def test_primal_dual_replay(self):
        m=interval_model(7);a=minimize_edge_then_span(m)
        self.assertTrue(replay_edge_then_span(m,a))
    def test_box_oracle(self):
        m=interval_model(7);a=minimize_edge_then_span(m)
        brute=min((m.objective((0,)+p),m.span((0,)+p))
                  for p in product(range(-7,15),repeat=3))
        self.assertEqual(brute,(a['edge_objective'],a['span']))
    def test_auxiliary_potential_mutation(self):
        m=interval_model(7);a=minimize_edge_then_span(m)
        a['second']['potential'][-1]+=100
        self.assertFalse(replay_edge_then_span(m,a))
    def test_output_mutation(self):
        m=interval_model(7);a=minimize_edge_then_span(m);a['span']+=1
        self.assertFalse(replay_edge_then_span(m,a))
    def test_large_bits(self):
        m=interval_model(1<<2048);a=minimize_edge_then_span(m)
        self.assertTrue(replay_edge_then_span(m,a))
    def test_actual_connected_surface(self):
        for middle in (False,True):
            g=product_solid_torus(3,middle);m=g.model();a=minimize_edge_then_span(m)
            s=expand_surface(g,a['potential'])
            self.assertEqual(len(s['components']),1)
            self.assertEqual(2*s['euler'],a['score2'])
    def test_zero_weight_secondary_objective(self):
        from dataclasses import replace
        m=interval_model(7);m=replace(m,edges=tuple((u,v,c,0) for u,v,c,w in m.edges))
        a=minimize_edge_then_span(m)
        self.assertEqual(a['span'],m.optimum)
        self.assertTrue(replay_edge_then_span(m,a))

if __name__=='__main__': unittest.main()
