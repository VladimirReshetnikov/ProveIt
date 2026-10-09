import unittest
from span_excess.geometry import product_solid_torus,expand_surface
from span_excess.pachner import from_product,moves23,move23,move14,replay_history
from span_excess.jsonio import dumps,loads
from span_excess import minimize_edge_then_span

class PachnerCodecTests(unittest.TestCase):
    def test_stellar_move(self):
        g=from_product(product_solid_torus());h=move14(g,0)
        self.assertEqual(len(h.tetrahedra),12);self.assertEqual(h.n,10)
        self.assertEqual(replay_history(h.history),h)
    def test_bistellar_move(self):
        g=from_product(product_solid_torus());moves=list(moves23(g))
        self.assertTrue(moves);h=move23(g,moves[0])
        self.assertEqual(len(h.tetrahedra),10);self.assertEqual(replay_history(h.history),h)
    def test_reject_nonface(self):
        with self.assertRaises(ValueError):move23(from_product(product_solid_torus()),[100,101,102])
    def test_reject_unknown_move(self):
        g=from_product(product_solid_torus())
        with self.assertRaises(ValueError):replay_history(g.history+({'move':'invented'},))
    def test_stellar_height_gauge(self):
        g=from_product(product_solid_torus());h=move14(g,0,10000);m=h.model()
        s=expand_surface(h,minimize_edge_then_span(m)['potential'])
        self.assertEqual(s['euler'],1)
    def test_large_integer_json_roundtrip(self):
        x={'a':-(1<<10000),'b':[1<<2000,0,1,None]}
        self.assertEqual(loads(dumps(x)),x)
    def test_malformed_hex(self):
        with self.assertRaises(ValueError):loads('{"$int":"zz"}')
    def test_reserved_key(self):
        with self.assertRaises(ValueError):dumps({'$int':'a'})
    def test_hex_mixed_fields(self):
        with self.assertRaises(ValueError):loads('{"$int":"ff","extra":1}')

if __name__=='__main__':unittest.main()
