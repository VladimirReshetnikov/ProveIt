from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'integration'))
from profile_scancomplex import predict_scancomplex
class AdapterTests(unittest.TestCase):
    def test_mock_reference_interface(self):
        class State: pass
        s=State(); m=frozenset({frozenset({0,1})})
        s.objects={10:(m,0),20:(m,1),30:(m,1)}
        s.out={10:{20:3}}
        ans=predict_scancomplex(s)
        self.assertEqual(ans['minimal_survivors'],1)
        self.assertEqual(ans['profile'][0]['degree'],1)
        self.assertEqual(s.out,{10:{20:3}})
        s.out={10:{20:{'not-bits'}}}
        with self.assertRaises(TypeError): predict_scancomplex(s)
