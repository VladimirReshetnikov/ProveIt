import json,unittest
from pathlib import Path
from report91_adapter import translate
from gauge_cuts import compile_grammar,decode_row
from checker import verify_packet,verify_coloring_recipe
from coloring import build_recipe
from reference import expand,literal_atlas

class AdapterTests(unittest.TestCase):
    def test_actual_upstream_prism(self):
        source=json.loads(Path('examples/report91_triangular_prism.json').read_text());g=translate(source);p=compile_grammar(g);verify_packet(p,g)
        self.assertEqual(p['query']['minimum_cost'],3)
        self.assertEqual(p['atlases'][-1]['metadata']['vertices'],6)
        self.assertEqual(p['atlases'][-1]['metadata']['edges'],9)
        self.assertTrue(p['atlases'][-1]['metadata']['private_cubic'])
        for i,z in enumerate(expand(g)):
            self.assertEqual({decode_row(r) for r in p['atlases'][i]['rows']},literal_atlas(z,3))
        ri=next(i for i,r in enumerate(p['atlases'][-1]['rows']) if r[3]==3)
        verify_coloring_recipe(build_recipe(p,ri),g)
    def test_selected_nonfinal_root(self):
        s=json.loads(Path('examples/report91_triangular_prism.json').read_text());s['root']=0
        g=translate(s);p=compile_grammar(g);verify_packet(p,g)
        self.assertEqual(p['query']['status'],'OPEN_INTERFACE')
        self.assertEqual(p['atlases'][-1]['rows'],p['atlases'][0]['rows'])
    def test_inventory_guard(self):
        s={'schema':'proveit.graph-grammar.v1','nodes':[{'kind':'leaf','vertices':1<<128,'edges':[],'terminals':[]}]}
        with self.assertRaises(ValueError):translate(s)
    def test_single_implicit_isolate(self):
        s={'schema':'proveit.graph-grammar.v1','nodes':[{'kind':'leaf','vertices':1,'edges':[],'terminals':[]}]}
        p=compile_grammar(translate(s));verify_packet(p);self.assertEqual(p['atlases'][0]['metadata']['hidden_components'],1)
    def test_explicit_private_isolates(self):
        s={'schema':'proveit.graph-grammar.v1','nodes':[{'kind':'leaf','vertices':3,'edges':[],'terminals':[1],'isolated_vertices':[0,2]}]}
        p=compile_grammar(translate(s));verify_packet(p);self.assertEqual(len(p['atlases'][0]['rows']),1)
    def test_repeated_and_invalid_maps(self):
        s={'schema':'proveit.graph-grammar.v1','nodes':[{'kind':'leaf','vertices':2,'edges':[[0,1,1]],'terminals':[0,1]},
           {'kind':'map','child':0,'mapping':[0,0],'terminals':[0]}]}
        p=compile_grammar(translate(s));verify_packet(p);self.assertEqual(len(p['atlases'][-1]['rows']),1)
        s['nodes'][-1]['mapping']=[2,2]
        with self.assertRaises(ValueError):translate(s)
if __name__=='__main__':unittest.main()
