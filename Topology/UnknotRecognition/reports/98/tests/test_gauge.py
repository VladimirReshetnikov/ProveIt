from __future__ import annotations
import copy,itertools,json,random,unittest
from gauge_cuts import (compile_grammar,decode_row,query_assignment,extract_cut_addresses,
                        BudgetExceeded,validate,ParityDSU,row_bound,pair_bound,compose_rows)
from checker import verify_packet,VerificationError
from reference import literal_atlas,literal_response,expand,dense_compile
from fixtures import *

class GaugeTests(unittest.TestCase):
    def audit(self,g):
        p=compile_grammar(g); verify_packet(p,g)
        literal=expand(g,max_vertices=12,max_edges=200)
        for i,z in enumerate(literal):
            self.assertEqual({decode_row(r) for r in p['atlases'][i]['rows']},literal_atlas(z,g['k']))
        return p
    def test_empty(self): self.audit({'k':3,'nodes':[leaf(0,[])]})
    def test_isolated_terminals(self):
        p=self.audit({'k':3,'nodes':[leaf(8,[],range(8))]})
        self.assertEqual(len(p['atlases'][0]['rows']),1)
    def test_single_edge(self): self.audit({'k':3,'nodes':[leaf(2,[(0,1,1)],[1,0])]})
    def test_hidden_edge(self): self.audit(hidden_power(2))
    def test_loops(self): self.audit({'k':3,'nodes':[leaf(2,[(0,0,2),(1,1,1)],[1,0])]})
    def test_parallel_edges(self): self.audit({'k':3,'nodes':[leaf(2,[(0,1,1),(0,1,2)],[0,1])]})
    def test_large_capacity(self): self.audit({'k':3,'nodes':[leaf(2,[(0,1,1<<4096)],[0,1])]})
    def test_reordered_roots(self):
        self.audit({'k':3,'nodes':[leaf(5,[(0,1,1),(1,2,1),(3,4,1)],[2,4,0,3,1]),mapping(0,range(5),[3,4,1,0])]})
    def test_self_identification(self):
        self.audit({'k':3,'nodes':[leaf(3,[(0,1,1),(1,2,1)],range(3)),mapping(0,[0,1,0],[1,0])]})
    def test_parity_contradiction(self):
        p=self.audit({'k':3,'nodes':[leaf(2,[(0,1,1)],[0,1]),mapping(0,[0,0],[0])]})
        self.assertTrue(all(r[0]==0 for r in p['atlases'][-1]['rows']))
    def test_forget_correlation(self):
        self.audit({'k':3,'nodes':[leaf(4,[(0,1,1),(2,3,1)],[0,1,2,3]),mapping(0,[0,1,1,2],[])]})
    def test_fresh_copy(self):
        p=self.audit({'k':3,'nodes':[leaf(2,[(0,1,1)],[0,1]),joining(0,0,[0,1],[0,1],[])]})
        self.assertEqual(p['atlases'][-1]['metadata']['edges'],2)
    def test_k4(self):
        p=self.audit(k4());self.assertEqual(p['query']['status'],'NO_MARKED_CUT')
    def test_prism(self):
        p=self.audit(prism());self.assertEqual(p['query']['minimum_cost'],3)
        self.assertTrue(p['atlases'][-1]['metadata']['private_cubic'])
    def test_threshold_four_distinction(self):
        p=self.audit(k4(4));self.assertEqual(p['query']['minimum_cost'],4)
    def test_cut_addresses(self):
        g={'k':3,'nodes':[leaf(3,[(0,1,1),(1,2,1)],range(3)),joining(0,0,[0,1,2],[2,3,4],[])]}
        p=self.audit(g)
        for j,r in enumerate(p['atlases'][-1]['rows']):
            addresses=extract_cut_addresses(p,j)
            self.assertEqual(sum(a['capacity'] for a in addresses),r[0]);self.assertLessEqual(len(addresses),g['k'])
            self.assertEqual(len({(tuple(a['path']),a['leaf_edge']) for a in addresses}),len(addresses))
    def test_assignment_queries(self):
        g={'k':3,'nodes':[leaf(5,[(0,1,1),(1,2,1),(3,4,2)],[0,3,2])]};p=self.audit(g)
        table=literal_response(g['nodes'][0],3)
        for x in range(8):
            expected={}
            for d,y,f in table:
                if y==x: expected[f]=min(d,expected.get(f,d))
            self.assertEqual(query_assignment(p['atlases'][0]['metadata'],[decode_row(r) for r in p['atlases'][0]['rows']],x),expected)
    def test_dense_baseline(self):
        rng=random.Random(811)
        for _ in range(35):
            g=random_grammar(rng,steps=3);p=self.audit(g);dense=dense_compile(g)
            for i,z in enumerate(expand(g,max_vertices=12,max_edges=200)):
                self.assertEqual(dense['tables'][i],literal_response(z,3))
    def test_disconnected_fan(self):
        p=self.audit(component_fan(5));self.assertEqual(max(len(t['rows']) for t in p['atlases']),2)
    def test_permutation_power(self): self.audit(permutation_power(2,2))
    def test_huge_hidden_multiplicity(self):
        g=hidden_power(128);p=compile_grammar(g);verify_packet(p,g)
        self.assertEqual(p['atlases'][-1]['metadata']['hidden_components'],1<<128)
        self.assertEqual(p['query']['minimum_cost'],0)
    def test_zero_budget(self):
        g=component_fan(5,k=0);p=compile_grammar(g);verify_packet(p,g)
        self.assertEqual(p['query']['status'],'NO_MARKED_CUT')
    def test_work_limit(self):
        with self.assertRaises(BudgetExceeded): compile_grammar(prism(),work_limit=0)
    def test_packet_omission(self):
        p=compile_grammar(prism());p['atlases'][0]['rows'].pop();p['atlases'][0]['origins'].pop()
        with self.assertRaises(VerificationError):verify_packet(p)
    def test_forged_cost(self):
        p=compile_grammar(k4());p['atlases'][0]['rows'][0][0]=1
        with self.assertRaises(VerificationError):verify_packet(p)
    def test_forged_tag(self):
        p=compile_grammar(component_fan(2));p['atlases'][0]['rows'][0][2][0]=0
        with self.assertRaises(VerificationError):verify_packet(p)
    def test_forged_metadata(self):
        p=compile_grammar(prism());p['atlases'][0]['metadata']['vertices']+=1
        with self.assertRaises(VerificationError):verify_packet(p)
    def test_wrong_source(self):
        p=compile_grammar(prism())
        with self.assertRaises(VerificationError):verify_packet(p,k4())
    def test_forged_origin(self):
        p=compile_grammar(prism());ri=next(i for i,r in enumerate(p['atlases'][0]['rows']) if r[0]>0)
        p['atlases'][0]['origins'][ri]['cut_edges']=[]
        with self.assertRaises(VerificationError):verify_packet(p)
    def test_forged_query(self):
        p=compile_grammar(prism());p['query']['status']='NO_MARKED_CUT'
        with self.assertRaises(VerificationError):verify_packet(p)
    def test_bad_grammar(self):
        bads=[]
        a=k4();a['nodes'][0]['edges'][0][2]=0;bads.append(a)
        a=k4();a['nodes'][0]['vertices']=1<<128;bads.append(a)
        a=k4();a['nodes'][0]['terminals']=[0,0];bads.append(a)
        a={'k':3,'nodes':[leaf(1,[],[0]),mapping(0,[10],[10])]};bads.append(a)
        a={'k':3,'nodes':[leaf(1,[],[0]),mapping(1,[0],[0])]};bads.append(a)
        for g in bads:
            with self.assertRaises(ValueError):compile_grammar(g)
    def test_random_grammars(self):
        rng=random.Random(1235)
        for _ in range(60):self.audit(random_grammar(rng))
    def test_parity_union_find(self):
        for n in range(1,15):
            rng=random.Random(n);values=[rng.randrange(2) for _ in range(n)];ds=ParityDSU(n)
            for a,b in itertools.combinations(range(n),2): self.assertTrue(ds.union(a,b,values[a]^values[b]))
            for a in range(n):
                ra,pa=ds.find(a)
                for b in range(n):
                    rb,pb=ds.find(b);self.assertEqual(ra,rb);self.assertEqual(pa^pb,values[a]^values[b])
            self.assertFalse(ds.union(0,0,1))
    def test_degree_sharpness(self):
        for n in range(2,9):
            p=self.audit({'k':3,'nodes':[leaf(n,[(0,j,1) for j in range(1,n)],range(n))]})
            from math import comb
            self.assertEqual(len(p['atlases'][0]['rows']),sum(comb(n-1,j) for j in range(min(3,n-1)+1)))
    def test_json_roundtrip(self):
        g=permutation_power(2,2);p=json.loads(json.dumps(compile_grammar(g)));verify_packet(p,g)

if __name__=='__main__':unittest.main()
