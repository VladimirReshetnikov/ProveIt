"""Fast regression suite. Larger deterministic sweeps live in experiments/validate.py."""
import copy
import itertools
import random
import unittest
from ranktwo import compress, optimal_pass, verify, maximal_corridors
from ranktwo.common import component_count
from ranktwo.families import (central_sleeve, sleeved_unknot, shortening_barrier,
                              HALF_TWIST_LEFT, HALF_TWIST_RIGHT, weaving_determinant)
from ranktwo.oracles import artin_action, brute_optimum, inverse
from ranktwo.orderedmap import AVLBestMap
from ranktwo.search_group import QuotientTrie
from ranktwo.verify import b3_central_form, local_equal
from ranktwo.cube import reduced_rank, CubeLimit
from ranktwo.reference import recognize_reference


class GroupTests(unittest.TestCase):
    def test_artin_relation(self):
        self.assertEqual(b3_central_form((1,2,1)), b3_central_form((2,1,2)))
        self.assertEqual(artin_action(3,(1,2,1)), artin_action(3,(2,1,2)))

    def test_central_guard(self):
        z = (1,2,1)*2
        trie = QuotientTrie(); node = 0
        for g in z: node = trie.append_generator(node,g)
        self.assertEqual(node,0)
        self.assertEqual(b3_central_form(z),(1,()))
        self.assertFalse(local_equal(z))

    def test_conjugacy_is_not_equality(self):
        self.assertNotEqual(b3_central_form((1,)),b3_central_form((2,)))
        self.assertEqual(component_count(3,(1,-1)),3)
        self.assertEqual(component_count(3,(2,-1)),1)

    def test_sleeve_identity(self):
        for m in range(8):
            self.assertTrue(local_equal(central_sleeve(m)))
            self.assertEqual(artin_action(3,central_sleeve(m)),artin_action(3,()))

    def test_commuting_support(self):
        self.assertTrue(local_equal((1,4,-1,-4)))
        self.assertTrue(local_equal((1,4,-1),4))
        self.assertFalse(local_equal((1,-4)))

    def test_half_twist_equality(self):
        self.assertEqual(artin_action(4,HALF_TWIST_LEFT),artin_action(4,HALF_TWIST_RIGHT))


class KernelTests(unittest.TestCase):
    def test_empty(self):
        result = compress(1,())
        self.assertEqual(verify(1,(),result['certificate'])[0],())

    def test_invalid_inputs(self):
        for strands,word in [(0,()),(True,()),(3,(0,)),(3,(3,)),(3,(True,)),(3,None)]:
            with self.assertRaises(ValueError): compress(strands,word)
        for options in [{'radius':2},{'radius':True},{'dictionary':'unsafe'},{'max_passes':-1}]:
            with self.assertRaises(ValueError): compress(3,(1,),**options)

    def test_budget(self):
        def stop(): raise TimeoutError('test budget')
        with self.assertRaises(TimeoutError): optimal_pass(3,(1,-1),check=stop)
        result = compress(3,(1,-1))
        with self.assertRaises(TimeoutError): verify(3,(1,-1),result['certificate'],check=stop)

    def test_no_pass(self):
        result = compress(3,(1,-1),max_passes=0)
        self.assertEqual(result['word'],[1,-1])
        self.assertFalse(result['stats']['saturated'])
        verify(3,(1,-1),result['certificate'])

    def test_corridor_coverage(self):
        rng=random.Random(402)
        for _ in range(100):
            word=tuple(rng.choice((1,2,3,4,-1,-2,-3,-4)) for _ in range(30))
            corridors=maximal_corridors(word)
            self.assertLessEqual(sum(c.stop-c.start for c in corridors),2*len(word))
            for i in range(len(word)):
                for j in range(i+1,len(word)+1):
                    if len(set(map(abs,word[i:j])))<=2:
                        self.assertTrue(any(c.start<=i and j<=c.stop for c in corridors))

    def test_optimality_small(self):
        for n in range(5):
            for word in itertools.product((1,-1,2,-2),repeat=n):
                for radius in (0,1):
                    output,_,stats=optimal_pass(3,word,radius=radius)
                    self.assertEqual(n-len(output),brute_optimum(3,word,radius))
                    self.assertLessEqual(stats['maximum_active_corridors'],2)

    def test_dictionary_agreement(self):
        rng=random.Random(718)
        for _ in range(100):
            word=tuple(rng.choice((1,-1,2,-2,3,-3,4,-4)) for _ in range(50))
            a=compress(5,word,dictionary='avl')
            b=compress(5,word,dictionary='hash')
            self.assertEqual(a['certificate'],b['certificate'])
            self.assertEqual(verify(5,word,a['certificate'])[0],tuple(a['word']))

    def test_multiple_passes_and_fresh_ids(self):
        rng=random.Random(639)
        found=False
        for _ in range(1000):
            word=tuple(rng.choice((1,-1,2,-2,3,-3)) for _ in range(20))
            result=compress(4,word)
            verify(4,word,result['certificate'])
            if len(result['stats']['passes'])>=3 and result['stats']['fresh_nodes']:
                found=True; break
        self.assertTrue(found)

    def test_sleeved_family(self):
        for s in (4,5,8,20):
            for m in (1,2,5,10):
                word=sleeved_unknot(s,m)
                output,_,_=optimal_pass(s,word)
                self.assertEqual(len(word),8*m+s+23)
                self.assertEqual(len(output),s-1)
                self.assertTrue(all(g>0 for g in output))
                self.assertEqual(set(output),set(range(1,s)))

    def test_shortening_barrier(self):
        for h in range(1,11):
            word=shortening_barrier(h)
            result=compress(4,word)
            self.assertEqual(result['word'],list(word))
            self.assertEqual(artin_action(4,word),artin_action(4,(1,2,3)))


class CertificateTests(unittest.TestCase):
    def setUp(self):
        self.word=sleeved_unknot(4,2)
        self.good=compress(4,self.word)['certificate']

    def test_provenance(self):
        bad=copy.deepcopy(self.good); bad['input_sha256']='0'*64
        with self.assertRaises(ValueError): verify(4,self.word,bad)

    def test_bad_output(self):
        bad=copy.deepcopy(self.good); bad['output_word']=[1]
        with self.assertRaises(ValueError): verify(4,self.word,bad)

    def test_dead_id(self):
        bad=copy.deepcopy(self.good); bad['steps'].insert(1,copy.deepcopy(bad['steps'][0]))
        with self.assertRaises(ValueError): verify(4,self.word,bad)

    def test_false_target(self):
        bad=copy.deepcopy(self.good); bad['steps'][0]['target']=1
        with self.assertRaises(ValueError): verify(4,self.word,bad)

    def test_reversed_endpoints(self):
        bad=copy.deepcopy(self.good)
        step=bad['steps'][0]; step['first'],step['last']=step['last'],step['first']
        with self.assertRaises(ValueError): verify(4,self.word,bad)

    def test_boolean_id(self):
        bad=copy.deepcopy(self.good); bad['steps'][0]['first']=False
        with self.assertRaises(ValueError): verify(4,self.word,bad)

    def test_central_forgery(self):
        word=(1,2,1)*2
        certificate=compress(3,word,max_passes=0)['certificate']
        certificate['steps']=[{'first':0,'last':5,'target':0}]
        certificate['output_word']=[]
        with self.assertRaises(ValueError): verify(3,word,certificate)

    def test_linear_accounting(self):
        rng=random.Random(110)
        for _ in range(200):
            word=tuple(rng.choice((1,-1,2,-2,3,-3)) for _ in range(100))
            result=compress(4,word)
            _,stats=verify(4,word,result['certificate'])
            self.assertLessEqual(stats['removed_nodes'],3*len(word)//2)
            self.assertLessEqual(stats['introduced_nodes'],len(word)//2)


class AVLTests(unittest.TestCase):
    def test_order_height_and_values(self):
        tree=AVLBestMap()
        for i in range(3000): tree.put_best((i,0),(i,i))
        for i in range(3000):
            tree.put_best((i,0),(i+1,i+2))
            self.assertEqual(tree.get((i,0)),(i+1,i+2))
        self.assertEqual(tree.size,3000)
        def walk(node,low=None,high=None):
            if node is None:return 0
            if low is not None:self.assertLess(low,node.key)
            if high is not None:self.assertLess(node.key,high)
            a,b=walk(node.left,low,node.key),walk(node.right,node.key,high)
            self.assertLessEqual(abs(a-b),1)
            self.assertEqual(node.height,1+max(a,b))
            return node.height
        self.assertLess(walk(tree.root),20)


class CubeTests(unittest.TestCase):
    def test_known_ranks_and_square(self):
        for s,word,rank in [(1,(),1),(2,(1,),1),(2,(-1,),1),(2,(1,1),2),
                             (2,(1,1,1),3),(3,(1,2),1),(3,(1,-2)*2,5),
                             (4,(1,2,3),1),(3,(1,-2)*4,45)]:
            self.assertEqual(reduced_rank(s,word,check_square=True)['homology_rank'],rank)

    def test_rank_invariance(self):
        for s,word in [(3,(1,2,1,-2,-1,-2,1,2)),(4,(1,3,-1,-3,1,2,3))]:
            output=compress(s,word)['word']
            self.assertEqual(reduced_rank(s,word,check_square=True)['homology_rank'],
                             reduced_rank(s,output,check_square=True)['homology_rank'])

    def test_limits(self):
        with self.assertRaises(CubeLimit): reduced_rank(3,(1,-2)*8)
        with self.assertRaises(CubeLimit): reduced_rank(3,(1,-2)*4,max_dimension=10)

    def test_reference(self):
        self.assertEqual(recognize_reference(4,sleeved_unknot(4,50))['status'],'UNKNOT')
        self.assertEqual(recognize_reference(2,(1,1,1))['status'],'KNOTTED')
        self.assertEqual(recognize_reference(4,shortening_barrier(1))['status'],'INCONCLUSIVE')
        with self.assertRaises(ValueError): recognize_reference(3,())

    def test_weaving_values(self):
        self.assertEqual([weaving_determinant(m) for m in (1,2,4,5,7)],[1,5,45,121,841])

if __name__=='__main__':unittest.main()
