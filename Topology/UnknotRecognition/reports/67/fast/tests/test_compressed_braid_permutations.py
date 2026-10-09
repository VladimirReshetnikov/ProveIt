"""Independent permutation oracles, shared DAGs and global component guards."""
from copy import deepcopy
from itertools import permutations
import random
import unittest
from unittest.mock import patch

from fastunknot.compressed_braid import recognize, verify
from fastunknot.compressed_braid import forest
from compressed_braid_research.exceptional import grammar, join
from compressed_braid_research.families import singleton_forest


def explicit_summary(m, word):
    p = list(range(m))
    counts = {}
    for letter in word:
        j = abs(letter)
        p[j-1], p[j] = p[j], p[j-1]
        counts[j] = counts.get(j, 0) + 1
    gap = next((j for j in range(1, m) if j not in counts), None)
    reached, current = set(), 0
    while current not in reached:
        reached.add(current)
        current = p[current]
    return dict(length=len(word), exponent=sum(1 if x > 0 else -1 for x in word),
                counts=counts, gap=gap, knot=len(reached) == m,
                permutation=p if gap is None else None)


class CompactPermutationTests(unittest.TestCase):
    def test_all_four_strand_products_in_both_representations(self):
        dense = list(permutations(range(4)))
        for p in dense:
            for q in dense:
                want = [p[q[i]] for i in range(4)]
                for left in (p, {i:j for i,j in enumerate(p) if i != j}):
                    for right in (q, {i:j for i,j in enumerate(q) if i != j}):
                        saved = deepcopy((left, right))
                        got = forest._compose_permutations(left, right, 4)
                        actual = [got.get(i,i) for i in range(4)] if isinstance(got,dict) else list(got)
                        self.assertEqual(actual, want)
                        self.assertEqual((left, right), saved)
                        if isinstance(got, dict):
                            self.assertTrue(all(i != j for i,j in got.items()))

    def test_shared_grammars_against_expanded_word_oracle(self):
        rng = random.Random(261008610)
        for trial in range(400):
            m = rng.randrange(2, 33)
            rules, words = [['e']], [[]]
            for _ in range(60):
                u, v = rng.randrange(len(rules)), rng.randrange(len(rules))
                if rng.randrange(3) and len(words[u])+len(words[v]) <= 1024:
                    rules.append(['c',u,v]);words.append(words[u]+words[v])
                else:
                    g = rng.choice((-1,1))*rng.randrange(1,m)
                    rules.append(['g',g]);words.append([g])
            root = rng.randrange(len(rules))
            # Half the trials force complete support; the rest exercise gaps.
            if trial % 2:
                for g in range(1,m):
                    node = len(rules);rules.append(['g',g]);words.append([g])
                    rules.append(['c',root,node]);words.append(words[root]+[g]);root=node+1
            data = dict(strands=m,rules=rules,root=root)
            self.assertEqual(forest.summarize(data), explicit_summary(m,words[root]))

    def test_huge_shared_powers_do_not_expand_and_cancel_exactly(self):
        data = grammar(32, list(range(1,32)))
        root = data['root']
        for _ in range(256):
            data['rules'].append(['c',root,root]);root=len(data['rules'])-1
        data['root'] = root
        s = forest.summarize(data)
        self.assertEqual(s['length'],31*(1<<256))
        self.assertEqual(s['permutation'],list(range(32)))
        self.assertFalse(s['knot'])
        p={1:2,2:1}
        self.assertEqual(forest._compose_permutations(p,p,32),{})

    def test_dead_rules_validated_but_never_evaluated(self):
        data = grammar(16,list(range(1,16)))
        original = forest.summarize(data)
        first = len(data['rules']);data['rules'].append(['g',15])
        for _ in range(64):
            data['rules'].append(['c',first,first]);first=len(data['rules'])-1
        calls=[];compose=forest._compose_permutations
        def track(*args):calls.append(1);return compose(*args)
        with patch.object(forest,'_compose_permutations',track):
            self.assertEqual(forest.summarize(data),original)
        self.assertEqual(len(calls),15)
        for rule in (['g',True], ['g',16], ['c',1,len(data['rules'])], ['e']):
            bad=deepcopy(data);bad['rules'].append(rule)
            with self.assertRaises(ValueError):forest.summarize(bad)

    def test_support_guard_precedes_any_strand_sized_allocation(self):
        for data in (dict(strands=10**100,rules=[['e']],root=0),
                     dict(strands=10**100,rules=[['e'],['g',10**99]],root=1)):
            with patch.object(forest,'_root_permutation',side_effect=AssertionError):
                self.assertEqual(recognize(data)['status'],'LINK')
        self.assertEqual(forest.summarize(dict(strands=1,rules=[['e']],root=0)),
                         explicit_summary(1,[]))

    def test_link_component_check_survives_negative_factor(self):
        data = join(singleton_forest(4,3),grammar(2,[1,1]))
        with patch.object(forest,'project',side_effect=AssertionError):
            result=recognize(data)
        self.assertEqual(result['status'],'LINK')
        self.assertEqual(verify(data,result['certificate']),'LINK')
        bad=deepcopy(result['certificate']);bad['permutation'][0]=0
        with self.assertRaises(ValueError):verify(data,bad)

    def test_public_proofs_match_dense_ablation_and_limits(self):
        root_permutation=forest._root_permutation
        def dense(*args,**kwargs):return root_permutation(*args,**kwargs,compact=False)
        for data in (singleton_forest(4,4), singleton_forest(5,8,negative_index=4),
                     grammar(16,list(range(1,16))),grammar(4,[1,2,3,1,-1])):
            current=recognize(data)
            with patch.object(forest,'_root_permutation',dense):
                old=recognize(data)
                self.assertEqual(verify(data,current['certificate']),current['status'])
            self.assertEqual(current,old)
            self.assertEqual(recognize(data,max_work=current['resources']['work']),current)
            limited=recognize(data,max_work=current['resources']['work']-1)
            self.assertEqual(limited['status'],'INCONCLUSIVE')
            self.assertNotIn('certificate',limited)

    def test_cancellation_during_permutation_evaluation_propagates(self):
        data=grammar(16,list(range(1,16)));steps=0
        def cancel():
            nonlocal steps
            steps+=1
            if steps==5:raise ValueError('cancel permutation')
        with self.assertRaisesRegex(ValueError,'cancel permutation'):
            forest._root_permutation(data,[1]*len(data['rules']),cancel)
        with patch.object(forest,'_compose_permutations',side_effect=AssertionError):
            self.assertEqual(forest.summarize(grammar(4,[1,2,3])),explicit_summary(4,[1,2,3]))


if __name__ == '__main__':unittest.main()
