"""Historical pairwise bounds preserve donor/sign/rotation order and polls.

The adaptive scheduler can terminate before visiting the remaining donors;
its handoff and cancellation checks are in test_cyclic_overlap_index.
"""
import unittest
from fastunknot.group_certificate import _Budget,GroupLimit
from fastunknot.relator_overlap import pairwise_overlap_move as overlap_move
from test_relator_overlap import brute_gain


class OverlapBoundTests(unittest.TestCase):
    def test_repeated_long_donors_fit_linear_work_allowance(self):
        # Once donor zero is fully matched at target one, no equal-length
        # donor can beat it. This is a resource outcome, not a timing test.
        word=list(range(1,129))
        relators=[word[:],word[:]]+[word[7:]+word[:7] for _ in range(126)]
        budget=_Budget(lambda:None,1000000,20*len(word)+len(relators))
        move=overlap_move(relators,budget)
        self.assertEqual(move,dict(kind='relator',target=1,donor=0,
            target_rotation=0,donor_rotation=0,inverse=False,overlap=len(word)))
        self.assertGreaterEqual(budget.left,0)

    def test_later_longer_donor_can_still_improve(self):
        words=[[1,2],[1,2],[3,4,5,6],[6,3,4,5]]
        move=overlap_move(words,_Budget(lambda:None,10000,10000))
        self.assertEqual(move['donor'],2)
        self.assertEqual(move['target'],3)
        self.assertEqual(move['overlap'],4)
        self.assertEqual(2*move['overlap']-len(words[move['donor']]),brute_gain(words))

    def test_skipped_donors_still_poll_cancellation_and_charge_work(self):
        class Stop(Exception):pass
        checks=0
        def cancel():
            nonlocal checks
            checks+=1
            if checks==100:raise Stop
        with self.assertRaises(Stop):
            overlap_move([[1]]*1000,_Budget(cancel,10000,100000))
        with self.assertRaises(GroupLimit):
            overlap_move([[1]]*1000,_Budget(lambda:None,10000,100))
