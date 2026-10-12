"""Production deadline and mutable-budget contracts for continuation APIs."""
import unittest
from unittest.mock import patch

from fastunknot.twist import tail, streaming
from fastunknot.twist.core import Budget, ResourceLimit, Run


class ContinuationResourceTests(unittest.TestCase):
    def test_tail_checks_shared_deadline_after_reference_computation(self):
        real = tail.homology
        for magnitude in (1, 101):
            now = [0.0]
            cap = Budget(seconds=1)
            def delayed(*args, **kwargs):
                self.assertLessEqual(kwargs['budget'].seconds, 1)
                result = real(*args, **kwargs)
                now[0] = 2.0
                return result
            with patch.object(tail, 'monotonic', side_effect=lambda: now[0]), \
                 patch.object(tail, 'homology', side_effect=delayed):
                with self.assertRaises(ResourceLimit):
                    tail.tail_homology(2, [Run(1, magnitude)], budget=cap)
            self.assertEqual(cap.seconds, 1)

    def test_streaming_revalidates_mutable_and_wrong_budget_types(self):
        cap = streaming.StreamBudget()
        cap.max_states = -1
        for function in (streaming.homology, streaming.recognize):
            for bad in (cap, Budget(), object()):
                with self.assertRaises(ValueError):
                    function(2, [Run(1, 3)], budget=bad)


if __name__ == '__main__':
    unittest.main()
