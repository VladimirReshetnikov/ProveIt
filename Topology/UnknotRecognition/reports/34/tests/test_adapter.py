import unittest
from integration.adapter import recognize_with_backend

class AdapterTests(unittest.TestCase):
    def test_unknown_preserved(self):
        r=recognize_with_backend(3,[1,2,1,-2],lambda f,t:{'status':'UNKNOWN'})
        self.assertEqual(r['status'],'UNKNOWN')
    def test_invalid_status_rejected(self):
        with self.assertRaises(ValueError):recognize_with_backend(3,[1,2,1,-2],lambda f,t:{'status':'CORE'})
    def test_budget_not_reset(self):
        r=recognize_with_backend(3,[1,2,1,-2],lambda f,t: self.fail('must not be called'),seconds=0)
        self.assertEqual(r['status'],'UNKNOWN')
    def test_exact_all_factors(self):
        calls=[]
        def backend(f,t):calls.append(f);return {'status':'UNKNOT'}
        r=recognize_with_backend(4,[1,1,-1,3,3,-3,2],backend)
        self.assertEqual(r['status'],'UNKNOT')
        self.assertEqual(len(calls),1) # literal equal factors are memoized
    def test_linear_descent_chain(self):
        r=recognize_with_backend(8,[1,2,1,-2]+list(range(3,8)),lambda f,t:{'status':'UNKNOT'},descend=True)
        self.assertEqual(r['status'],'UNKNOT')
        self.assertIn('descent_certificate',r)
