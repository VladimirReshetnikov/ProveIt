"""Adapter contract tests with an injected fake gateway, NOT upstream tests."""
import importlib.util
from pathlib import Path
import unittest
from ranktwo.families import sleeved_unknot
from ranktwo.reference import is_signed_coxeter
spec=importlib.util.spec_from_file_location('adapter',Path(__file__).parents[1]/'integration/fastunknot_adapter.py')
adapter=importlib.util.module_from_spec(spec);spec.loader.exec_module(adapter)

class AdapterContractTests(unittest.TestCase):
    def test_verified_retry(self):
        calls=[]
        def gateway(s,w,check=None):
            calls.append(tuple(w))
            return {'status':'UNKNOT' if is_signed_coxeter(s,w) else 'INCONCLUSIVE'}
        original=sleeved_unknot(4,2)
        answer=adapter.braid_gateway_with_ranktwo(4,original,gateway=gateway)
        self.assertEqual(answer['status'],'UNKNOT');self.assertEqual(len(calls),2)
        self.assertEqual(answer['reduced_input']['word'],[1,2,3])
        self.assertEqual(answer['ranktwo_verification']['verified_steps'],2)

    def test_existing_decision_is_kept(self):
        def gateway(s,w,check=None):return {'status':'KNOTTED','method':'test-only'}
        result=adapter.braid_gateway_with_ranktwo(3,(1,-2)*2,gateway=gateway)
        self.assertEqual(result['status'],'KNOTTED')
        self.assertNotIn('ranktwo_certificate',result)

    def test_resource_exception_not_a_verdict(self):
        def gateway(s,w,check=None):return {'status':'INCONCLUSIVE'}
        def stop():raise TimeoutError('contract test')
        with self.assertRaises(TimeoutError):
            adapter.braid_gateway_with_ranktwo(4,sleeved_unknot(4,2),gateway=gateway,check=stop)
