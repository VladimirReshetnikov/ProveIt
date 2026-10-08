import unittest
from terminal_updates.terminal import SignedGraph,TerminalKernel,ExactObserver
from terminal_updates.batch import MergePlan
from terminal_updates.linear import Budget,BudgetExceeded
from integration.boundary_adapter import ModularBoundaryObserver

class BatchTests(unittest.TestCase):
    def setUp(self):
        self.graph=SignedGraph(4,((0,1,1),(1,2,-1),(2,3,2),(3,0,1),(1,3,1)))
        self.labels=[(0,1,2),(0,1,1),(0,0,2),(0,0,0),(8,9,9)]
    def test_exact_plan(self):
        e=ExactObserver(self.graph,(0,1,2));p=MergePlan.compile(3,self.labels)
        self.assertEqual(p.evaluate(e),[e.query(z) for z in self.labels])
        self.assertEqual(p.observations[1],p.observations[-1])
    def test_field_plan(self):
        p=MergePlan.compile(3,self.labels)
        for prime in (2,3,5,101):
            e=TerminalKernel(self.graph,(0,1,2),prime)
            self.assertEqual(p.evaluate(e),[e.query(z) for z in self.labels])
    def test_empty_plan(self):
        self.assertEqual(MergePlan.compile(3,[]).evaluate(TerminalKernel(self.graph,(0,1,2),3)),[])
    def test_bad_plan(self):
        with self.assertRaises(ValueError):MergePlan.compile(0,[])
        with self.assertRaises(ValueError):MergePlan.compile(3,[(1,2)])
        with self.assertRaises(ValueError):MergePlan(3,((1,0,1),),(1,)).evaluate(TerminalKernel(self.graph,(0,1,2),3))
    def test_budget_failure(self):
        e=ExactObserver(self.graph,(0,1,2));p=MergePlan.compile(3,self.labels)
        with self.assertRaises(BudgetExceeded):p.evaluate(e,Budget(units_left=0))
        self.assertEqual(p.evaluate(e),[e.query(z) for z in self.labels])
    def test_contract_adapter(self):
        # This is explicitly a protocol fixture, not upstream geometry validation.
        graph=self.graph
        class Fixture:
            laplacian=graph.laplacian();terminals=(0,1,2)
            def partition(self,labels):
                if labels=='invalid':raise ValueError('geometry declined')
                return dict(partition=labels,phase=2,shadow_components=1)
        adapter=ModularBoundaryObserver(Fixture())
        self.assertEqual(adapter.evaluate_many(self.labels),[adapter.evaluate(z) for z in self.labels])
        with self.assertRaises(ValueError):adapter.evaluate('invalid')
    def test_disconnected_contract(self):
        graph=self.graph
        class Fixture:
            laplacian=graph.laplacian();terminals=(0,1,2)
            def partition(self,labels):return dict(partition=labels,phase=0,shadow_components=2)
        a=ModularBoundaryObserver(Fixture())
        self.assertEqual(a.evaluate((0,1,2))[0],(0,0))
        self.assertEqual(a.evaluate_many([(0,1,2)])[0][0],(0,0))

if __name__=='__main__':unittest.main()
