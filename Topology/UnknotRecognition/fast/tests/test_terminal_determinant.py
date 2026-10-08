"""Integer terminal quotients against independent full cofactor determinants."""
import copy
from pathlib import Path
import random
import sys
import unittest

from fastunknot.terminal_determinant import IntegerTerminalKernel, verify_integer_terminal_kernel

sys.path.insert(0, str(Path(__file__).resolve().parents[2]/'reports/26'))
from detshadow.linalg import bareiss, quotient_cofactor, signed_laplacian


class IntegerTerminalTests(unittest.TestCase):
    def test_random_signed_graphs_and_source_replay(self):
        rng = random.Random(261008117)
        comparisons = 0
        for trial in range(400):
            n = rng.randrange(1,10)
            terminals = rng.sample(range(n), rng.randrange(1,n+1))
            edges = [(i,j,rng.choice((-3,-2,-1,1,2,3))) for i in range(n)
                     for j in range(i+1,n) if rng.random()<0.5]
            lap = signed_laplacian(n,edges)
            saved = copy.deepcopy(lap)
            kernel = IntegerTerminalKernel.build(lap,terminals)
            self.assertTrue(verify_integer_terminal_kernel(lap,kernel))
            for _ in range(20):
                labels = [rng.randrange(len(terminals)) for _ in terminals]
                self.assertEqual(kernel.query(labels),bareiss(quotient_cofactor(lap,terminals,labels)))
                comparisons += 1
            self.assertEqual(lap,saved)
        self.assertEqual(comparisons,8000)

    def test_off_diagonal_pivot_singular_border_and_empty_quotient(self):
        lap = [[0,1,-1],[1,0,-1],[-1,-1,2]]
        kernel = IntegerTerminalKernel.build(lap,(2,))
        self.assertEqual(kernel.pivots[0],(0,1))
        self.assertEqual(kernel.query((7,)),-1)
        self.assertTrue(verify_integer_terminal_kernel(lap,kernel))
        zero = IntegerTerminalKernel.build([[0]*4 for _ in range(4)],(0,1,2))
        self.assertEqual(zero.nullity,1)
        for labels in ((0,1,2),(0,0,1),(0,0,0)):
            self.assertEqual(zero.query(labels),0)
        singleton = IntegerTerminalKernel.build([[0]],(0,))
        self.assertEqual(singleton.query((99,)),1)
        nonunit = IntegerTerminalKernel.build([[3,-3],[-3,3]],(0,))
        self.assertEqual(nonunit.query((0,)),3)

    def test_invalid_inputs_corrupted_kernel_and_interruption(self):
        with self.assertRaises(ValueError):IntegerTerminalKernel.build([[1,2],[3,1]],(0,))
        with self.assertRaises(ValueError):IntegerTerminalKernel.build([[0]],(True,))
        lap = [[2,-1,-1],[-1,2,-1],[-1,-1,2]]
        kernel = IntegerTerminalKernel.build(lap,(0,1))
        with self.assertRaises(ValueError):kernel.query((0,True))
        forged = copy.copy(kernel)
        forged.scale += 1
        self.assertFalse(verify_integer_terminal_kernel(lap,forged))
        forged = copy.copy(kernel)
        forged.border = tuple(tuple(x+1 for x in row) for row in kernel.border)
        self.assertFalse(verify_integer_terminal_kernel(lap,forged))
        class Stop(Exception):pass
        def cancel():raise Stop()
        for fn in (lambda:IntegerTerminalKernel.build(lap,(0,1),check=cancel),
                   lambda:kernel.query((0,1),check=cancel),
                   lambda:verify_integer_terminal_kernel(lap,kernel,check=cancel)):
            with self.assertRaises(Stop):fn()
        self.assertEqual(kernel.query((0,1)),3)

    def test_boundary_adapter_preserves_value_and_all_metadata(self):
        sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'determinant_research'))
        from boundary_tait import BoundaryTait
        from fastunknot import Diagram
        from fastunknot.diagram import DiagramError
        from fastunknot.scan_fast import FastScan
        rng = random.Random(261008118)
        accepted = 0
        for _ in range(200):
            try:d = Diagram.from_braid(3,[rng.choice((-2,-1,1,2)) for _ in range(8)])
            except DiagramError:continue
            accepted += 1
            scan = FastScan(shape_cache=False)
            order = list(range(d.crossings))
            for stage,index in enumerate(order):
                rational = BoundaryTait(d.pd,order,stage)
                integer = BoundaryTait(d.pd,order,stage,arithmetic='integer')
                integer.prepare_kernel(verify=True)
                for m in set(scan.mid)-{None}:
                    pairs = scan.algebra.pairs[m]
                    self.assertEqual(integer.evaluate(pairs),rational.evaluate(pairs))
                scan.add_crossing(d.pd[index])
            if accepted == 25:break
        self.assertEqual(accepted,25)
