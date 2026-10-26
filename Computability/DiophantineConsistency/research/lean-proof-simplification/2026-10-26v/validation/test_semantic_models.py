#!/usr/bin/env python3
"""Finite illustrative Python models, NOT executions or verification of Lean.
The tests probe conventions and boundary counterexamples independently of tactics.
"""
import itertools,unittest

def state_number(s):return 215 if s is None else s
def adapted_target(q):return q if q<215 else None
def head_color(s,b):return 2*state_number(s)+b+2
def color(s,h,tape,x):return head_color(s,tape.get(x,0)) if x==h else tape.get(x,0)

class SemanticModelTests(unittest.TestCase):
    def test_state_last_slot_all_216(self):
        states=[None]+list(range(215));codes=[state_number(s) for s in states]
        self.assertEqual(set(codes),set(range(216)));self.assertEqual(len(codes),len(set(codes)))
        self.assertEqual(state_number(None),215)
    def test_zero_slot_equivalence_would_change_encoding(self):
        self.assertNotEqual(state_number(None),0)
        self.assertNotEqual(state_number(0),1)
    def test_action_reflection_valid_targets_and_invalid_counterexample(self):
        for q in range(216):self.assertEqual(adapted_target(q) is None,q==215)
        self.assertIsNone(adapted_target(216));self.assertNotEqual(216,215)
        self.assertNotEqual(state_number(adapted_target(216)),216)
    def test_color_formula_old_new_elsewhere_and_entering_halt(self):
        for h,d,next_state,write,bits in itertools.product(range(-2,3),[-1,1],[None,0,214],[0,1],itertools.product([0,1],repeat=3)):
            tape=dict(zip([h-1,h,h+1],bits));after=dict(tape);after[h]=write
            for x in range(h-2,h+3):
                lhs=color(next_state,h+d,after,x)
                rhs=head_color(next_state,tape.get(x,0)) if x==h+d else write if x==h else color(0,h,tape,x)
                self.assertEqual(lhs,rhs)
                if next_state is None and x==h+d:self.assertEqual(lhs,432+tape.get(x,0))
    def test_already_halted_is_stationary_not_fictitious_action(self):
        # Machine.step cfg = cfg when cfg.state=None; action-record theorem is
        # deliberately separate and row interpretation still requires a live q.
        def step(cfg,transition):
            s,h,tape=cfg
            if s is None:return cfg
            nxt,d,w=transition(s,tape.get(h,0));out=dict(tape);out[h]=w
            return nxt,h+d,out
        def forbidden_transition(s,b):
            raise AssertionError('halted configurations must not evaluate transition')
        cfg=(None,3,{3:1});self.assertEqual(step(cfg,forbidden_transition),cfg)
        live=(0,3,{3:1});entered=step(live,lambda s,b:(None,-1,0))
        self.assertEqual(entered,(None,2,{3:0}));self.assertEqual(step(entered,forbidden_transition),entered)
    def test_bond_direction_orientation_and_horizontal_matching(self):
        for h,d,signal in itertools.product(range(-3,4),[False,True],[1,2,215,432]):
            nxt=h+(1 if d else -1);left=h if d else nxt
            pulse=lambda x:signal if x==left else 0
            west=lambda x:signal if x==(nxt if d else h) else 0
            east=lambda x:signal if x==(h if d else nxt) else 0
            for x in range(-6,7):
                self.assertEqual(west(x),pulse(x-1));self.assertEqual(east(x),pulse(x))
                self.assertEqual(west(x+1),east(x))
            self.assertNotEqual(pulse(left),pulse(left+1))
    def test_interval_paths_retain_open_boundary_guards(self):
        for l,r in itertools.combinations(range(-6,7),2):
            for seed in range(l+1,r):
                for x in range(l+1,r):
                    pos=seed;d=1 if x>=seed else -1
                    while pos!=x:
                        self.assertTrue(l<pos<r)
                        if d==1:self.assertTrue(l<pos and pos+1<r)
                        else:self.assertTrue(l<pos-1 and pos<r)
                        pos+=d
                    self.assertEqual(seed+(x-seed),x)
    def test_seed_guard_is_essential_at_both_boundaries(self):
        l,r=0,3
        for seed in [l,r]:
            P=lambda x:x==seed
            self.assertTrue(P(seed));self.assertFalse(P(1))
            # Both guarded closure assumptions hold, but coverage fails.
            for x in range(-3,6):
                self.assertTrue(not(l<x and x+1<r and P(x)) or P(x+1))
                self.assertTrue(not(l<x-1 and x<r and P(x)) or P(x-1))
    def test_abs_exterior_inclusive_and_zero(self):
        for t,x in itertools.product(range(8),range(-10,11)):
            self.assertEqual(t<=abs(x),x<=-t or t<=x)
        self.assertTrue(0<=abs(0));self.assertTrue(0<=0 or 0<=0)

if __name__=='__main__':unittest.main()
