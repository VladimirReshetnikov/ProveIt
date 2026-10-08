import json
import random
import unittest
from portkh import gf2
from portkh.automata import Register, product_register
from portkh.complexes import (TemplateBlock, PortComplex, analyze, expand,
                              coupled_pair, connected_singular_pair)


def elementary_rank(rows, width):
    """Independent dense list implementation, using low-column pivots."""
    a = [[(x >> j) & 1 for j in range(width)] for x in rows]
    p = 0
    for j in range(width):
        k = next((i for i in range(p, len(a)) if a[i][j]), None)
        if k is None:
            continue
        a[p], a[k] = a[k], a[p]
        for i in range(p+1, len(a)):
            if a[i][j]:
                a[i] = [x ^ y for x, y in zip(a[i], a[p])]
        p += 1
    return p


def random_register(rng, m, width, outputs):
    widths = tuple(rng.randint(1, width) for _ in range(m+1))
    transitions = tuple(tuple(tuple(rng.randrange(1 << widths[j+1])
                                     for _ in range(widths[j])) for _ in (0, 1))
                        for j in range(m))
    return Register(widths, transitions, rng.randrange(1 << widths[0]),
                    tuple(rng.randrange(1 << outputs) for _ in range(widths[-1])), outputs)


def random_two_term(rng, m=3, d0=2, d1=3, r=3, blocks=1):
    result = []
    for _ in range(blocks):
        d = d0+d1
        a = (0,)*d0 + tuple(rng.randrange(1 << d0) for _ in range(d1))
        terms = [[rng.randrange(1,4) for _ in range(m)] for _ in range(rng.randint(1,5))]
        masks = []
        for term in terms:
            value = 0
            for t in range(d):
                if t >= d0:
                    value |= rng.randrange(1 << r) << (t*r)
                else:
                    value |= rng.randrange(1 << r) << ((d+t)*r)
            masks.append(value)
        reg = product_register(terms, masks, 2*d*r, length=m)
        result.append(TemplateBlock(a, (0,)*d0+(1,)*d1, reg))
    return PortComplex(tuple(result), (0,)*r)


class Matrices(unittest.TestCase):
    def test_random_rank_updates(self):
        rng = random.Random(92371)
        for _ in range(1000):
            m, n, r = (rng.randrange(9) for _ in range(3))
            a = [rng.randrange(1 << n) for _ in range(m)]
            u = [rng.randrange(1 << r) for _ in range(m)]
            v = [rng.randrange(1 << n) for _ in range(r)]
            result = gf2.rank_update(a, n, u, v)
            d = gf2.add(a, gf2.mul(u,v))
            self.assertEqual(result['rank'], elementary_rank(d,n))
            self.assertLessEqual(max(result['core_shape']), 2*r)

    def test_reflexive_generalized_inverse(self):
        rng = random.Random(833)
        for _ in range(300):
            m, n = rng.randrange(12), rng.randrange(12)
            a = [rng.randrange(1 << n) for _ in range(m)]
            h,q = gf2.generalized_inverse(a,n)
            self.assertEqual(gf2.mul(gf2.mul(a,h),a), a)
            self.assertEqual(gf2.mul(gf2.mul(h,a),h),h)
            self.assertEqual(q,elementary_rank(a,n))

    def test_rank_factor(self):
        rng = random.Random(95)
        for _ in range(200):
            m,n = rng.randrange(12),rng.randrange(12)
            a = [rng.randrange(1 << n) for _ in range(m)]
            u,v = gf2.rank_factor(a,n)
            self.assertEqual(gf2.mul(u,v),a)
            self.assertEqual(len(v), elementary_rank(a,n))

    def test_singular_middle(self):
        ans = gf2.rank_update([1],1,[1],[1])
        self.assertEqual(ans['middle_rows'],[0])
        self.assertEqual(ans['rank'],0)

    def test_zero_ports_and_empty_dimensions(self):
        for m in range(4):
            for n in range(4):
                a = [0]*m
                self.assertEqual(gf2.rank_update(a,n,[0]*m,[])['rank'],0)

    def test_invalid_matrix(self):
        for a,n in [([-1],2),([4],2),([True],1)]:
            with self.assertRaises(ValueError): gf2.generalized_inverse(a,n)
        with self.assertRaises(ValueError): gf2.inverse([0])
        with self.assertRaises(ValueError): gf2.rank_update([0],1,[],[])


class Registers(unittest.TestCase):
    def test_random_reachable_and_pairings(self):
        rng = random.Random(32873)
        for _ in range(300):
            m,b,q = rng.randrange(7),rng.randrange(1,7),rng.randrange(1,13)
            reg = random_register(rng,m,b,q)
            ev = [reg.evaluate([(x >> j)&1 for j in range(m)]) for x in range(1 << m)]
            reach = reg.reachable()
            self.assertEqual(len(reach['evaluation_rows']),elementary_rank(ev,q))
            for word,value in zip(reach['witnesses'],reach['evaluation_rows']):
                self.assertEqual(reg.evaluate(word),value)
            actual_gram = [0]*q
            for value in ev:
                for j in range(q):
                    if value >> j & 1: actual_gram[j] ^= value
            predicted = gf2.mul(gf2.transpose(reg.outputs,q),
                                gf2.mul(reg.state_gram(),reg.outputs))
            self.assertEqual(predicted,actual_gram)

    def test_gram_is_not_rank(self):
        reg = product_register([[3]*4],[1],1)
        self.assertEqual(reg.state_gram(),[0])
        self.assertEqual(len(reg.reachable()['evaluation_rows']),1)

    def test_literals(self):
        for literal in range(4):
            reg = product_register([[literal]],[1],1)
            self.assertEqual([reg.evaluate([x]) for x in (0,1)],
                             [(literal >> x)&1 for x in (0,1)])

    def test_zero_register(self):
        reg = product_register([],[],5,length=100)
        self.assertEqual(reg.reachable()['evaluation_rows'],[])
        self.assertEqual(reg.state_gram(),[0])

    def test_empty_word(self):
        reg = product_register([[],[]],[1,2],2)
        self.assertEqual(reg.evaluate([]),3)
        self.assertEqual(reg.reachable()['witnesses'],[[]])

    def test_json_roundtrip(self):
        reg = random_register(random.Random(9),5,4,7)
        copy = Register.from_dict(json.loads(json.dumps(reg.to_dict())))
        self.assertEqual(copy,reg)

    def test_long_witnesses(self):
        reg = product_register([[2]*1000],[1],1)
        self.assertEqual(reg.reachable()['witnesses'],[[1]*1000])

    def test_invalid_input(self):
        with self.assertRaises(ValueError): Register((0,),(),0,(),0)
        with self.assertRaises(ValueError): Register((1,),(),0,(2,),1)
        with self.assertRaises(ValueError): product_register([[4]],[1],1)
        with self.assertRaises(ValueError): product_register([[1]],[1],1).evaluate([2])


class Complexes(unittest.TestCase):
    def test_random_two_term(self):
        rng = random.Random(12378)
        for _ in range(250):
            c = random_two_term(rng,m=rng.randrange(5),d0=rng.randint(1,3),
                                d1=rng.randint(1,3),r=rng.randrange(5),blocks=rng.randint(1,3))
            result = analyze(c)
            rows,degrees = expand(c)
            self.assertFalse(any(gf2.mul(rows,rows)))
            n = len(rows)
            self.assertEqual(result['homology_dimension'],n-2*elementary_rank(rows,n))

    def test_three_term_square_zero_accept_reject(self):
        rng = random.Random(8008)
        for _ in range(160):
            m = rng.randrange(4)
            # one port for 0->1, one for 1->2; random register functions.
            terms = [[rng.randrange(1,4) for _ in range(m)] for _ in range(4)]
            allowed = [1 << 2, 1 << 5, 1 << 6, 1 << 9]
            masks = [sum(bit for bit in allowed if rng.randrange(2)) for t in terms]
            reg = product_register(terms,masks,12,length=m)
            c = PortComplex((TemplateBlock((0,0,0),(0,1,2),reg),),(0,1))
            rows,_ = expand(c)
            valid = not any(gf2.mul(rows,rows))
            if valid:
                self.assertEqual(analyze(c)['homology_dimension'],
                                 len(rows)-2*elementary_rank(rows,len(rows)))
            else:
                with self.assertRaisesRegex(ValueError,'square to zero'): analyze(c)

    def test_nonzero_base_three_term(self):
        # Two template intervals in degrees 0->1 and 1->2, coupled by a port.
        # Run all single-entry legal degree-one ports, zero-length register.
        degrees=(0,1,1,2)
        a=(0,1,0,4)
        for source in range(4):
            for target in range(4):
                if degrees[target] != degrees[source]+1: continue
                mask=(1 << target) | (1 << (4+source))
                reg=product_register([[]],[mask],8)
                c=PortComplex((TemplateBlock(a,degrees,reg),),(degrees[source],))
                rows,_=expand(c)
                if any(gf2.mul(rows,rows)):
                    with self.assertRaises(ValueError): analyze(c)
                else:
                    self.assertEqual(analyze(c)['homology_dimension'],4-2*elementary_rank(rows,4))

    def test_examples_small(self):
        for m in range(8):
            for kind in ('singular','invertible','large_homology'):
                c=coupled_pair(m,kind)
                ans=analyze(c); rows,_=expand(c)
                self.assertEqual(ans['homology_dimension'],len(rows)-2*gf2.rank(rows))

    def test_connected_support(self):
        for m in range(2,7):
            c=connected_singular_pair(m)
            ans=analyze(c); rows,_=expand(c)
            self.assertEqual(ans['homology_dimension'],2)
            graph=[set() for _ in rows]
            for i,row in enumerate(rows):
                for j in gf2.bits(row): graph[i].add(j);graph[j].add(i)
            seen={0}; todo=[0]
            while todo:
                v=todo.pop()
                for w in graph[v]-seen: seen.add(w);todo.append(w)
            self.assertEqual(len(seen),len(rows))

    def test_huge_not_expanded(self):
        for m in (40,200,1000):
            c=connected_singular_pair(m)
            result=analyze(c)
            self.assertEqual(result['dimension'],1 << (m+1))
            self.assertEqual(result['homology_dimension'],2)
            self.assertEqual(result['middle_rows'],[0])
            self.assertIsNone(result['topological_verdict'])
            with self.assertRaises(ValueError): expand(c)

    def test_unsafe_cap_counterexample(self):
        result=analyze(coupled_pair(1,'large_homology'))
        self.assertEqual(result['base_homology_dimension'],4)
        self.assertEqual(result['homology_dimension'],2)
        self.assertFalse(result['rank_two_obstruction_from_budget'])
        self.assertEqual(result['base_dimension_safe_cap'],4)

    def test_obstruction(self):
        result=analyze(coupled_pair(40,'large_homology'))
        self.assertTrue(result['rank_two_obstruction_from_budget'])
        self.assertEqual(result['base_dimension_safe_cap'],5)

    def test_no_ports(self):
        c=random_two_term(random.Random(9),m=40,r=0)
        result=analyze(c)
        self.assertEqual(result['homology_dimension'],result['base_homology_dimension'])
        self.assertEqual(result['core_shape'],[0,0])

    def test_empty_complex(self):
        self.assertEqual(analyze(PortComplex((),()))['homology_dimension'],0)
        self.assertEqual(analyze(PortComplex((),(0,)))['homology_dimension'],0)

    def test_wrong_port_degree(self):
        c=coupled_pair(3)
        bad=PortComplex(c.blocks,(5,))
        with self.assertRaisesRegex(ValueError,'wrong degree'): analyze(bad)

    def test_bad_base(self):
        reg=product_register([],[],0)
        with self.assertRaises(ValueError):
            PortComplex((TemplateBlock((1,),(0,),reg),),())
        with self.assertRaises(ValueError):
            PortComplex((TemplateBlock((0,1,2),(0,1,2),reg),),())

    def test_roundtrip(self):
        c=random_two_term(random.Random(72))
        copy=PortComplex.from_dict(json.loads(json.dumps(c.to_dict())))
        self.assertEqual(copy,c)
        self.assertEqual(analyze(copy),analyze(c))
        with self.assertRaises(ValueError): PortComplex.from_dict({'format':'not-portkh'})



class MinimumPorts(unittest.TestCase):
    def test_random_exact_minimum(self):
        from portkh.minimize import minimize_ports
        rng=random.Random(23691)
        for _ in range(100):
            c=random_two_term(rng,m=rng.randrange(4),r=rng.randrange(7),blocks=rng.randint(1,3))
            new,report=minimize_ports(c)
            rows,_=expand(c);newrows,_=expand(new)
            self.assertEqual(newrows,rows)
            # Build the same base with zero ports, independently of optimizer.
            base=PortComplex(tuple(TemplateBlock(b.differential,b.degrees,
                    Register(b.register.widths,b.register.transitions,b.register.initial,
                             (0,)*b.register.widths[-1],0)) for b in c.blocks),())
            base_rows,_=expand(base)
            self.assertEqual(new.ports,elementary_rank(gf2.add(rows,base_rows),len(rows)))
            self.assertEqual(analyze(new)['homology_dimension'],analyze(c)['homology_dimension'])
            self.assertEqual([b.register.widths for b in new.blocks],[b.register.widths for b in c.blocks])

    def test_cancelling_duplicate_ports(self):
        from portkh.minimize import minimize_ports
        # d=2,r=2: identical constant columns/rows; UV=0 in characteristic two.
        reg=product_register([[3]*40],[ (3 << 2) | (3 << 4) ],8)
        c=PortComplex((TemplateBlock((0,1),(0,1),reg),),(0,0))
        new,report=minimize_ports(c)
        self.assertEqual(new.ports,0)
        self.assertEqual(analyze(new)['homology_dimension'],0)

    def test_multiple_degrees(self):
        from portkh.explicit import from_dense
        from portkh.minimize import minimize_ports
        c=from_dense([0,1,0,4],[0,1,1,2])
        new,report=minimize_ports(c)
        self.assertEqual(expand(c),expand(new))

if __name__=='__main__': unittest.main()
