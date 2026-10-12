"""Reproducible exact tests, independent finite oracles, and binary stress cases."""
from __future__ import annotations
import sys, json, random, time, unittest, platform
from pathlib import Path
from collections import Counter
from math import gcd
from itertools import product
from dataclasses import replace
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'code'))
import ranked_morse as rm
import sources as so
COUNTS=Counter()
STRESS=[]

class ResearchTests(unittest.TestCase):
    def test_01_signed_floor_sum_exhaustive(self):
        for n in range(13):
            for M in range(1,18):
                for a in range(-12,13):
                    for b in (-25,-13,-2,-1,0,1,7,19,31):
                        self.assertEqual(rm.floor_sum(n,M,a,b),sum((a*i+b)//M for i in range(n)))
                        COUNTS['signed_floor_sums']+=1

    def test_02_residue_counts(self):
        rng=random.Random(417802)
        for _ in range(14000):
            lo=rng.randrange(-30,31); hi=lo+rng.randrange(0,35)
            M=rng.randrange(1,70); a=rng.randrange(-120,121); b=rng.randrange(-500,501)
            t=rng.randrange(M+1)
            got=rm.residue_ge(lo,hi,M,a,b,t)
            self.assertEqual(got,sum((a*i+b)%M>=t for i in range(lo,hi+1)))
            COUNTS['residue_counts']+=1

    def test_03_exact_modular_constraints(self):
        rng=random.Random(372719)
        for _ in range(15000):
            M=rng.randrange(1,55); D=rng.randrange(1,10)
            lo=rng.randrange(-20,21); hi=lo+rng.randrange(20)
            sign=rng.choice([-1,1]); shift=rng.randrange(-30,31)
            au=rng.randrange(-80,81); av=sign*(au+rng.randrange(-4,5)*M)
            cu=rng.randrange(-90,91); cv=rng.randrange(-90,91)
            e=rm.Arc('U','V',lo,hi,sign,shift)
            image=sorted([sign*lo+shift,sign*hi+shift])
            p=rm.Prepared(rm.Packet((rm.Family('U',1,lo,hi),rm.Family('V',0,*image)),(),()),(e,),(),(0,0))
            c=rm.modular_constraints(p,M,D,{'U':au,'V':av},{'U':cu,'V':cv})[0][2]
            expected=max(1+D*((av*(sign*i+shift)+cv)%M)-D*((au*i+cu)%M) for i in range(lo,hi+1))
            self.assertEqual(c,expected)
            proof=rm.ModularProof(M,D,{'U':au,'V':av},{'U':cu,'V':cv},{'U':c,'V':0})
            self.assertTrue(rm.verify_modular(p,proof))
            self.assertFalse(rm.verify_modular(p,replace(proof,offsets={'U':c-1,'V':0})))
            COUNTS['modular_arc_constraints']+=1

    def test_04_affine_endpoint_constraints(self):
        rng=random.Random(61928)
        for _ in range(5000):
            lo=rng.randrange(-30,31); hi=lo+rng.randrange(30)
            sign=rng.choice([-1,1]); shift=rng.randrange(-30,31)
            image=sorted([sign*lo+shift,sign*hi+shift])
            a={'U':rng.randrange(-20,21),'V':rng.randrange(-20,21)}
            p=rm.Prepared(rm.Packet((rm.Family('U',1,lo,hi),rm.Family('V',0,*image)),(),()),(rm.Arc('U','V',lo,hi,sign,shift),),(),(0,0))
            c=rm.affine_constraints(p,a)[0][2]
            self.assertEqual(c,max(1+a['V']*(sign*i+shift)-a['U']*i for i in range(lo,hi+1)))
            self.assertTrue(rm.verify_affine(p,rm.AffineProof(a,{'U':c,'V':0})))
            self.assertFalse(rm.verify_affine(p,rm.AffineProof(a,{'U':c-1,'V':0})))
            COUNTS['affine_arc_constraints']+=1

    def test_05_offsets_against_exhaustive_oracle(self):
        names=('a','b','c')
        rng=random.Random(8712)
        for _ in range(500):
            edges=tuple((rng.choice(names),rng.choice(names),rng.randrange(-2,3)) for _ in range(rng.randrange(8)))
            answer=rm.solve_offsets(names,edges)
            # A feasible system with edge weights at most 2 has a nonnegative
            # longest-simple-path solution bounded by 4, independently enumerated.
            feasible=any(all(h[names.index(u)]>=h[names.index(v)]+c for u,v,c in edges)
                         for h in product(range(5),repeat=3))
            self.assertEqual(answer is not None,feasible)
            if answer is not None:
                self.assertTrue(all(answer[u]>=answer[v]+c for u,v,c in edges))
            COUNTS['difference_constraint_systems']+=1
        self.assertIsNone(rm.solve_offsets(('a','b'),(('a','b',0),('b','a',1))))
        self.assertIsNotNone(rm.solve_offsets(('a','b'),(('a','b',1),('b','a',-1))))

    def test_06_all_modular_paths_small(self):
        for N in range(2,44):
            for step in range(1,N):
                for start in sorted({0,N//2,N-1}):
                    packet,terminal=so.modular_path(N,step,start)
                    p=rm.prepare(packet)
                    expected=gcd(N,step)==1
                    self.assertTrue(rm.one_critical_vertex(p))
                    self.assertEqual(rm.explicit_acyclic(p),expected)
                    self.assertEqual(rm.explicit_collapse(p),expected)
                    proof=so.path_proof(packet,N,step,start)
                    self.assertEqual(proof is not None,expected)
                    if expected:
                        self.assertTrue(rm.verify_modular(p,proof))
                    COUNTS['modular_paths']+=1

    def test_07_closed_cycles_rejected(self):
        for N in range(2,45):
            for step in range(1,N):
                packet,_=so.modular_path(N,step,closed=True)
                p=rm.prepare(packet)
                self.assertFalse(rm.explicit_acyclic(p))
                self.assertFalse(rm.one_critical_vertex(p))
                if gcd(N,step)==1:
                    self.assertIsNone(so.path_proof(packet,N,step))
                COUNTS['closed_cycles']+=1

    def test_08_three_dimensional_sources(self):
        for N in range(2,17):
            for step in range(1,N):
                for fan in (3,4):
                    for start in sorted({0,N-1}):
                        facets=so.disk_fan(fan)
                        packet,metadata,bm=so.product_source(N,step,facets,start)
                        p=rm.prepare(packet)
                        self.assertTrue(so.surface_is_disk(facets))
                        self.assertTrue(so.compare_product_geometry(packet,metadata,N,step,facets,start,bm))
                        self.assertTrue(rm.one_critical_vertex(p))
                        expected=gcd(N,step)==1
                        self.assertEqual(rm.explicit_acyclic(p),expected)
                        self.assertEqual(rm.explicit_collapse(p),expected)
                        proof=so.product_proof(packet,N,step,facets,start)
                        self.assertEqual(proof is not None,expected)
                        if expected:
                            self.assertTrue(rm.verify_modular(p,proof))
                        COUNTS['three_dimensional_source_comparisons']+=1

    def test_09_reflected_coordinates(self):
        rng=random.Random(916)
        for _ in range(200):
            N=rng.choice([7,11,13,17,19,23]); step=rng.randrange(1,N); start=rng.randrange(N)
            facets=so.disk_fan(rng.choice([3,4,5]))
            packet,meta,bm=so.product_source(N,step,facets,start)
            p=rm.prepare(packet); proof=so.product_proof(packet,N,step,facets,start)
            names={f.name for f in packet.families if rng.randrange(2)}
            reflected,change=rm.reflect(p,names); q=rm.prepare(reflected)
            a={f:proof.multipliers[f]*r for f,(r,c) in change.items()}
            c={f:proof.multipliers[f]*z+proof.phases[f] for f,(r,z) in change.items()}
            transported=rm.ModularProof(proof.modulus,proof.scale,a,c,proof.offsets)
            self.assertTrue(rm.verify_modular(q,transported))
            self.assertTrue(rm.explicit_acyclic(q)); self.assertTrue(rm.explicit_collapse(q))
            self.assertEqual(p.counts,q.counts)
            COUNTS['family_reflections']+=1

    def test_10_disk_source_authentication(self):
        for n in range(3,24):
            self.assertTrue(so.surface_is_disk(so.disk_fan(n)));COUNTS['disk_source_checks']+=1
        bad=[(),((0,1,1),),((0,1,2),(0,1,2)),
             ((0,1,2),(0,1,3),(0,2,3),(1,2,3)), # sphere
             ((0,1,2),(0,3,4)), # pinched link at 0
             ((0,1,2),(3,4,5)), # disconnected
             ((0,1,2),(0,1,3),(0,1,4))] # nonmanifold edge
        for facets in bad:
            self.assertFalse(so.surface_is_disk(facets));COUNTS['disk_source_checks']+=1
        annulus=tuple(t for i in range(3) for t in ((i,(i+1)%3,3+(i+1)%3),(i,3+(i+1)%3,3+i)))
        self.assertFalse(so.surface_is_disk(annulus));COUNTS['disk_source_checks']+=1
        packet,meta,bm=so.product_source(7,2,annulus)
        p=rm.prepare(packet);proof=so.product_proof(packet,7,2,annulus)
        self.assertTrue(so.compare_product_geometry(packet,meta,7,2,annulus,base_matching=bm))
        self.assertTrue(rm.verify_modular(p,proof));self.assertTrue(rm.explicit_acyclic(p))
        self.assertFalse(rm.one_critical_vertex(p));self.assertFalse(rm.explicit_collapse(p))
        self.assertEqual(p.counts,(3,3,0,0))

    def test_11_affine_ranking_barrier(self):
        for m in range(2,70):
            N=2*m+1
            packet,_=so.modular_path(N,2)
            proof=so.path_proof(packet,N,2);p=rm.prepare(packet)
            ranks=[proof.scale*((proof.multipliers['V']*i+proof.phases['V'])%N)+proof.offsets['V'] for i in range(N)]
            self.assertTrue(min(ranks[::2])>max(ranks[1::2]))
            self.assertTrue(all((ranks[i+1]-ranks[i])*(ranks[i+2]-ranks[i+1])<0 for i in range(N-2)))
            # Any chosen global affine vertex slope in this exhaustive range fails.
            # The theorem, not this finite sample, proves impossibility for all slopes.
            for slope in range(-5,6):
                slopes={f.name:slope for f in packet.families}
                self.assertIsNone(rm.synthesize_affine(p,slopes))
            COUNTS['affine_barrier_examples']+=1

    def test_12_malformed_data_and_tampering(self):
        packet,_=so.modular_path(11,2)
        p=rm.prepare(packet); proof=so.path_proof(packet,11,2)
        m=packet.matching[0]
        corrupt=[replace(packet,matching=packet.matching+(m,)),
                 replace(packet,covers=packet.covers+(packet.covers[0],)),
                 replace(packet,matching=(replace(m,hi=1000),)),
                 replace(packet,covers=(replace(packet.covers[0],slope=2),)+packet.covers[1:]),
                 replace(packet,families=(replace(packet.families[0],lo=True),)+packet.families[1:]),
                 replace(packet,families=(replace(packet.families[0],hi=-1),)+packet.families[1:])]
        for bad in corrupt:
            with self.assertRaises(ValueError):rm.prepare(bad)
            COUNTS['malformed_packet_rejections']+=1
        # Opposite affine maps overlap in a singleton actual incidence.
        singleton=rm.Packet((rm.Family('E',1,0,2),rm.Family('V',0,0,2)),
                            (rm.Cover('E','V',0,2),rm.Cover('E','V',0,2,-1,2)),())
        with self.assertRaises(ValueError):rm.prepare(singleton)
        COUNTS['malformed_packet_rejections']+=1
        for bad in [replace(proof,modulus=0),replace(proof,scale=0),replace(proof,offsets={}),
                    replace(proof,multipliers={**proof.multipliers,'V':proof.multipliers['V']+1})]:
            self.assertFalse(rm.verify_modular(p,bad));COUNTS['rank_tampering_rejections']+=1
        # Deliberately break the first directed inequality by changing the source offset.
        e=p.arcs[0];bad=replace(proof,offsets={**proof.offsets,e.src:-10000})
        self.assertFalse(rm.verify_modular(p,bad));COUNTS['rank_tampering_rejections']+=1

    def test_13_saved_proof_independent_replay(self):
        text=(ROOT/'examples'/'prism_100bit.json').read_text()
        packet,proof=rm.loads_certificate(text)
        with patch.object(rm,'synthesize_modular',side_effect=AssertionError('producer called')),\
             patch.object(rm,'solve_offsets',side_effect=AssertionError('solver called')),\
             patch.object(rm,'expand',side_effect=AssertionError('expansion called')):
            p=rm.prepare(packet)
            self.assertTrue(rm.verify_modular(p,proof));self.assertTrue(rm.one_critical_vertex(p))
        COUNTS['saved_proof_replays']+=1

    def test_14_large_binary_without_expansion(self):
        for bits in (64,1024,4096,16384):
            N=2**bits+1;facets=so.disk_fan(4)
            with patch.object(rm,'expand',side_effect=AssertionError('expansion called')):
                t=time.perf_counter()
                packet,metadata,bm=so.product_source(N,2,facets)
                p=rm.prepare(packet);proof=so.product_proof(packet,N,2,facets)
                self.assertIsNotNone(proof);self.assertTrue(rm.verify_modular(p,proof))
                self.assertTrue(rm.one_critical_vertex(p));self.assertTrue(so.surface_is_disk(facets))
                text=rm.dumps_certificate(packet,proof)
                p2,proof2=rm.loads_certificate(text)
                self.assertTrue(rm.verify_modular(rm.prepare(p2),proof2))
                STRESS.append({'N_bits':N.bit_length(),'families':len(packet.families),
                               'covers':len(packet.covers),'matches':len(packet.matching),
                               'certificate_bytes':len(text.encode()),'seconds':time.perf_counter()-t})
            COUNTS['huge_binary_product_checks']+=1

    def test_15_euclidean_worst_case(self):
        a,b=1,1
        while b.bit_length()<1024:a,b=b,a+b
        # Consecutive Fibonacci integers force a long Euclidean chain.
        self.assertEqual(rm.floor_sum(b,b,a,0),(a-1)*(b-1)//2)
        self.assertEqual(rm.residue_ge(0,b-1,b,a,0,b//2),b-b//2)
        packet,_=so.modular_path(b,a)
        proof=so.path_proof(packet,b,a)
        self.assertTrue(rm.verify_modular(rm.prepare(packet),proof))
        COUNTS['fibonacci_binary_checks']+=3

    def test_16_modulus_one_and_signed_affine(self):
        # A single interval has a point-collapse and also a constant-residue rank.
        packet=rm.Packet((rm.Family('A',0,-2,-2),rm.Family('B',0,7,7),rm.Family('E',1,10,10)),
                         (rm.Cover('E','A',10,10,1,-12),rm.Cover('E','B',10,10,-1,17)),
                         (rm.Match(0,10,10),))
        p=rm.prepare(packet);maps={f.name:0 for f in packet.families}
        proof=rm.synthesize_modular(p,1,1,maps,maps)
        self.assertTrue(rm.verify_modular(p,proof));self.assertTrue(rm.explicit_collapse(p))
        aproof=rm.synthesize_affine(p,{f.name:(-1 if f.dim else 2) for f in packet.families})
        self.assertTrue(rm.verify_affine(p,aproof))
        packet2,aproof2=rm.loads_certificate(rm.dumps_certificate(packet,aproof))
        self.assertTrue(rm.verify_affine(rm.prepare(packet2),aproof2))
        COUNTS['boundary_contract_checks']+=1

    def test_17_relative_product_collapse(self):
        annulus=tuple(t for i in range(3) for t in ((i,(i+1)%3,3+(i+1)%3),(i,3+(i+1)%3,3+i)))
        for facets in (so.disk_fan(3),so.disk_fan(6),annulus):
            for N in range(3,23):
                for step in range(1,N):
                    if gcd(N,step)!=1:continue
                    packet,meta,bm=so.product_source(N,step,facets,base_matching=())
                    p=rm.prepare(packet);proof=so.product_proof(packet,N,step,facets)
                    self.assertTrue(rm.verify_modular(p,proof))
                    expected=frozenset((f,i) for f,lo,hi in p.critical for i in range(lo,hi+1))
                    self.assertEqual(rm.explicit_collapse_remainder(p),expected)
                    self.assertTrue(all(meta[f][0]==0 and i==(-step)%N for f,i in expected))
                    self.assertEqual(len(expected),len(so.simplex_faces(facets)))
                    COUNTS['relative_product_collapses']+=1

    def test_18_arbitrary_small_simplicial_matchings(self):
        rng=random.Random(601212)
        bases=[((0,1,2),),((0,1,2,3),),so.disk_fan(4),
               ((0,1,2),(0,1,3),(0,2,3),(1,2,3))]
        for _ in range(1000):
            facets=rng.choice(bases);cells=so.simplex_faces(facets)
            ids={s:'S'+str(j) for j,s in enumerate(cells)}
            covers=tuple(rm.Cover(ids[s],ids[t],0,0) for s,t in so.base_covers(cells))
            order=list(range(len(covers)));rng.shuffle(order)
            matched=set();ms=[]
            for k in order:
                c=covers[k]
                if c.upper not in matched and c.lower not in matched and rng.randrange(4):
                    ms.append(rm.Match(k,0,0));matched.update([c.upper,c.lower])
            packet=rm.Packet(tuple(rm.Family(ids[s],len(s)-1,0,0) for s in cells),covers,tuple(ms))
            p=rm.prepare(packet);zeros={f.name:0 for f in packet.families}
            proof=rm.synthesize_modular(p,1,1,zeros,zeros)
            acyclic=rm.explicit_acyclic(p)
            self.assertEqual(proof is not None,acyclic)
            if acyclic:
                self.assertTrue(rm.verify_modular(p,proof))
                critical=set(ids.values())-matched
                if all(c.upper not in critical or c.lower in critical for c in covers):
                    self.assertEqual(rm.explicit_collapse_remainder(p),frozenset((x,0) for x in critical))
                if rm.one_critical_vertex(p):self.assertTrue(rm.explicit_collapse(p))
            COUNTS['arbitrary_simplicial_matchings']+=1

if __name__=='__main__':
    start=time.perf_counter()
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(ResearchTests)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    record={'schema':'modular-morse-validation-v1','python':platform.python_version(),
            'platform':platform.platform(),'tests_run':result.testsRun,'failures':len(result.failures),
            'errors':len(result.errors),'skipped':len(result.skipped),'counted_cases':dict(COUNTS),
            'total_counted_cases':sum(COUNTS.values()),'binary_stress':STRESS,
            'elapsed_seconds':time.perf_counter()-start,
            'native_repository_tests_run':False,'native_knot_benchmarks_run':False}
    (ROOT/'results'/'validation.json').write_text(json.dumps(record,indent=2)+'\n')
    sys.exit(not result.wasSuccessful())
