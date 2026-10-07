"""Independent bounded exact arithmetic and geometry regressions for Report282."""
import sys
sys.dont_write_bytecode = True
import ast
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
ROOT=Path(__file__).absolute().parents[1]
COMPANION=ROOT/'companion/exact_checks.py'
spec=importlib.util.spec_from_file_location('report282_checks',COMPANION)
e=importlib.util.module_from_spec(spec); spec.loader.exec_module(e)


class SymbolicTests(unittest.TestCase):
    def test_fixed_identities_and_independent_expansions(self):
        d=e.exact_identities()
        self.assertEqual(d['t'],(-1882-59*10477,-176*10477))
        self.assertEqual(d['b'],(1882+59*10479,176*10479))
        self.assertEqual(d['beta'],(2*d['t'][0]-12-3*d['b'][0],2*d['t'][1]-3*d['b'][1]))
        self.assertEqual(d['e'],(-3100876,-9222672))
        self.assertEqual(d['maynard_numerator'],(-3100872,-9222672))
        self.assertEqual(d['tb'],(118,352))
        self.assertEqual(d['fgK'],(-270,-1536))

    def test_exact_coefficient_and_printed_certificates(self):
        for fn,count in ((e.coefficient_certificates,17),(e.printed_comparison_certificates,8),(e.near_maximal_constants,12)):
            d=fn();self.assertEqual(d['count'],count);self.assertTrue(all(d['checks'].values()))
        self.assertTrue(e.strict_for_nonnegative_h((1,3),(2,3)))
        self.assertFalse(e.strict_for_nonnegative_h((1,4),(2,3)))
        self.assertFalse(e.strict_for_nonnegative_h((2,1),(2,2)))
        for q in range(1,513):
            d=e.recurrence_budget(q)
            self.assertEqual(d['r'],Fraction(1,128*q*q))
            self.assertGreaterEqual(d['v'],Fraction(19,64))
            self.assertGreaterEqual(d['s'],Fraction(63,64))
        self.assertEqual(e.recurrence_budget(1)['v'],Fraction(19,64))
        for q in (True,0,513,1.0,'1'):
            with self.assertRaises(ValueError):e.recurrence_budget(q)

    def test_no_evaluation_of_giant_powers_or_assert_validation(self):
        text=COMPANION.read_text();tree=ast.parse(text)
        self.assertFalse(any(isinstance(n,ast.Assert) for n in ast.walk(tree)))
        self.assertFalse(any(isinstance(n,ast.BinOp) and isinstance(n.op,ast.Pow) for n in ast.walk(tree)))
        self.assertEqual(sum(isinstance(n,ast.BinOp) and isinstance(n.op,ast.LShift) for n in ast.walk(tree)),1)
        calls={n.func.id for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name)}
        self.assertFalse(calls & {'eval','exec','compile','pow','float'})
        self.assertNotIn('set_int_max_str_digits(',text)
        with self.assertRaises(RuntimeError):e.require(False,'survives -O')
        for value in (1,None,'yes',[]):
            with self.assertRaises(RuntimeError):e.require(value,'strict Boolean')

    def test_affine_and_small_power_bounds(self):
        self.assertEqual(e.pow2_small(30),1073741824)
        self.assertEqual(e.pow2_small(0),1)
        for value in (True,False,-1,31,1048576,1.0,'3',None):
            with self.subTest(value=value),self.assertRaises(ValueError):e.pow2_small(value)
        for value in ([1,2],(True,1),(1,2,3),(100000001,0),('1',2)):
            with self.subTest(value=value),self.assertRaises(ValueError):e.affine(value)
        with self.assertRaises(ValueError):e.add((100000000,0),(1,0))
        with self.assertRaises(ValueError):e.scale(2,(100000000,0))
        with self.assertRaises(ValueError):e.scale(True,(1,0))


class RoundingTests(unittest.TestCase):
    def test_floor_half_integer_division_boundaries(self):
        for x,expected in ((Fraction(8),4),(Fraction(899,100),4),(Fraction(9),4),
                           (Fraction(999,100),4),(Fraction(10),5),(Fraction(17,2),4)):
            self.assertEqual(e.floor_half(x),expected)
            self.assertGreaterEqual(Fraction(expected),x/4)
        self.assertNotEqual(e.floor_half(Fraction(9)),Fraction(9,2))

    def test_two_unit_and_ceiling_budgets(self):
        for d in range(1,9):
            for n in range(4*d,32*d):
                x=Fraction(n,d)
                self.assertEqual(e.floor_predecessor(x),n//d-1)
                self.assertGreaterEqual(e.floor_predecessor(x),x/2)
                self.assertEqual(e.ceiling_budget(x),(n+d-1)//d)
        self.assertEqual(e.ceiling_budget(Fraction(1)),1)

    def test_exact_rational_and_domain_caps(self):
        for fn,minimum in ((e.floor_half,8),(e.floor_predecessor,4),(e.ceiling_budget,1)):
            for value in (True,minimum,float(minimum),str(minimum),Fraction(minimum)-Fraction(1,100),
                          Fraction(65537),Fraction(65537,65536),Fraction(1,65537)):
                with self.subTest(fn=fn.__name__,value=value),self.assertRaises(ValueError): fn(value)

    def test_diagnostic_case_counts(self):
        self.assertEqual(e.rounding_diagnostics(),dict(floor_half=7632,floor_predecessor=3824,ceiling=2056))


class GeometryTests(unittest.TestCase):
    def test_selected_short_parent_from_square_budget(self):
        for m in range(3,65):
            for r in (m,m+1):
                self.assertEqual(e.short_parent_budget(m,r,m*m),2*(r-1))
                self.assertLess(e.short_parent_budget(m,r,m*m),m*m)
        for args in ((2,3,9),(65,65,5000),(3,5,9),(3,4,8),(4,5,15),(True,4,16)):
            with self.subTest(args=args),self.assertRaises(ValueError):e.short_parent_budget(*args)

    def test_exact_clean_square_absorption(self):
        for denominator in range(1,9):
            for numerator in range(3*denominator,32*denominator+1):
                x=Fraction(numerator,denominator)
                self.assertEqual(e.square_absorption(x),x*x/2-1)
                self.assertGreaterEqual(e.square_absorption(x),x)
        for value in (3,True,3.0,Fraction(2999,1000),Fraction(65537)):
            with self.subTest(value=value),self.assertRaises(ValueError):e.square_absorption(value)

    def test_rectification_both_orientations_and_carrier(self):
        one=e.rectify_progression(31,13,1,3,4)
        reverse=e.rectify_progression(31,13,10,28,4)
        self.assertEqual(one,reverse)
        self.assertEqual(one,dict(points=(1,4,7,10),stride=3,span=9))
        # Even a composite normalized modulus is safe under strict shortness.
        self.assertEqual(e.rectify_progression(30,10,8,28,4)['points'],(2,4,6,8))

    def test_exhaustive_small_contained_progressions(self):
        count=0
        for N in (11,13,17):
            for r in range(2,(N+1)//2):
                for start in range(r):
                    for step in range(1,N):
                        for length in range(2,r+1):
                            points=tuple((start+i*step)%N for i in range(length))
                            if len(set(points))==length and max(points)<r:
                                d=e.rectify_progression(N,r,start,step,length)
                                self.assertEqual(d['points'],tuple(sorted(points)))
                                self.assertLessEqual(d['span'],r-1);count+=1
        self.assertEqual(count,490)

    def test_shortness_properness_containment_and_type_guards(self):
        bad=((17,10,0,1,2),(31,13,12,1,2),(15,7,0,5,4),
             (True,4,0,1,2),(258,4,0,1,2),(31,13,0,0,2),
             (31,13,0,1,1),(31,13,0,1,14))
        for args in bad:
            with self.subTest(args=args),self.assertRaises(ValueError): e.rectify_progression(*args)
        # Without strict shortness the sequence can have two integer differences.
        points=(0,7,3)
        self.assertNotEqual(points[1]-points[0],points[2]-points[1])
        with self.assertRaises(ValueError):e.rectify_progression(11,8,0,7,3)

    def test_balanced_partition_and_residue_chains(self):
        for L in range(2,17):
            for n in range(L-1,100):
                sizes=e.balanced_sizes(n,L)
                self.assertEqual(sum(sizes),n)
                self.assertEqual(len(sizes),(n+L-1)//L)
                self.assertGreaterEqual(min(sizes),(L+1)//2)
                self.assertLessEqual(max(sizes),L)
        self.assertEqual(e.balanced_sizes(8,7),(4,4))
        parents=e.aligned_parents(22,8,3)
        self.assertEqual(sorted(x for parent in parents for x in parent),list(range(22)))
        for parent in parents:
            self.assertTrue(4 <= len(parent) <= 8)
            self.assertTrue(all(y-x==3 for x,y in zip(parent,parent[1:])))

    def test_balanced_and_aligned_caps(self):
        for args in ((0,2),(513,2),(4,6),(1,1),(5,65),(True,2),(5,True)):
            with self.subTest(args=args),self.assertRaises(ValueError): e.balanced_sizes(*args)
        for args in ((21,8,3),(513,8,3),(20,21,1),(20,2,True),(20,2,0)):
            with self.subTest(args=args),self.assertRaises(ValueError): e.aligned_parents(*args)

    def test_endpoint_cover_keeps_terminal_mass(self):
        self.assertEqual(e.contained_cover(8,3),((0,1,2),(3,4,5),(5,6,7)))
        self.assertEqual(e.contained_cover(6,3),((0,1,2),(3,4,5)))
        for n in range(1,65):
            for k in range(1,n+1):
                blocks=e.contained_cover(n,k)
                self.assertEqual(set(x for block in blocks for x in block),set(range(n)))
                self.assertTrue(all(len(b)==k and min(b)>=0 and max(b)<n for b in blocks))
                self.assertLess(k*len(blocks),2*n)
        for args in ((0,1),(513,1),(5,6),(5,True),(5,0)):
            with self.subTest(args=args),self.assertRaises(ValueError): e.contained_cover(*args)

    def test_square_fit_full_side_without_square_root(self):
        self.assertEqual(e.square_fit(25,25,3,9),8)
        self.assertEqual(e.square_fit(9,9,1,9),8)
        for args in ((20,21,1,2),(20,20,4,6),(20,20,1,1),(65,20,1,2),(20,20,True,2)):
            with self.subTest(args=args),self.assertRaises(ValueError):e.square_fit(*args)

    def test_contained_square_and_arbitrary_endpoint_mass(self):
        for L,M,j in ((7,4,2),(11,3,4),(16,5,3),(25,9,3),(32,16,2)):
            d=e.contained_square_cover(L,M,j);k=M-1
            pairs=set()
            for col in d['columns']:
                self.assertTrue(all(y-x==j for x,y in zip(col,col[1:])))
                for row in d['rows']:pairs.update((x,y) for x in col for y in row)
            self.assertEqual(pairs,{(x,y) for x in range(L) for y in range(M)})
            self.assertLess(d['capacity'],4*L*M)
            for target in ((0,0),(L-1,M-1),(L//2,M//2)):
                self.assertTrue(any(target[0] in c and target[1] in r for c in d['columns'] for r in d['rows']))
                self.assertGreaterEqual(Fraction(1,k*k),Fraction(1,4*L*M))
        for args in ((7,5,2),(65,5,2),(7,1,2),(7,5,True)):
            with self.subTest(args=args),self.assertRaises(ValueError):e.contained_square_cover(*args)

    def test_geometry_diagnostic_inventory(self):
        d=e.geometry_diagnostics()['counts']
        self.assertEqual(d['mass_averaging_cases'],25)
        self.assertEqual(d['short_parent_budgets'],372)
        self.assertGreater(d['rectifications'],1000)
        self.assertGreater(d['balanced_partitions'],3000)
        self.assertGreater(d['square_fits'],10000)


class PartitionAndExtensionTests(unittest.TestCase):
    def test_source16_blocks_and_whole_partition(self):
        self.assertEqual(e.source16_blocks(17,6),(6,11))
        self.assertEqual(e.source16_blocks(12,6),(6,6))
        for n in range(2,100):
            for L in range(2,min(n,16)+1):
                sizes=e.source16_blocks(n,L)
                self.assertEqual(sum(sizes),n)
                self.assertTrue(all(L<=x<2*L for x in sizes))
        for args in ((97,3,4,7),(128,2,5,8),(32,2,8,2)):
            cells=e.source16_partition(*args)
            self.assertEqual(sorted(x for cell in cells for x in cell),list(range(args[0])))
            self.assertTrue(all(args[1]<=len(cell)<2*args[1] for cell in cells))
        for args in ((5,6),(513,4),(6,True),(0,2)):
            with self.assertRaises(ValueError):e.source16_blocks(*args)
        for args in ((31,2,8,2),(256,2,8,33),(32,1,8,1),(32,2,9,1),(32,2,8,True)):
            with self.assertRaises(ValueError):e.source16_partition(*args)

    def test_rounded_row_models_and_hypothesis_failures(self):
        self.assertEqual(e.rounded_row_model(Fraction(1,2),Fraction(1,2),Fraction(1,2),Fraction(6)),3)
        self.assertEqual(e.rounded_row_model(Fraction(1,4),Fraction(1,4),Fraction(1,4),Fraction(16)),4)
        for args in ((Fraction(1),Fraction(1,2),Fraction(1,2),Fraction(6)),
                     (Fraction(1,2),Fraction(0),Fraction(1,2),Fraction(6)),
                     (Fraction(1,2),Fraction(1,2),Fraction(1,2),Fraction(5)),
                     (Fraction(1,2),Fraction(1,2),Fraction(0),Fraction(6)),
                     (True,Fraction(1,2),Fraction(1,2),Fraction(6))):
            with self.assertRaises(ValueError):e.rounded_row_model(*args)

    def test_dense_extension_on_a_domain_not_containing_zero(self):
        self.assertEqual(e.dense_extension(5,5,(1,2,3,4),(2,4,1,3)),(0,2,4,1,3))
        self.assertEqual(e.dense_extension(6,3,(0,1,2,3,4),(0,2,1,0,2)),(0,2,1,0,2,1))
        self.assertEqual(e.dense_extension(1,4,(0,),(0,)),(0,))

    def test_strict_density_is_essential_and_bad_maps_are_rejected(self):
        # A={0,1,3} has exactly 3/4 density in Z/4Z; this map to Z/3Z
        # is partially additive but cannot extend to a homomorphism.
        self.assertTrue(e.partial_additive(4,3,(0,1,3),(0,1,2)))
        with self.assertRaises(ValueError):e.dense_extension(4,3,(0,1,3),(0,1,2))
        for args in ((5,5,(1,2,3,4),(2,4,1,2)),(5,5,(2,1,3,4),(4,2,1,3)),
                     (5,5,(1,1,3,4),(2,2,1,3)),(8,5,(1,2,3,4),(2,4,1,3)),
                     (5,6,(1,2,3,4),(2,4,1,3)),(5,5,(1,2,3,4),(2,4,1,5)),
                     (True,5,(0,),(0,)),(5,5,[1,2,3,4],(2,4,1,3))):
            with self.assertRaises(ValueError):e.dense_extension(*args)

    def test_exhaustive_diagnostic_bounds(self):
        d=e.dense_extension_diagnostics()
        self.assertGreater(d['candidate_maps'],10000)
        self.assertGreater(d['partially_additive_maps'],100)
        self.assertEqual(d['nonzero_multiplier_kernels'],128*127//2)
        p=e.partition_and_rounding_diagnostics()['counts']
        self.assertEqual(p['recurrence_budget_samples'],512)
        self.assertEqual(p['rounded_row_models'],81)
        self.assertGreater(p['source16_partitions'],1000)


class SourceTests(unittest.TestCase):
    def fixture(self,name='Section10.lean'):
        raw=b'precise\r\nsource\n'
        if name=='Mathlib_Fourier_ZMod.lean':
            repository='leanprover-community/mathlib4';commit=e.MATHLIB_PIN;path='Mathlib/Analysis/Fourier/ZMod.lean'
        else:
            repository='VladimirReshetnikov/ProveIt';commit=e.MAIN_PIN
            path='Combinatorics/Ramsey/Lean/GowersSzemeredi/'+name
        row=dict(name=name,repository=repository,repository_path=path,commit=commit,
                 url='https://github.com/'+repository+'/blob/'+commit+'/'+path,
                 bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),
                 git_blob_sha1=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest())
        return raw,row

    def test_source_exact_bytes_and_line_endings(self):
        for name in ('Section10.lean','Mathlib_Fourier_ZMod.lean'):
            raw,row=self.fixture(name);self.assertEqual(e.verify_source_bytes(raw,row),row['git_blob_sha1'])
            with self.assertRaises(RuntimeError):e.verify_source_bytes(raw.replace(b'\r\n',b'\n'),row)
            for data in ('text',b'',b'x'*(e.MAX_SOURCE_SNAPSHOT_BYTES+1)):
                with self.assertRaises(ValueError):e.verify_source_bytes(data,row)

    def test_strict_source_record_and_url_binding(self):
        raw,base=self.fixture()
        changes=({'name':'../Section10.lean'},{'name':'Section10.lean/extra'},
                 {'bytes':True},{'bytes':len(raw)+1},{'commit':'main'}, {'commit':'a'*40},
                 {'sha256':'0'*64},{'git_blob_sha1':'0'*40},{'repository':'untrusted/other'},
                 {'url':'https://example.com/fake'},{'repository_path':'elsewhere'},{'extra':'x'})
        for change in changes:
            row=dict(base);row.update(change)
            with self.subTest(change=change),self.assertRaises((ValueError,RuntimeError)):e.verify_source_bytes(raw,row)

    def test_manifest_inventory_duplicates_and_caps(self):
        raw,row=self.fixture();files={'provenance/sources/'+row['name']:raw}
        self.assertEqual(e.validate_source_manifest([row],files),1)
        for rows in ([row,row],[],{},[row]*65,[{}]):
            with self.subTest(rows=str(rows)[:60]),self.assertRaises((ValueError,RuntimeError)):e.validate_source_manifest(rows,files)
        for data in ({},{**files,'provenance/sources/Extra.lean':raw},{0:raw}):
            with self.assertRaises((ValueError,RuntimeError)):e.validate_source_manifest([row],data)

    def test_frozen_source_inventory(self):
        d=e.source_diagnostics()
        self.assertEqual(d['verified_source_snapshots'],20)
        self.assertEqual(d['verified_lean_snapshots'],19)
        self.assertEqual(d['pins'],sorted([e.MAIN_PIN,e.MATHLIB_PIN]))


class CommandTests(unittest.TestCase):
    def test_builder_verify_from_unrelated_working_directory(self):
        with tempfile.TemporaryDirectory(prefix='report282-cli-cwd-') as tmp:
            r=subprocess.run([sys.executable,'-I','-B',str(ROOT/'build.py'),'verify'],
                             cwd=tmp,capture_output=True,timeout=10)
            self.assertEqual(r.returncode,0,r.stderr)
            self.assertIn(b'PASS: Report282',r.stdout)
            self.assertEqual(list(Path(tmp).iterdir()),[])
            r=subprocess.run([sys.executable,'-I','-B',str(ROOT/'build.py'),'verify','--no-zip'],
                             cwd=tmp,capture_output=True,timeout=10)
            self.assertEqual(r.returncode,1)
            self.assertIn(b'only valid for reproduce',r.stderr)

    def test_unknown_cli_is_rejected(self):
        r=subprocess.run([sys.executable,'-I','-B',str(COMPANION),'--density','0.1'],capture_output=True,timeout=10)
        self.assertEqual(r.returncode,2);self.assertEqual(r.stdout,b'')
        self.assertIn(b'unrecognized arguments',r.stderr)


if __name__=='__main__':unittest.main()
