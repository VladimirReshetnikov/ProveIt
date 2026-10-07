"""Independent exact checks and strict bounded-interface tests for Report279."""
import sys
sys.dont_write_bytecode = True
import ast
from collections import Counter
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).absolute().parents[1]
COMPANION = ROOT/'companion/exact_checks.py'
spec = importlib.util.spec_from_file_location('report279_checks', COMPANION)
e = importlib.util.module_from_spec(spec); spec.loader.exec_module(e)


class ExponentTests(unittest.TestCase):
    def test_fixed_integer_identities_and_symbolic_large_constants(self):
        result = e.exponent_diagnostics()
        self.assertEqual(result['integer_identities']['t'], 7995833)
        self.assertEqual(result['integer_identities']['Q_upper_log2'], 9437184)
        self.assertEqual(result['integer_identities']['z0_multiplier'], 2531)
        self.assertEqual(result['integer_identities']['complete_square_binary_exponent'],386)
        self.assertEqual(result['integer_identities']['complete_square_alpha_exponent'],1856)
        self.assertEqual(result['symbolic_constants']['beta0'], '2^(-13*2^9437184)')
        self.assertTrue(all(type(x) is str for x in e.symbolic_constants().values()))
        self.assertEqual(e.pow2_small(0), 1)
        self.assertEqual(e.pow2_small(30), 1073741824)

    def test_no_assert_or_dynamic_evaluation_or_unbounded_power_evaluator(self):
        tree = ast.parse(COMPANION.read_text())
        self.assertFalse(any(isinstance(node, ast.Assert) for node in ast.walk(tree)))
        calls = {node.func.id for node in ast.walk(tree)
                 if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)}
        self.assertFalse(calls & {'eval','exec','compile','pow','Fraction'})
        shifts = [node for node in ast.walk(tree) if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift)]
        self.assertEqual(len(shifts), 1)
        self.assertNotIn('set_int_max_str_digits(', COMPANION.read_text())

    def test_strict_power_cap(self):
        for value in (True, False, -1, 31, 762, 7995833, 9437184, 1.0, '3', None):
            with self.subTest(value=value), self.assertRaises(ValueError): e.pow2_small(value)
        with self.assertRaises(RuntimeError): e.require(False, 'active in every mode')


class GeometryTests(unittest.TestCase):
    def test_f47_geometry(self):
        result = e.difference_obstruction(47,5)
        self.assertEqual(result['difference_intersection'], [0])
        self.assertEqual(result['scanned_nonzero_steps'],46)
        self.assertEqual(result['common_nonzero_steps'],[])
        s=set(range(5)); u={5*j for j in range(5)}
        # Independent first-two-point comparison, without using difference sets.
        for x0,x1,y0,y1 in product(s,s,u,u):
            if x0 != x1 and y0 != y1:
                self.assertNotEqual((x1-x0)%47,(y1-y0)%47)

    def test_composite_boundary_is_also_geometric(self):
        self.assertEqual(e.difference_obstruction(25,5)['difference_intersection'],[0])
        self.assertEqual(e.progression(12,1,4,3),(1,5,9))
        with self.assertRaises(RuntimeError): e.progression(12,1,4,4)

    def test_invalid_geometry_parameters(self):
        for args in ((True,0,1,1),(1,0,1,1),(8193,0,1,1),(7,-1,1,1),
                     (7,7,1,1),(7,0,0,1),(7,0,7,1),(7,0,1,0),(7,0,1,8),
                     (257,0,1,129),(7,0,1,1.0)):
            with self.subTest(args=args),self.assertRaises(ValueError): e.progression(*args)
        for args in ((24,5),(47,True),(8193,5),(4096,65)):
            with self.subTest(args=args),self.assertRaises(ValueError): e.difference_obstruction(*args)


class CoverTests(unittest.TestCase):
    def test_terminal_overlapping_block_is_contained(self):
        self.assertEqual(e.cover_indices(7,3),((0,1,2),(3,4,5),(4,5,6)))
        self.assertEqual(e.cover_indices(6,3),((0,1,2),(3,4,5)))
        self.assertEqual(e.cover_indices(1,1),((0,),))
        self.assertEqual(e.residue_cover(7,2,3),((0,2,4),(2,4,6),(1,3,5)))

    def test_all_small_subset_masses(self):
        checked=0
        for length,height,stride,side in ((3,3,1,2),(4,3,2,2),(4,4,1,3)):
            sb=e.residue_cover(length,stride,side); ub=e.cover_indices(height,side)
            points=list(product(range(length),range(height)))
            for mask in range(1<<len(points)):
                selected={point for i,point in enumerate(points) if mask & (1<<i)}
                masses=[len(selected & set(product(b,c))) for b in sb for c in ub]
                self.assertGreaterEqual(sum(masses),len(selected))
                self.assertGreaterEqual(max(masses)*4*length*height,len(selected)*side*side)
                checked+=1
        self.assertEqual(checked,70144)

    def test_invalid_cover_parameters(self):
        for args in ((0,1),(129,1),(3,0),(3,4),(3,True),(3.0,1)):
            with self.subTest(args=args),self.assertRaises(ValueError): e.cover_indices(*args)
        for args in ((65,1,1),(5,0,1),(5,6,1),(5,2,3),(5,True,1)):
            with self.subTest(args=args),self.assertRaises(ValueError): e.residue_cover(*args)


class CountNormalizationTests(unittest.TestCase):
    def test_eightfold_convolution_against_direct_tuples(self):
        for modulus,width in ((3,2),(5,2),(7,3)):
            direct=Counter(sum(xs)%modulus for xs in product(range(width),repeat=8))
            self.assertEqual(e.cyclic_sum_counts(modulus,width,8),
                             tuple(direct[i] for i in range(modulus)))
            energy=sum(direct[i]*direct[i] for i in range(modulus))
            self.assertGreaterEqual(modulus*energy,width**16)

    def test_full_strip_exact_count(self):
        for modulus in (2,3,5):
            rho=e.cyclic_sum_counts(modulus,modulus,8)
            self.assertEqual(rho,(modulus**7,)*modulus)
            energy=sum(x*x for x in rho)
            self.assertEqual(energy,modulus**15)
            self.assertEqual(modulus**16*energy,modulus**31)

    def test_cyclotomic_fourier_normalization(self):
        self.assertEqual(e.fourier_polynomial(3,1,0),(3,0))
        self.assertEqual(e.fourier_polynomial(3,2,0),(6,0))
        self.assertEqual(e.fourier_polynomial(3,2,1),(0,-3))
        self.assertEqual(e.fourier_polynomial(3,2,2),(3,3))
        for p in (2,3,5,7):
            for frequency in range(1,p):
                self.assertEqual(e.fourier_polynomial(p,p,frequency),(0,)*(p-1))
        result=e.strip_diagnostics()
        self.assertEqual(result['zero_frequency'],'N*b')
        self.assertGreater(result['exact_fourier_coefficients'],100)

    def test_counting_caps(self):
        for args in ((32,1,1),(1,1,1),(3,0,1),(3,4,1),(3,1,0),(3,1,9),(3,1,True)):
            with self.subTest(args=args),self.assertRaises(ValueError): e.cyclic_sum_counts(*args)
        for p in (True,1,4,9,32):
            with self.subTest(p=p),self.assertRaises(ValueError): e.prime_small(p)
        for values in ((1,2,3,4),(True,0),[1<<129,0],(1.0,0),'12'):
            with self.subTest(values=values),self.assertRaises(ValueError): e.cyclotomic_reduce(values)


class ConstructiveTests(unittest.TestCase):
    def test_rectification_in_each_orientation(self):
        self.assertEqual(e.rectify_short_carrier(11,6,(5,3,1)),
                         dict(stride=2,reversed=True,indices=(1,3,5)))
        self.assertEqual(e.rectify_short_carrier(11,6,(0,2,4)),
                         dict(stride=2,reversed=False,indices=(0,2,4)))
        for length in range(2,5):
            for values in product(range(4),repeat=length):
                if len(set(values)) == length and len({(values[j+1]-values[j]) % 7 for j in range(length-1)}) == 1:
                    result=e.rectify_short_carrier(7,4,values)
                    self.assertEqual(set(result['indices']),set(values))
                    self.assertEqual(tuple(sorted(values)),result['indices'])
                    self.assertLessEqual(result['stride']*(length-1),3)

    def test_shortness_cannot_be_dropped(self):
        values=(0,3,1)
        self.assertEqual({(values[j+1]-values[j]) % 5 for j in range(2)},{3})
        self.assertGreater(min(3,5-3)*(len(values)-1),4-1)
        with self.assertRaises(ValueError):e.rectify_short_carrier(5,4,values)

    def test_balanced_partition_bounds_disjointness_and_sharpness(self):
        for cap in range(2,17):
            for length in range(cap-1,65):
                blocks=e.balanced_chain_blocks(length,cap)
                self.assertEqual([x for b in blocks for x in b],list(range(length)))
                self.assertGreaterEqual(min(map(len,blocks)),(cap+1)//2)
                self.assertLessEqual(max(map(len,blocks)),cap)
            blocks=e.balanced_chain_blocks(cap+1,cap)
            self.assertEqual(min(map(len,blocks)),(cap+1)//2)
        blocks=e.aligned_parent_partition(13,3,5)
        self.assertEqual(set(x for b in blocks for x in b),set(range(13)))
        self.assertEqual(sum(map(len,blocks)),13)
        self.assertTrue(all(3<=len(b)<=5 for b in blocks))

    def test_weighted_density_retention_for_all_small_indicator_weights(self):
        for total,stride,length in ((5,1,3),(7,2,3),(8,3,3)):
            blocks=e.aligned_parent_partition(total,stride,length)
            for mask in range(1<<total):
                weights=tuple(int(bool(mask & (1<<i))) for i in range(total))
                selected=e.weighted_parent_choice(weights,blocks)
                block=blocks[selected]
                self.assertGreaterEqual(sum(weights[x] for x in block)*total,sum(weights)*len(block))

    def test_side_m_minus_one_and_ceiling_square(self):
        for length in range(3,65):
            self.assertGreaterEqual(((length+1)//2)**2,length)
            for m in range(2,length+1):
                for stride in range(1,(length-1)//(m-1)+1):
                    self.assertLessEqual(stride*(m-1),length-1)
                    blocks=e.residue_cover(length,stride,m-1)
                    self.assertLess(len(blocks)*(m-1),2*length)

    def test_phase_uses_original_translated_coordinates(self):
        p,start,step,offset=7,6,3,5
        a0,a1,b0,b1=2,3,4,5
        c0,cx,cz,cxz=e.ambient_phase_coefficients(p,start,step,offset,a0,a1,b0,b1)
        for j in range(4):
            for x in range(p):
                z=(start+j*step+offset) % p
                self.assertEqual((a0+j*a1+(b0+j*b1)*x) % p,(c0+cx*x+cz*z+cxz*x*z) % p)
        reversed_coefficients=e.ambient_phase_coefficients(p,(start+3*step)%p,(-step)%p,offset,
            (a0+3*a1)%p,(-a1)%p,(b0+3*b1)%p,(-b1)%p)
        self.assertEqual((c0,cx,cz,cxz),reversed_coefficients)

    def test_constructive_caps_and_invalid_partitions(self):
        for args in ((47,2,(0,1)),(7,5,(0,1)),(7,4,(0,0)),(7,4,(0,1,3)),(7,4,(0,True))):
            with self.subTest(args=args),self.assertRaises(ValueError):e.rectify_short_carrier(*args)
        for args in ((129,2),(1,3),(4,True),(5,65)):
            with self.subTest(args=args),self.assertRaises(ValueError):e.balanced_chain_blocks(*args)
        for args in ((65,1,2),(7,2,5),(7,0,3),(7,1,1)):
            with self.subTest(args=args),self.assertRaises(ValueError):e.aligned_parent_partition(*args)
        for weights,blocks in (((1,2),((0,),(0,))),((1,True),((0,1),)),((129,0),((0,1),))):
            with self.subTest(weights=weights,blocks=blocks),self.assertRaises(ValueError):e.weighted_parent_choice(weights,blocks)
        for args in ((7,0,0,0,0,0,0,0),(47,0,1,0,0,0,0,0),(7,0,1,True,0,0,0,0)):
            with self.subTest(args=args),self.assertRaises(ValueError):e.ambient_phase_coefficients(*args)

    def test_constructive_fixed_profile_counts(self):
        result=e.constructive_diagnostics()
        expected=dict(short_progression_prefixes=31670,aligned_parent_partitions=7824,
            weighted_density_retention_cases=23472,final_side_m_minus_one_covers=1605,
            original_coordinate_phase_cases=336,selected_cell_shortness_cases=124)
        self.assertEqual({key:result[key] for key in expected},expected)


class SourceTests(unittest.TestCase):
    def fixture(self):
        raw=b'precise\r\nsource\n'
        git=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        path='Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean'
        commit='a'*40
        row=dict(file='sources/Definitions.lean',repository_path=path,commit=commit,
                 bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),git_blob=git,
                 verified_url='https://github.com/VladimirReshetnikov/ProveIt/blob/'+commit+'/'+path)
        return raw,row

    def test_exact_byte_validation_and_line_endings(self):
        raw,row=self.fixture(); self.assertEqual(e.verify_source_bytes(raw,row),row['git_blob'])
        with self.assertRaises(RuntimeError): e.verify_source_bytes(raw.replace(b'\r\n',b'\n'),row)

    def test_corrupt_hashes_urls_and_unbounded_records_fail(self):
        raw,original=self.fixture()
        for change in ({'sha256':'0'*64},{'git_blob':'0'*40},{'bytes':len(raw)+1},
                       {'bytes':True},{'file':'../Definitions.lean'},
                       {'commit':'main'},{'verified_url':'https://example.com/file'},
                       {'repository_path':'somewhere/Definitions.lean'},{'extra':'unrequested'}):
            row=dict(original);row.update(change)
            with self.subTest(change=change),self.assertRaises((ValueError,RuntimeError)):
                e.verify_source_bytes(raw,row)

    def test_manifest_exact_inventory_and_duplicate_guards(self):
        raw,row=self.fixture()
        manifest=dict(schema='report279-curated-sources-v1',scope='test fixture',
                      sources=[row],unchanged_at_later_pins=[])
        files={'provenance/sources/Definitions.lean':raw}
        self.assertEqual(e.validate_source_manifest(manifest,files),(1,0))
        for mode in ('duplicate','missing','extra','later-missing','extra-key'):
            copy=json.loads(json.dumps(manifest));data=files.copy()
            if mode=='duplicate':copy['sources'].append(row)
            elif mode=='missing':data.clear()
            elif mode=='extra':data['provenance/sources/Extra.lean']=raw
            elif mode=='later-missing':copy['unchanged_at_later_pins']=[dict(row,file='sources/Extra.lean')]
            else:copy['unknown']='value'
            with self.subTest(mode=mode),self.assertRaises((ValueError,RuntimeError)):
                e.validate_source_manifest(copy,data)

    def test_frozen_source_inventory(self):
        result=e.source_diagnostics()
        self.assertEqual(result['verified_lean_snapshots'],18)
        self.assertEqual(result['unchanged_later_pin_checks'],6)
        self.assertEqual(result['provenance_files'],19)
        self.assertEqual(len(result['pins']),6)


class CommandTests(unittest.TestCase):
    def test_unknown_cli_option_is_rejected(self):
        result=subprocess.run([sys.executable,'-I','-B',str(COMPANION),'--modulus','999999999'],
                              capture_output=True,timeout=10)
        self.assertEqual(result.returncode,2)
        self.assertIn(b'unrecognized arguments',result.stderr)
        self.assertEqual(result.stdout,b'')


if __name__ == '__main__':
    unittest.main()
