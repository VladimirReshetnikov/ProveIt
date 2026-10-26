#!/usr/bin/env python3
"""No Lean execution: source integrity, exact patch replay, bounded algebraic models."""
from pathlib import Path
import hashlib, json, re, shutil, subprocess, tempfile, unittest
ROOT=Path(__file__).resolve().parents[2]
HERE=ROOT/'helical'
REL=Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency')
SRC=ROOT/'sources'/REL
PROPOSED=HERE/'proposed'
FILES=['WangTiles942HelicalQuotient.lean','WangTiles942CycleBand.lean','WangTiles942BandMarker.lean']

def original(f): return (SRC/f).read_text()
def proposed(f): return (PROPOSED/f).read_text()
def signature(s,n):
    p=s.index('theorem '+n+' ')
    return s[p:s.index(':= by',p)]
def gitblob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()

class CandidateTests(unittest.TestCase):
    def test_pinned_sources_match_manifest(self):
        m={i['path']:i for i in json.loads((ROOT/'provenance/source_manifest.json').read_text())['sources']}
        for f in FILES:
            b=(SRC/f).read_bytes(); r=m[str(REL/f)]
            self.assertEqual(hashlib.sha256(b).hexdigest(),r['sha256'])
            self.assertEqual(gitblob(b),r['sha'])
            self.assertTrue(r['verified'])
    def test_new_files_in_active_delta(self):
        d=json.loads((ROOT/'provenance/active_tree_delta.json').read_text())
        self.assertEqual(d['head'],'e652d21c413de59e4821f6e8e9b6a3a077bf5bfe')
        files={i['path']:i for i in d['files']}
        for f in FILES: self.assertEqual(files['DiophantineConsistency/'+f]['status'],'added')
    def test_mathlib_blob_identity_and_api(self):
        p=HERE/'dependencies/Periodic.lean'
        m=json.loads((HERE/'dependencies/Periodic.source.json').read_text())
        self.assertEqual(gitblob(p.read_bytes()),m['sha'])
        self.assertIn('protected theorem Periodic.zsmul [AddGroup α]',p.read_text())
        self.assertEqual(m['ref'],'81a5d257c8e410db227a6665ed08f64fea08e997')
    def test_replay_combined_patches(self):
        with tempfile.TemporaryDirectory(prefix='helical-review-') as td:
            dest=Path(td)/REL; dest.mkdir(parents=True)
            for f in FILES: shutil.copy2(SRC/f,dest/f)
            patches=[str(HERE/'patches'/f) for f in ['H1.patch','H2.patch']]
            subprocess.run(['git','apply','--check',*patches],cwd=td,check=True,capture_output=True)
            subprocess.run(['git','apply',*patches],cwd=td,check=True,capture_output=True)
            for f in FILES: self.assertEqual((dest/f).read_bytes(),(PROPOSED/f).read_bytes())
    def test_signatures_definitions_imports_preserved(self):
        for f,n in [(FILES[0],'row_zero_of_helix'),(FILES[1],'marked_word_of_halt'),(FILES[2],'canonicalWord_properties')]:
            self.assertEqual(signature(original(f),n),signature(proposed(f),n))
            self.assertEqual(re.findall(r'^import .*$',original(f),re.M),re.findall(r'^import .*$',proposed(f),re.M))
        f=FILES[2]
        a=original(f).index('noncomputable def canonicalWord')
        b=original(f).index('/-- The literal index zero',a)
        self.assertIn(original(f)[a:b],proposed(f))
    def test_no_unsafe_proof_placeholders_or_added_guards(self):
        for f in FILES:
            self.assertNotRegex(proposed(f),r'\b(sorry|admit|axiom|unsafe|native_decide)\b')
        h=proposed(FILES[1]); h=h[h.index('theorem band_quotient_properties'):h.index('/-- A halting actual blank run')]
        self.assertNotRegex(h,r'\b(Coprime|uniqueStart|Unique|IsLeast)\b')
        self.assertIn('∀ x, -(L : ℤ) ≤ x → x < (R : ℤ) → ∀ t,',h)
    def test_duplicate_descent_removed_not_coordinate_api_rewritten(self):
        before='\n'.join(original(f) for f in FILES[1:]); after='\n'.join(proposed(f) for f in FILES[1:])
        self.assertEqual(before.count('rcases extension_properties'),2)
        self.assertEqual(after.count('rcases extension_properties'),1)
        self.assertEqual(before.count('apply extend_on_band'),2)
        self.assertEqual(after.count('apply extend_on_band'),1)
        self.assertEqual(after.count('theorem band_quotient_properties'),1)
    def test_signed_transport_model(self):
        for w in range(-7,8):
            for x in range(-12,13):
                for t in range(-12,13):
                    self.assertEqual((x+t*w,t+t*(-1)),(x+w*t,0))
                    def T(a,b): return ((a+w*b)%7,(a+w*b)**2%11)
                    self.assertEqual(T(x+w,t-1),T(x,t))
                    self.assertEqual(T(x,t),T(x+w*t,0))
        self.assertNotEqual(2+3*4,2-3*4) # wrong-sign transport detected
    def test_independent_dimensions_signed_binding_model(self):
        # Models tile values only, not actual-machine halt or edge matching proofs.
        cases=[(0,2,2,3),(0,2,7,3),(0,8,2,12),(3,5,9,7),(3,11,5,24)]
        for T,L,R,H in cases:
            self.assertTrue(T+2<=L and T+2<=R and T+2<=H and 3<=H)
            w=L+R; N=w*H
            def C(x,t): return (x,t%H)
            def ext(x,t): return C((x+L)%w-L,t+(x+L)//w)
            def word(z): return ext(-(z%N),0)
            for x in range(-L-2*w,R+2*w):
                for t in range(-2*H,2*H+1):
                    self.assertEqual(word(-x-w*t),ext(x,t))
                    if -L<=x<R: self.assertEqual(word(-x-w*t),C(x,t))
            # At the excluded right wall the representative is the next copy's left wall.
            self.assertEqual(ext(R,0),C(-L,1))
            self.assertNotEqual(ext(R,0),C(R,0))
    def test_literal_line_metrics(self):
        m=json.loads((HERE/'metrics.json').read_text())
        self.assertEqual(sum(i['delta_lines'] for i in m),-13)
        for i in m:
            self.assertEqual(i['original_lines'],len(original(i['file']).splitlines()))
            self.assertEqual(i['proposed_lines'],len(proposed(i['file']).splitlines()))

if __name__=='__main__': unittest.main(verbosity=2)
