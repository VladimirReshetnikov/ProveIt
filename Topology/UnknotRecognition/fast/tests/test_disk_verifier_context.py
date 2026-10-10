"""Verifier-owned batch geometry preserves actual-source proof acceptance."""
from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot.normal_disk_kernel import _DiskCertificateVerifier,normal_compressing_disk_count,verify_normal_disk_count_certificate
from fastunknot import normal_disk_kernel as disk
from fastunknot import normal_component_geometry as geometry
from fastunknot.normal_sector import sector_rays
from fastunknot.sector_sparse import PreparedSectorSource
from planar_sector_research.fixtures import double_capped_fibonacci


class DiskVerifierContextTests(unittest.TestCase):
    def fixture(self):
        f=double_capped_fibonacci(2);raw=f['triangulation'];source=PreparedSectorSource(raw)
        rows=list(sector_rays(source.build(f['allowed_types'])))
        proofs=[normal_compressing_disk_count(raw,r,max_cycles=0,record_certificate=True)['certificate']for r in rows]
        return raw,source,rows,proofs

    def test_batch_builds_its_own_source_and_homology_once_with_producers_disabled(self):
        raw,producer,rows,proofs=self.fixture()
        prepare=disk._prepare;basis=geometry.boundary_homology_basis
        with patch.object(disk,'_prepare',side_effect=prepare)as prepares,\
             patch.object(geometry,'boundary_homology_basis',side_effect=basis)as bases:
            verifier=_DiskCertificateVerifier(raw)
            self.assertIsNot(verifier._prepared,producer.prepared)
            self.assertIsNot(verifier._source,raw)
            with patch.object(disk,'canonical_disk_core',side_effect=AssertionError('producer called')),\
                 patch.object(disk,'normal_compressing_disk_count',side_effect=AssertionError('producer called')),\
                 patch.object(disk,'_count_prepared_discs',side_effect=AssertionError('producer called')):
                for r,p in zip(rows,proofs):self.assertTrue(verifier.verify(raw,r,p))
        self.assertEqual(prepares.call_count,1);self.assertEqual(bases.call_count,1)
        self.assertEqual(len(rows),7)

    def test_acceptance_matches_fresh_public_replay_for_tampering_and_scaled_sources(self):
        raw,_,rows,proofs=self.fixture();verifier=_DiskCertificateVerifier(raw)
        for r,p in zip(rows,proofs):
            bad=[]
            for key in ('coordinate_divisor','compressing_disk_components'):
                q=deepcopy(p);q[key]+=1;bad.append((r,q))
            q=deepcopy(p);q['core_coordinates'][0][0]+=1;bad.append((r,q))
            q=deepcopy(p);q['vertex_links'][0]['multiplicity']+=1;bad.append((r,q))
            q=deepcopy(p);q['input_sha256']='bad';bad.append((r,q))
            q=deepcopy(p);q['core_certificate']['euler_characteristic']+=1;bad.append((r,q))
            q=deepcopy(p);q['core_certificate']['boundary_homology_mod2'][0]^=1;bad.append((r,q))
            q=deepcopy(r);q[0][0]+=1;bad.append((q,p))
            for coordinates,proof in bad:
                self.assertFalse(verify_normal_disk_count_certificate(raw,coordinates,proof))
                self.assertFalse(verifier.verify(raw,coordinates,proof))
            scale=2**90+1;scaled=[[scale*x for x in row]for row in r]
            proof=normal_compressing_disk_count(raw,scaled,max_cycles=0,record_certificate=True)['certificate']
            self.assertTrue(verify_normal_disk_count_certificate(raw,scaled,proof))
            self.assertTrue(verifier.verify(raw,scaled,proof))

    def test_source_changes_and_equal_boolean_aliases_never_bind_to_the_snapshot(self):
        raw,_,rows,proofs=self.fixture();verifier=_DiskCertificateVerifier(raw)
        changed=deepcopy(raw)
        found=False
        for faces in changed['tetrahedra']:
            for face in faces:
                if face is not None and face['tetrahedron']in(0,1):
                    face['tetrahedron']=bool(face['tetrahedron']);found=True;break
            if found:break
        self.assertTrue(found);self.assertEqual(changed,raw)
        self.assertFalse(verify_normal_disk_count_certificate(changed,rows[0],proofs[0]))
        self.assertFalse(verifier.verify(changed,rows[0],proofs[0]))
        raw['tetrahedra'][0][0]=None
        self.assertFalse(verifier.verify(raw,rows[0],proofs[0]))
        self.assertTrue(verifier.verify(verifier._source,rows[0],proofs[0]))

    def test_interrupted_homology_construction_never_leaves_a_partial_cache(self):
        raw,_,rows,proofs=self.fixture();verifier=_DiskCertificateVerifier(raw)
        class Interrupted(RuntimeError):
            def __bool__(self):return False
        with patch.object(geometry,'boundary_homology_basis',side_effect=Interrupted):
            with self.assertRaises(Interrupted):verifier.verify(raw,rows[0],proofs[0])
        self.assertIsNone(verifier._basis)
        self.assertTrue(verifier.verify(raw,rows[0],proofs[0]))


if __name__=='__main__':unittest.main()
