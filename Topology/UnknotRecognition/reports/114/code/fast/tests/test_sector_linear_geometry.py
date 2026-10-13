"""Sparse window geometry against complete source rays and generic rank paths."""
import unittest
from unittest.mock import patch

from fastunknot.normal_sector import sector_rays
from fastunknot.normal_surface_geometry import _coordinates
from fastunknot.sector_residual import _full_quad_columns
from fastunknot.sector_sparse import PreparedSectorSource
from fastunknot.sector_linear_form import SparseLinearForm
from fastunknot.sector_window_basis import projected_window_kernel
from planar_sector_research.fixtures import double_capped_fibonacci,vector_key


class SparseWindowGeometryTests(unittest.TestCase):
    def test_low_dimensional_source_rays_never_materialize_dense_linear_forms(self):
        fixture=double_capped_fibonacci(3);raw=fixture['triangulation'];source=PreparedSectorSource(raw)
        _,_,potentials=_full_quad_columns(source.prepared,lambda:None,True)
        dims=[]
        for allowed in (fixture['allowed_types'][-1:],fixture['allowed_types'][-2:],fixture['allowed_types']):
            fresh=source.build(allowed);dims.append(len(fresh.basis))
            expected=list(sector_rays(fresh))
            updated=projected_window_kernel(raw,source.prepared,allowed,fresh.basis,potentials,lambda:None)
            with patch.object(SparseLinearForm,'__iter__',side_effect=AssertionError('dense form requested by low-dimensional path')):
                actual=list(sector_rays(updated))
                for rows in actual:
                    q=[rows[t][4+kind]for t,kind in updated.support]
                    self.assertEqual(updated.lift(q),rows)
                    self.assertTrue(updated.is_standard_ray(rows))
            self.assertEqual({vector_key(r)for r in actual},{vector_key(r)for r in expected})
        self.assertEqual(dims,[1,2,3])

    def test_generic_methods_densify_the_same_complete_source_geometry(self):
        fixture=double_capped_fibonacci(1);raw=fixture['triangulation']
        raw['tetrahedra'][1][0]={'tetrahedron':3,'permutation':[0,1,2,3]}
        raw['tetrahedra'].append([{'tetrahedron':1,'permutation':[0,1,2,3]},None,None,None])
        source=PreparedSectorSource(raw);allowed=fixture['allowed_types']+[(3,0)]
        fresh=source.build(allowed);self.assertEqual(len(fresh.basis),4)
        _,_,potentials=_full_quad_columns(source.prepared,lambda:None,True)
        updated=projected_window_kernel(raw,source.prepared,allowed,fresh.basis,potentials,lambda:None)
        self.assertTrue(all(len(row)==len(updated.classes)+len(allowed)for row in updated.matrix))
        for method in ('arrangement','supports'):
            self.assertEqual({vector_key(r)for r in sector_rays(updated,method=method)},
                             {vector_key(r)for r in sector_rays(fresh,method=method)})

    def test_large_genuine_sector_keeps_linear_storage_and_validates_huge_lifts(self):
        fixture=double_capped_fibonacci(16);raw=fixture['triangulation'];source=PreparedSectorSource(raw)
        fresh=source.build(fixture['allowed_types'])
        _,_,potentials=_full_quad_columns(source.prepared,lambda:None,True)
        updated=projected_window_kernel(raw,source.prepared,fresh.support,fresh.basis,potentials,lambda:None)
        d=len(updated.basis);k=len(updated.support);p=len(updated.classes)
        self.assertEqual(d,3)
        self.assertLessEqual(updated.stats['stored_matrix_coefficients'],(k-d)*(d+1)+(p-len(updated.groups))*(d+2))
        self.assertLessEqual(updated.stats['stored_potential_coefficients'],p*d)
        rays=list(sector_rays(updated));self.assertEqual(len(rays),7)
        for rows in rays:
            q=[rows[t][4+kind]for t,kind in updated.support]
            scale=2**90+1
            lifted=updated.lift([scale*x for x in q])
            self.assertEqual(lifted,[[scale*x for x in row]for row in rows])
            self.assertEqual(_coordinates(source.prepared,lifted,lambda:None)['normal_disks'],
                             scale*sum(x for row in rows for x in row))


if __name__=='__main__':unittest.main()
