#!/usr/bin/env python3
"""Independent floating-point check from the two original circles.

Requires NumPy and SciPy. No ruled chart or symbolic elliptic reduction is used.
The convex hull of the sampled circle points has triangular facets. The origin
is interior, so coning those facets to the origin partitions the polytope.
"""
import numpy as np
from scipy.spatial import ConvexHull
from scipy.special import ellipe, ellipk


def polytope_quantities(n):
    angle = np.arange(n) * (2 * np.pi / n)
    s, c = np.sin(angle), np.cos(angle)
    zeros = np.zeros_like(s)
    points = np.vstack((
        np.column_stack((c - 0.5, s, zeros)),
        np.column_stack((c + 0.5, zeros, s)),
    ))
    hull = ConvexHull(points)
    faces = points[hull.simplices]
    a, b, c = (faces[:, j, :] for j in range(3))
    area = np.linalg.norm(np.cross(b-a, c-a), axis=1).sum() / 2
    volumes = np.abs(np.einsum('ij,ij->i', a, np.cross(b, c))) / 6
    sums = faces.sum(axis=1)
    first = volumes @ sums / 4
    # On a uniform tetrahedron E[lambda_i lambda_j]=(1+delta_ij)/20.
    second = (np.einsum('f,fki,fkj->ij', volumes, faces, faces)
              + np.einsum('f,fi,fj->ij', volumes, sums, sums)) / 20
    tensor = np.trace(second) * np.eye(3) - second
    return area, volumes.sum(), first / volumes.sum(), tensor


def main():
    K, E = ellipk(0.75), ellipe(0.75)
    exact = np.array([4*np.pi, (2*K+4*E)/3, (32*E-2*K)/45, (142*E-19*K)/90])
    print("Samples per circle and signed errors (polytope minus analytic value)")
    print("   n          area         volume        I_xx           I_yy        diagonal check*")
    for n in (48, 96, 192, 384, 768):
        area, volume, center, tensor = polytope_quantities(n)
        errs = np.array([area, volume, tensor[0,0], tensor[1,1]]) - exact
        diag = np.diag(np.diag(tensor))
        symmetry_error = max(np.max(np.abs(center)), np.max(np.abs(tensor-diag)),
                             abs(tensor[1,1]-tensor[2,2]))
        print(f"{n:4d} " + " ".join(f"{err: .6e}" for err in errs) +
              f"   {symmetry_error:.2e}")
    print("*Max absolute residual of center coordinates, off-diagonals and I_yy-I_zz.")


if __name__ == "__main__":
    main()
