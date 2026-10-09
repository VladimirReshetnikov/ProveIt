"""Explicit algebraic screening family; not asserted to be triangulable.

The model is a homogeneous integer cone arranged in seven-coordinate blocks.
There are r irrelevant prefix blocks, r mandatory blocks, and ceil(r/4)
auxiliary blocks.  If z is the first mandatory type-0 coordinate, the equations
are q[j,0]=z and q[j,1]+p[j]=z.  Auxiliary p coordinates are triangles ordered
after every mandatory quad.  The objective is z.

The model-building and geometric-analysis boundaries are replaced explicitly
only in this synthetic research harness.  Actual triangulation tests use the
unmodified model builder and independent certificate verifier.
"""

from contextlib import ExitStack
from unittest.mock import patch

from fastunknot.normal_propagation import search_positive_euler as baseline
from fastunknot.normal_propagation_cached import search_positive_euler as screened


def model(size):
    if type(size) is not int or size < 1:
        raise ValueError('a positive integer size is required')
    tetrahedra = 2*size + (size+3)//4
    width = 7*tetrahedra
    origin = 7*size+4
    objective = [int(j == origin) for j in range(width)]
    equations = []
    for j in range(size):
        if j:
            row = [0]*width
            row[7*(size+j)+4] = 1
            row[origin] = -1
            equations.append(row)
        row = [0]*width
        row[7*(size+j)+5] = 1
        row[7*(2*size+j//4)+j % 4] = 1
        row[origin] = -1
        equations.append(row)
    return dict(prepared=None, matrix=equations, euler=objective,
                anchor_groups=[], tetrahedra=tetrahedra,
                vertices=0, variables=width)


def run(size, *, cached, check=lambda: None, capacity=256):
    source = model(size)
    module = 'fastunknot.normal_propagation' + ('_cached' if cached else '')

    def analyse(prepared, rows, cb):
        cb()
        flat = [value for row in rows for value in row]
        return dict(euler_characteristic=sum(x*c for x, c in zip(flat, source['euler'])))

    with ExitStack() as stack:
        stack.enter_context(patch(module+'.build_standard_model', return_value=source))
        stack.enter_context(patch(module+'._coordinates', side_effect=analyse))
        options = dict(max_branch_depth=0, max_pivots=None, check=check)
        if cached:
            options['max_cached_witnesses'] = capacity
        return (screened if cached else baseline)({'algebraic_family': size}, **options)
