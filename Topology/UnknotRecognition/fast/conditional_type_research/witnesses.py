"""Independent original STANDARD replay; no kernel or solver imports."""
from copy import deepcopy
from fractions import Fraction
from math import gcd
from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_surface_geometry import _prepare
from .common import digest


def integer(value):
    assert type(value) is int
    return value


def rational(value):
    assert type(value) is list and len(value) == 2
    num, den = map(integer, value)
    assert den > 0 and gcd(abs(num), den) == 1
    return Fraction(num, den)


def mask(value, n):
    assert type(value) is list
    result = []
    for pair in value:
        assert type(pair) is list and len(pair) == 2
        t, q = map(integer, pair)
        assert 0 <= t < n and 0 <= q < 3
        result.append((t, q))
    assert result == sorted(result) and len(result) == len(set(result))
    return result


def pair(value, n):
    assert type(value) is list and len(value) == 2
    t, q = map(integer, value)
    assert 0 <= t < n and 0 <= q < 3
    return t, q


def kernel_diagnostics(stats, n, width):
    expected = {'tetrahedra', 'allowed_types', 'active_equations', 'triangle_classes',
                'kernel_variables', 'kernel_equations', 'matching_nullity', 'matching_rank',
                'removed_link_factors'}
    assert type(stats) is dict and set(stats) == expected
    assert all(type(v) is int and v >= 0 for v in stats.values())
    assert stats['tetrahedra'] == n and stats['allowed_types'] == width
    assert stats['matching_nullity']+stats['matching_rank'] == width
    assert stats['kernel_variables'] == stats['triangle_classes']+width
    assert stats['triangle_classes'] <= 4*n
    assert stats['kernel_equations'] <= stats['active_equations'] <= 4*width
    assert stats['removed_link_factors'] <= 1


def verify_witness(prepared, tested, query):
    """Check actual matching feasibility, not Euler sign or compatibility elsewhere."""
    n = len(prepared['tetrahedra'])
    conditional = [(t, q) for t in range(n) for q in range(3) if t != tested[0] or q == tested[1]]
    assert mask(query['conditional_mask'], n) == conditional
    assert pair(query['tested_type'], n) == tested and query['status'] == 'MATCHING_WITNESS'
    rows = query['coordinates']
    assert type(rows) is list and len(rows) == n
    assert all(type(row) is list and len(row) == 7 for row in rows)
    flat = [value for row in rows for value in row]
    assert all(type(value) is int and value >= 0 for value in flat)
    assert rows[tested[0]][4+tested[1]] > 0
    assert all(rows[tested[0]][4+q] == 0 for q in range(3) if q != tested[1])
    assert all(sum(coefficient*flat[column] for column, coefficient in equation.items()) == 0
               for equation in prepared['matching'])
    assert gcd(*flat) == 1
    diagnostic = query['construction']
    assert type(diagnostic) is dict and set(diagnostic) == {'basis_index', 'original_target',
        'block_shifts', 'triangle_link_shifts', 'denominator', 'primitive_divisor'}
    assert 0 <= integer(diagnostic['basis_index']) < query['kernel_statistics']['matching_nullity']
    assert rational(diagnostic['original_target']) != 0
    denominator, divisor = integer(diagnostic['denominator']), integer(diagnostic['primitive_divisor'])
    assert denominator > 0 and divisor > 0
    assert rows[tested[0]][4+tested[1]]*divisor == denominator
    assert type(diagnostic['block_shifts']) is list
    previous = -1
    for entry in diagnostic['block_shifts']:
        assert type(entry) is list and len(entry) == 2
        tet = integer(entry[0])
        assert previous < tet < n and tet != tested[0] and rational(entry[1]) > 0
        previous = tet
    links = diagnostic['triangle_link_shifts']
    assert type(links) is list and len(links) == prepared['vertices']
    assert [integer(entry[0]) for entry in links] == sorted(set(prepared['vertex_roots']))
    for entry in links:
        assert type(entry) is list and len(entry) == 2
        rational(entry[1])
    return True


def replay_record(record, old, cap):
    source = old['preprocessing']['u1']['result']['partial_chain']['triangulation']
    assert digest(record['source']) == record['source_sha256'] == digest(source)
    assert record['id'] == old['id'] and digest(record['input_pd']) == digest(old['input_pd'])
    assert verify_crushing_chain(Diagram.from_pd(old['input_pd']), old['preprocessing']['u1']['result']['partial_chain'])
    prepared = _prepare(source, lambda: None)
    n = len(prepared['tetrahedra'])
    assert prepared['vertices'] == 1 and len(prepared['boundary_faces']) == 2
    full = [(t, q) for t in range(n) for q in range(3)]
    assert mask(record['full_initial_mask'], n) == full
    assert 0 <= integer(record['checks_used']) <= cap
    assert type(record['queries']) is list and len(record['queries']) <= len(full)
    prep = record['preparation']
    assert type(prep) is dict
    used = integer(prep['checks_used'])
    assert 0 <= used <= record['checks_used']
    capped = prep['status'] == 'CAPPED'
    if capped:
        assert set(prep) == {'status', 'checks_used'} and used == cap and not record['queries']
    else:
        assert set(prep) == {'status', 'checks_used', 'vertices'}
        assert prep['status'] == 'RETURNED' and integer(prep['vertices']) == 1
    witnesses = zeros = 0
    first = None
    for index, query in enumerate(record['queries']):
        assert not capped and type(query) is dict and integer(query['index']) == index
        tested = pair(query['tested_type'], n)
        assert tested == full[index]
        conditional = [a for a in full if a[0] != tested[0] or a == tested]
        assert mask(query['conditional_mask'], n) == conditional
        assert integer(query['start_checks']) == used
        used = integer(query['end_checks'])
        assert query['start_checks'] <= used <= cap
        common = {'index', 'tested_type', 'conditional_mask', 'start_checks', 'end_checks', 'status'}
        if 'kernel_statistics' in query:
            kernel_diagnostics(query['kernel_statistics'], n, len(conditional))
        if query['status'] == 'CAPPED':
            assert set(query) in (common | {'reason'}, common | {'reason', 'kernel_statistics'})
            assert type(query['reason']) is str and query['reason']
            assert used == cap and index == len(record['queries'])-1
            capped = True
        elif query['status'] == 'ZERO_LINEAR_TARGET':
            assert set(query) == common | {'scope', 'kernel_statistics'}
            assert query['scope'] == 'Producer linear diagnostic only; no independently certified infeasibility or deletion.'
            zeros += 1
        else:
            assert set(query) == common | {'kernel_statistics', 'coordinates', 'construction'}
            assert verify_witness(prepared, tested, query)
            witnesses += 1
            if first is None:
                first = prepared, tested, query
    assert record['checks_used'] == used
    if capped:
        assert record['status'] == 'CAPPED'
    else:
        assert record['status'] == 'COMPLETE_INITIAL_MASK_SCAN' and len(record['queries']) == len(full)
    complete = not capped and witnesses == len(full)
    assert type(record['all_types_have_matching_witnesses']) is bool and record['all_types_have_matching_witnesses'] == complete
    return dict(id=record['id'], source_sha256=digest(source), tetrahedra=n,
        expected_types=len(full), attempted_queries=len(record['queries']), verified_matching_witnesses=witnesses,
        uncertified_zero_diagnostics=zeros, status=record['status'], checks_used=used,
        all_initial_conditional_types_feasible=complete), first


def corruption_controls(control):
    if control is None:
        return []
    prepared, tested, query = control
    def zero_target(value):
        value['coordinates'][tested[0]][4+tested[1]] = 0
    def competing(value):
        value['coordinates'][tested[0]][4+(tested[1]+1) % 3] = 1
    def bool_entry(value):
        value['coordinates'][0][0] = bool(value['coordinates'][0][0])
    def wrong_type(value):
        value['tested_type'][1] = (tested[1]+1) % 3
    column = next(column for equation in prepared['matching'] for column, value in equation.items()
                  if column % 7 < 4 and value)
    def matching_residue(value):
        value['coordinates'][column//7][column%7] += 1
    mutations = [
        ('nonzero original matching residue', matching_residue),
        ('bool tested type', lambda x: x['tested_type'].__setitem__(1, bool(x['tested_type'][1]))),
        ('zero target', zero_target), ('competing target quadrilateral', competing),
        ('bool coordinate', bool_entry), ('wrong tested type', wrong_type),
        ('negative triangle', lambda x: x['coordinates'][0].__setitem__(0, -1)),
        ('float coordinate', lambda x: x['coordinates'][0].__setitem__(0, float(x['coordinates'][0][0]))),
        ('missing coordinate row', lambda x: x['coordinates'].pop()),
        ('missing conditional type', lambda x: x['conditional_mask'].pop()),
        ('duplicate conditional type', lambda x: x['conditional_mask'].append(x['conditional_mask'][-1])),
        ('false denominator diagnostic', lambda x: x['construction'].update(denominator=0)),
    ]
    records = []
    for name, change in mutations:
        altered = deepcopy(query)
        change(altered)
        try:
            verify_witness(prepared, tested, altered)
        except (AssertionError, KeyError, ValueError, TypeError, IndexError):
            rejected = True
        else:
            rejected = False
        assert rejected, name
        records.append(dict(name=name, rejected=True))
    return records


