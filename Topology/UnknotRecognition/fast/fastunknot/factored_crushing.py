"""Additive recognition by certified crushing of visible diagram factors.

The source driver remains the authority for defaults. This wrapper shares every
charged cap across visible factors and retains every attempted child's result.
It does not infer a bound on the full-cone parameter of a connected-sum source.
"""
from inspect import signature

from .diagram import Diagram
from .interlace import visible_factors_interlacement
from .normal_crushing_search import recognize_by_crushing
from .euler_lp_budget import validate_lp_controls

# Bind once to the actual public source-driver signature. Tests require every
# supported option to be deliberately represented in side-effect-free validation.
_CHILD_SIGNATURE = signature(recognize_by_crushing)
CAP_STATS = {
    'max_sectors': ('sectors_attempted',),
    'max_bases': ('bases_attempted',),
    'max_crushes': ('crushing_steps', 'boundary_unlayerings'),
    'max_pivots': ('lp_pivots',),
    'max_anchors': ('anchors_tested',),
    'max_tree_nodes': ('nodes_attempted',),
    'max_hitting_subsets': ('hitting_subsets_tested',),
    'max_ellipsoid_iterations': ('lp_ellipsoid_iterations',),
    'max_feasibility_calls': ('lp_feasibility_calls',),
}
MAX_STATS = frozenset((
    'max_cached_sector_jobs', 'maximum_tableau_bits',
    'maximum_ellipsoid_precision', 'maximum_ellipsoid_dimension',
    'maximum_planned_ellipsoid_iterations', 'maximum_tree_depth',
    'maximum_transversal_size', 'maximum_conflict_size', 'peak_cached_conflicts',
))
POLICY_OPTIONS = frozenset((
    'sector_order', 'sector_quantum', 'sector_method', 'lp_strategy',
    'reduce_vertices', 'unlayer_boundary', 'tree_model',
    'transversal_candidate_policy', 'lp_policy', 'lp_fast_path_pivots',
))
FACTOR_STATS = frozenset(('factors_total', 'factors_attempted', 'factors_unknot',
                          'factors_knotted', 'factors_inconclusive'))


def _options(diagram, check, supplied):
    """Use authoritative defaults and validate everything before any work."""
    bound = _CHILD_SIGNATURE.bind(diagram, check=check, **supplied)
    bound.apply_defaults()
    options = {k: v for k, v in bound.arguments.items() if k not in ('diagram', 'check')}
    if set(options) != set(CAP_STATS) | POLICY_OPTIONS:
        raise ArithmeticError('raw crushing option contract changed; update factorwise validation')
    for name in CAP_STATS:
        value = options[name]
        if value is not None and (type(value) is not int or value < 0):
            raise ValueError(name+' must be a nonnegative integer or None')
    if options['sector_order'] not in ('diversified', 'canonical'):
        raise ValueError('sector_order must be diversified or canonical')
    quantum = options['sector_quantum']
    if quantum is not None and (type(quantum) is not int or quantum <= 0):
        raise ValueError('sector_quantum must be a positive integer or None')
    if options['sector_method'] not in ('corners', 'lp', 'tree', 'transversal'):
        raise ValueError('sector_method must be corners, lp, tree or transversal')
    if options['lp_strategy'] not in ('anchors', 'envelope'):
        raise ValueError('lp_strategy must be anchors or envelope')
    for name in ('reduce_vertices', 'unlayer_boundary'):
        if type(options[name]) is not bool:
            raise ValueError(name+' must be a boolean')
    if options['tree_model'] not in ('source', 'restricted'):
        raise ValueError('tree_model must be source or restricted')
    if options['sector_method'] == 'transversal' and options['tree_model'] != 'source':
        raise ValueError('transversal search requires tree_model=source')
    policy = options['transversal_candidate_policy']
    if type(policy) is not str or policy not in ('subsets', 'conflicts'):
        raise ValueError('transversal_candidate_policy must be subsets or conflicts')
    validate_lp_controls(options['lp_policy'], options['lp_fast_path_pivots'],
                         options['max_ellipsoid_iterations'], options['max_feasibility_calls'])
    return options


def _remaining(options, stats):
    local = dict(options)
    for cap, fields in CAP_STATS.items():
        used = sum(stats.get(field, 0) for field in fields)
        if options[cap] is not None:
            if used > options[cap]:
                raise ArithmeticError('child work exceeded shared '+cap)
            local[cap] = options[cap]-used
    return local


def _merge(stats, child):
    for name, value in child.items():
        if name in FACTOR_STATS or type(value) is not int or value < 0:
            raise ArithmeticError('invalid raw crushing statistics')
        if name.startswith(('maximum_', 'peak_', 'max_')) and name not in MAX_STATS:
            raise ArithmeticError('unknown raw crushing peak statistic')
        stats[name] = max(stats.get(name, 0), value) if name in MAX_STATS else stats.get(name, 0)+value


def recognize_factored_by_crushing(diagram, *, check=lambda: None, **crushing_options):
    """Run the bounded complete crushing recognizer on visible diagram factors.

    Options/defaults are those of recognize_by_crushing. Nine work allowances
    are shared across all attempted factors; max_crushes includes inverse
    boundary layers. All attempted child results remain in factor_results.
    A verified negative child proves KNOTTED; all factors must prove UNKNOT.
    INCONCLUSIVE contains partial results and no conclusive certificate. Caller
    check exceptions propagate without conversion to local limit exhaustion.
    Additive statistics, including initial/shelled tetrahedron counts, sum over
    attempted factors. Peak statistics take the maximum across factors.
    Existing direct-driver and high-level-router defaults are unchanged.
    """
    options = _options(diagram, check, crushing_options)
    check()
    source = Diagram.from_pd(diagram.pd)
    factors, factorization = visible_factors_interlacement(source, check=check)
    factor_pds = [[list(row) for row in factor.pd] for factor in factors]
    stats = dict(factors_total=len(factors), factors_attempted=0,
                 factors_unknot=0, factors_knotted=0, factors_inconclusive=0)
    for fields in CAP_STATS.values():
        for field in fields:
            stats[field] = 0
    factor_results = []
    positive_proofs = []

    def result(status, certificate=None):
        check()
        output = dict(status=status, stats=stats, factor_results=factor_results,
                      factorization=factorization, factor_pds=factor_pds)
        if certificate is not None:
            output['certificate'] = certificate
        else:
            output['reason'] = 'one or more visible factors remain inconclusive'
        return output

    def conclusive(status, proofs):
        from .factored_crushing_verify import verify_factored_crushing_recognition
        packet = dict(schema='diagram-factor-crushing-v1', status=status,
                      input_pd=[list(row) for row in source.pd],
                      factorization=factorization, factor_pds=factor_pds,
                      proofs=sorted(proofs, key=lambda p: p['factor_index']))
        if not verify_factored_crushing_recognition(source, packet, check=check):
            raise ArithmeticError('independent factorwise recognition replay failed')
        return result(status, packet)

    for index in sorted(range(len(factors)), key=lambda i: (factors[i].crossings, i)):
        check()
        local = _remaining(options, stats)
        child = recognize_by_crushing(factors[index], check=check, **local)
        if child['status'] not in ('UNKNOT', 'KNOTTED', 'INCONCLUSIVE'):
            raise ArithmeticError('unexpected child crushing outcome')
        _merge(stats, child['stats'])
        _remaining(options, stats)  # Every returned count must respect all caps.
        stats['factors_attempted'] += 1
        stats['factors_'+child['status'].lower()] += 1
        factor_results.append(dict(factor_index=index, result=child))
        if child['status'] == 'KNOTTED':
            return conclusive('KNOTTED', [dict(factor_index=index, certificate=child['certificate'])])
        if child['status'] == 'UNKNOT':
            positive_proofs.append(dict(factor_index=index, certificate=child['certificate']))
        # An inconclusive early factor does not rule out a later negative child,
        # including one decidable by uncapped polynomial preprocessing alone.
    if len(positive_proofs) == len(factors):
        return conclusive('UNKNOT', positive_proofs)
    return result('INCONCLUSIVE')
