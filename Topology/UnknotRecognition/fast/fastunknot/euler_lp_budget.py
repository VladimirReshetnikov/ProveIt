"""Shared fallback controls and accounting for exact Euler LP callers."""

FALLBACK_SUM_FIELDS = ('lp_fallbacks', 'lp_ellipsoid_iterations',
                       'lp_feasibility_calls', 'lp_support_descent_steps')
FALLBACK_MAX_FIELDS = ('maximum_ellipsoid_precision', 'maximum_ellipsoid_dimension',
                       'maximum_planned_ellipsoid_iterations')


def fallback_statistics():
    return dict.fromkeys(FALLBACK_SUM_FIELDS+FALLBACK_MAX_FIELDS, 0)


def validate_lp_controls(policy, fast_path_pivots, max_ellipsoid_iterations,
                         max_feasibility_calls):
    if type(policy) is not str or policy not in ('polynomial', 'bland'):
        raise ValueError('lp_policy must be polynomial or bland')
    for name, value in (('lp_fast_path_pivots', fast_path_pivots),
                        ('max_ellipsoid_iterations', max_ellipsoid_iterations),
                        ('max_feasibility_calls', max_feasibility_calls)):
        if value is not None and (type(value) is not int or value < 0):
            raise ValueError(name+' must be a nonnegative integer or None')
    if policy == 'bland' and fast_path_pivots is not None:
        raise ValueError('lp_fast_path_pivots requires polynomial policy')


def lp_options(statistics, *, policy, fast_path_pivots, max_pivots,
               max_ellipsoid_iterations, max_feasibility_calls):
    def remaining(cap, field):
        return None if cap is None else cap-statistics[field]
    options = dict(policy=policy, max_pivots=remaining(max_pivots, 'lp_pivots'))
    if policy == 'polynomial':
        options.update(fast_path_pivots=fast_path_pivots,
            max_ellipsoid_iterations=remaining(max_ellipsoid_iterations, 'lp_ellipsoid_iterations'),
            max_feasibility_calls=remaining(max_feasibility_calls, 'lp_feasibility_calls'))
    return options


def record_fallback(statistics, result):
    for target, source in zip(FALLBACK_SUM_FIELDS,
            ('fallback_used', 'ellipsoid_iterations', 'feasibility_calls', 'support_descent_steps')):
        statistics[target] += result.get(source, 0)
    for field in FALLBACK_MAX_FIELDS:
        statistics[field] = max(statistics[field], result.get(field, 0))


def merge_fallback(statistics, source):
    for field in FALLBACK_SUM_FIELDS:
        statistics[field] += source[field]
    for field in FALLBACK_MAX_FIELDS:
        statistics[field] = max(statistics[field], source[field])
