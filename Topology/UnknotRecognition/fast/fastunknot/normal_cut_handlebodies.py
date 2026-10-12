"""Source-certified handlebody census with disk-bundle annulus absorption.

This conservative terminal operator combines the complete source parallelity
decomposition, ordered core attachments, and geometric core cancellations.
It never infers a ball from homology or a sphere boundary alone.  Unsupported annular
attachments, closed bundle bases, or stalled core cancellations are unresolved.
"""

from collections import Counter

from .bundle_boundary_kernel import bundle_boundary_kernel
from .bundle_primitive_annuli import primitive_bundle_annuli
from .core_primitive_annuli import core_primitive_annuli
from .core_handlebody import core_handlebody_certificate, select_core_forest
from .core_three_handle_reduction import reduce_core_three_handles
from .disk_bundle_absorption import absorb_disk_bundles
from .normal_parallelity import normal_cut_parallelity
from .parallelity_boundary_words import normal_parallelity_boundary_words
from .parallelity_boundary_moments import _compile as _compile_moment_boundary


def _census(geometry, summary, skeleton, components, check, absorbed=frozenset(), primitive=None, core_annuli=None):
    primitive = {} if primitive is None else primitive
    core_annuli = {} if core_annuli is None else core_annuli
    core_deductions = Counter(core_annuli.values())
    profiles = summary['base_profiles']
    if any(p['boundary_components'] == 0 for p in profiles):
        return None, 'closed_bundle_base'
    owner = {v: c['id'] for c in components for v in c['zero_handles']}
    port_base = {p: i for i, profile in enumerate(profiles)
                 for p in profile['core_ports']}
    port_core = {}
    for port in geometry['ports']:
        check()
        dimension, handle = port['core_dimension'], port['core_handle']
        if dimension == 0:
            vertex = handle
        elif dimension == 1:
            vertex = geometry['core']['handles1'][handle]['ends'][0]
        else:
            raise ArithmeticError('invalid core-facing port owner')
        port_core[port['id']] = owner[vertex]
    nodes = [('core', c['id']) for c in components]
    nodes += [('base', i) for i, p in enumerate(profiles) if p['core_ports'] and i not in absorbed]
    parent = {v: v for v in nodes}
    genera = {('core', c['id']): c['genus'] - core_deductions[c['id']] for c in components}
    genera.update({('base', i): 1 - p['euler_characteristic'] - primitive.get(i, 0)
                   for i, p in enumerate(profiles) if p['core_ports'] and i not in absorbed})

    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    edges = []
    for i, attachment in enumerate(skeleton['attachment_components']):
        check()
        ports = [abs(p) - 1 for p in attachment['word']]
        if attachment['kind'] == 'circle' and port_base[ports[0]] in absorbed:
            continue
        bases = {port_base[p] for p in ports}
        cores = {port_core[p] for p in ports}
        permitted = (attachment['kind'] == 'interval' or
                     (attachment['kind'] == 'circle' and
                      (bases <= primitive.keys() or i in core_annuli)))
        if not permitted or len(bases) != 1 or len(cores) != 1:
            raise ArithmeticError('one connected disk attachment has inconsistent owners')
        b, c = next(iter(bases)), next(iter(cores))
        if i in core_annuli and core_annuli[i] != c:
            raise ArithmeticError('core annulus has inconsistent component owner')
        left, right = ('base', b), ('core', c)
        a, z = root(left), root(right)
        if a != z:
            parent[max(a, z)] = min(a, z)
        edges.append(dict(attachment=i, base_profile=b, core_component=c))
    groups = {}
    for v in nodes:
        groups.setdefault(root(v), []).append(v)
    histogram = Counter()
    joined = []
    for key, vertices in sorted(groups.items()):
        check()
        selected = [i for i, e in enumerate(edges)
                    if root(('base', e['base_profile'])) == key]
        cycle_rank = len(selected) - len(vertices) + 1
        genus = sum(genera[v] for v in vertices) + cycle_rank
        if genus < 0 or cycle_rank < 0:
            raise ArithmeticError('invalid disk-gluing graph genus')
        histogram[genus] += 1
        joined.append(dict(core_components=sorted(v[1] for v in vertices if v[0] == 'core'),
                           base_profiles=sorted(v[1] for v in vertices if v[0] == 'base'),
                           attachments=selected, cycle_rank=cycle_rank, genus=genus))
    isolated = []
    for i, profile in enumerate(profiles):
        check()
        if not profile['core_ports']:
            genus = 1 - profile['euler_characteristic']
            if genus < 0:
                raise ArithmeticError('a bordered bundle has negative handlebody genus')
            copies = profile['multiplicity']
            histogram[genus] += copies
            isolated.append(dict(base_profile=i, genus=genus, multiplicity=copies))
    euler = sum((1 - genus) * copies for genus, copies in histogram.items())
    expected = (summary['core_euler_characteristic'] +
                summary['bundle_euler_characteristic'] -
                summary['attachment_euler_characteristic'])
    if euler != expected:
        raise ArithmeticError('handlebody census violates source-cut Euler identity')
    return dict(histogram=[dict(genus=g, multiplicity=n) for g, n in sorted(histogram.items())],
                components=sum(histogram.values()), ball_components=histogram[0],
                all_balls=all(g == 0 for g in histogram), euler_characteristic=euler,
                joined_components=joined, isolated_bundles=isolated, attachments=edges), None


def _kernel_fallback(result, parallelity, boundary, record_certificate, check, *,
                     geometry=None, reduction=None, forest=None, defer_forest=False):
    geometry = parallelity['geometry'] if geometry is None else geometry
    kernel = bundle_boundary_kernel(geometry, parallelity['summary'],
                                    boundary['skeleton'], forest=forest, defer_forest=defer_forest, check=check)
    if kernel is None:
        return result
    proof, census, stats = kernel
    result.pop('reason', None)
    result.update(status='COMPLETE', census=census)
    result['stats']['boundary_kernel'] = stats
    if record_certificate:
        result['certificate'] = dict(schema='normal-cut-handlebodies-v5',
            parallelity=parallelity['certificate'], boundary=boundary['certificate'],
            kernel=proof, census=census)
        if reduction is not None:
            result['certificate'].update(schema='normal-cut-handlebodies-v6', core_reduction=reduction)
    return result


def _attempt_cut(parallelity, discover_boundary, record_certificate, precheck_core,
                 top_forest, forest, check, *, defer_forest=False):
    """One finite forest choice, sharing immutable source and boundary packets."""
    result = dict(status='INCONCLUSIVE', stats=dict(parallelity=parallelity['stats']),
                  trust='source cut handlebodies; no standalone knot verdict')
    geometry, reduction = parallelity['geometry'], None
    if geometry['core']['handles3']:
        reduced = reduce_core_three_handles(geometry, strategy=top_forest, lower_forest=forest, check=check)
        if reduced is None:
            result['reason'] = 'core_three_handle_reduction_stalled'
            return result
        geometry, reduction = reduced
        result['stats']['core_reduction'] = dict(cancelled_23=len(reduction['cancellations']),
                                               strategy=top_forest)
    prepared_core = None
    if precheck_core:
        prepared_core = core_handlebody_certificate(geometry['core'], forest=forest, defer_forest=defer_forest, check=check)
        result['stats']['core_precheck'] = prepared_core.get('stats', {})
        if prepared_core['status'] != 'COMPLETE':
            # Added bundle columns vanish on the original core rows. A source
            # stopping set therefore persists in every supported whole-cut
            # presentation with this forest. In deferred mode the full-matrix
            # obstruction holds for every lower forest on these retained rows.
            # This is only a method refusal.
            result['reason'] = prepared_core['reason']
            return result
    boundary = discover_boundary()
    result['stats']['boundary'] = boundary['stats']
    if boundary['status'] != 'COMPLETE':
        result['reason'] = 'boundary_budget_exhausted'
        return result
    if reduction is not None:
        result['reason'] = 'boundary_kernel_cancellation_stalled'
        return _kernel_fallback(result, parallelity, boundary, record_certificate, check,
                                geometry=geometry, reduction=reduction, forest=forest, defer_forest=defer_forest)
    family = primitive_bundle_annuli(parallelity['summary'], boundary['skeleton'], check=check)
    core_side = family is None
    if core_side:
        primitive_proof, primitive = None, {}
        deferred = {i for i, p in enumerate(parallelity['summary']['base_profiles'])
                    if (p['euler_characteristic'], p['boundary_components']) != (1, 1)}
    else:
        primitive_proof, primitive = family
        deferred = primitive
    absorption = absorb_disk_bundles(parallelity['geometry'], parallelity['summary'],
                                     boundary['skeleton'], primitive_bases=deferred, check=check)
    if absorption is None:
        result['reason'] = 'annular_core_attachment'
        return result
    augmented, absorption_proof, absorbed = absorption
    core = (prepared_core if prepared_core is not None and
            len(augmented['handles2']) == len(parallelity['geometry']['core']['handles2'])
            else core_handlebody_certificate(augmented, forest=forest, defer_forest=defer_forest, check=check))
    result['stats']['core'] = core.get('stats', {})
    if core['status'] != 'COMPLETE':
        result['reason'] = core['reason']
        return _kernel_fallback(result, parallelity, boundary, record_certificate, check, forest=forest, defer_forest=defer_forest)
    core_annuli = {}
    if core_side:
        transported = core_primitive_annuli(parallelity['geometry'], parallelity['summary'],
            boundary['skeleton'], augmented, core['certificate'], check=check)
        if transported is None:
            result['reason'] = 'annular_core_attachment'
            return _kernel_fallback(result, parallelity, boundary, record_certificate, check, forest=forest, defer_forest=defer_forest)
        core_annuli_proof, core_annuli, result['stats']['core_annuli'] = transported
    census, reason = _census(parallelity['geometry'], parallelity['summary'],
                            boundary['skeleton'], core['components'], check, absorbed, primitive, core_annuli)
    if census is None:
        result['reason'] = reason
        return result
    result.update(status='COMPLETE', census=census)
    if record_certificate:
        result['certificate'] = dict(schema='normal-cut-handlebodies-v1',
            parallelity=parallelity['certificate'], boundary=boundary['certificate'],
            core=core['certificate'], census=census)
        if absorbed:
            result['certificate'].update(schema='normal-cut-handlebodies-v2',
                                         absorption=absorption_proof)
        if primitive:
            result['certificate'].update(schema='normal-cut-handlebodies-v3',
                                         absorption=absorption_proof, primitive_annuli=primitive_proof)
        if core_side:
            result['certificate'].update(schema='normal-cut-handlebodies-v4',
                                         absorption=absorption_proof, core_annuli=core_annuli_proof)
    check()
    return result


def normal_cut_handlebodies(triangulation, coordinates, *, max_cycles=None,
                           record_certificate=False, precheck_core=True, boundary_method='masks',
                           top_forest='max_weight', lower_forest='adaptive', check=lambda: None):
    """Classify the whole supplied cut when the disk-gluing criterion succeeds.

    A COMPLETE result is an exact binary multiplicity census of handlebodies.
    An INCONCLUSIVE result is neither a knottedness nor a non-handlebody proof.
    Source validity is the established compact orientable one-torus contract.
    The four source queries and one or two boundary queries share the cycle
    allowance; cancellation callbacks also cover the finite core/interface work. The
    optional core precheck defaults on: a raw obstruction skips boundary
    discovery, without claiming any negative topological conclusion. The
    boundary_method chooses legacy endpoint masks or a single moment census.
    top_forest minimizes retained raw incidence by default; queue retains the
    earlier top-handle selector. Neither choice guarantees later cancellation.
    The adaptive lower policy tries the source forest, then maximum original
    passage weight on refusal, then deferred full-matrix selection. It shares
    every orbit query between attempts. Deferred lower discovery follows a
    fixed top reduction priced against the historical source lower forest;
    its completeness concerns lower choices for those retained rows only.
    """
    check()
    if type(boundary_method) is not str or boundary_method not in ('masks', 'moments'):
        raise ValueError('boundary_method must be masks or moments')
    if type(top_forest) is not str or top_forest not in ('queue', 'max_weight'):
        raise ValueError('top_forest must be queue or max_weight')
    if type(lower_forest) is not str or lower_forest not in ('adaptive', 'source', 'max_passages', 'reverse_id', 'deferred'):
        raise ValueError('invalid lower_forest policy')
    if type(precheck_core) is not bool:
        raise ValueError('precheck_core must be bool')
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    result = dict(status='INCONCLUSIVE', stats={},
                  trust='source cut handlebodies; no standalone knot verdict')
    parallelity = normal_cut_parallelity(triangulation, coordinates,
        max_cycles=max_cycles, record_certificate=record_certificate, check=check)
    result['stats']['parallelity'] = parallelity['stats']
    if parallelity['status'] != 'COMPLETE':
        result['reason'] = 'parallelity_budget_exhausted'
        return result
    boundary = None
    def discover_boundary():
        nonlocal boundary
        if boundary is None:
            remaining = max_cycles
            if remaining is not None:
                remaining -= sum(s['orbit_cycles'] for s in parallelity['stats'].values())
            if boundary_method == 'moments':
                fingerprint = parallelity['certificate']['input_sha256'] if record_certificate else None
                boundary = _compile_moment_boundary(parallelity['geometry'], fingerprint, remaining,
                                                     record_certificate, check, 'pair')
            else:
                boundary = normal_parallelity_boundary_words(triangulation, coordinates,
                    max_cycles=remaining, record_certificate=record_certificate, check=check)
        return boundary

    modes = ('source', 'max_passages', 'deferred') if lower_forest == 'adaptive' else (lower_forest,)
    attempts = []
    source_core = parallelity['geometry']['core']
    for mode in modes:
        check()
        forest = None if mode in ('source', 'deferred') else select_core_forest(source_core, strategy=mode, check=check)
        if attempts and mode == 'max_passages' and set(forest) == set(select_core_forest(source_core, strategy='source', check=check)):
            continue  # Same fixed forest; still allow full-matrix deferred discovery.
        result = _attempt_cut(parallelity, discover_boundary, record_certificate,
                              precheck_core, top_forest, forest, check, defer_forest=mode == 'deferred')
        attempts.append(dict(strategy=mode, status=result['status'], reason=result.get('reason')))
        if result['status'] == 'COMPLETE' or result.get('reason') == 'boundary_budget_exhausted':
            break
    if len(attempts) > 1 or lower_forest not in ('source', 'adaptive'):
        result['stats']['lower_forest_attempts'] = attempts
    check()
    return result
