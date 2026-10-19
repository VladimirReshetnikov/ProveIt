#!/usr/bin/env python3
"""Check integrity and mutual consistency of the completed 238-state evidence.

This script reads packaged tables, sources, and completed receipts as data.
It checks their byte hashes, state renumbering, structural source census,
recorded trace rows, all per-case affine clocks, and complete startup-frame
data. It does NOT execute the Turing machine, rerun the symbolic runtime or
selector-guard proof, replay source transformations, or invoke Lean.
All requirements use explicit exceptions and remain active under Python -O.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
SCOPE = ('Integrity and consistency of completed evidence against exact packaged '
         'bytes; no TM execution, symbolic runtime/guard proof replay, source '
         'transformation replay, or Lean kernel replay.')
FINAL_OLD = '069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c'
FINAL_CANONICAL = '909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08'
SOURCE = '7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6'
BASE_SOURCE = '74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d'
PHY = [6, 2, 0, 4, 3, 7, 8, 5, 1]


class IntegrityError(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise IntegrityError(message)


def integer(value, minimum=None):
    return type(value) is int and (minimum is None or value >= minimum)


def affine(value, label, nonnegative=False):
    require(isinstance(value, list) and len(value) == 13,
            label + ': expected thirteen affine coefficients')
    require(all(integer(x, 0 if nonnegative else None) for x in value),
            label + ': invalid affine coefficient')


def table(raw, label, default_start=None):
    rows, start = {}, None
    for number, line in enumerate(raw.decode('utf-8').splitlines(), 1):
        if line.startswith('#! start '):
            require(start is None, label + ': duplicate start')
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            fields = line.split()
            require(len(fields) == 5, f'{label}:{number}: malformed row')
            q, b, w, d, n = fields
            q, b, w, n = map(int, (q, b, w, n))
            require(q >= 0 and n >= 0 and b in (0, 1) and w in (0, 1)
                    and d in ('L', 'R'), label + ': invalid action')
            require((q, b) not in rows, label + ': duplicate row')
            rows[q, b] = (w, 1 if d == 'R' else -1, n)
    if start is None:
        start = default_start
    states = {q for q, _ in rows}
    require(start in states, label + ': missing/invalid start')
    require(set(rows) == {(q, b) for q in states for b in (0, 1)},
            label + ': working state without both rows')
    return rows, start


def source_census(sites, label):
    require(isinstance(sites, list), label + ': source must be a list')
    leaves = {}
    for item in sites:
        require(isinstance(item, list) and len(item) == 3, label + ': invalid site')
        p, op, arg = item
        require(isinstance(p, str) and p and len(p) <= 64 and set(p) <= {'0', '1'},
                label + ': invalid binary path')
        require(p not in leaves, label + ': duplicate site')
        require(op in ('CI', 'CD', 'CB', 'CC', 'CH'), label + ': invalid opcode')
        if op in ('CI', 'CD'):
            require(integer(arg, 0) and arg < 9, label + ': invalid register')
        elif op in ('CB', 'CC'):
            require(integer(arg, 1), label + ': invalid control depth')
        else:
            require(arg is None, label + ': halt operand')
        leaves[p] = (op, arg)
    require(list(leaves) == sorted(leaves), label + ': sites not in path order')
    prefixes = {p[:i] for p in leaves for i in range(len(p))}
    require(not prefixes.intersection(leaves), label + ': non-prefix-free leaves')
    require(len(prefixes) + 1 == len(leaves), label + ': non-full binary tree')
    require(all(p + b in leaves or p + b in prefixes for p in prefixes for b in '01'),
            label + ': missing child')
    intern = {}
    def visit(p):
        key = leaves[p] if p in leaves else (visit(p + '0'), visit(p + '1'))
        if key not in intern:
            intern[key] = len(intern)
        return intern[key]
    visit('')
    kinds = len(set(leaves.values()))
    counts = dict(sorted(Counter(op for op, arg in leaves.values()).items()))
    return dict(leaves=len(leaves), leaf_kinds=kinds, dag_nodes=len(intern),
                internal_source_nodes=len(intern) - kinds,
                max_path=max(map(len, leaves)),
                max_zero_run=max(len(z) for p in leaves for z in p.split('1')),
                operations=counts)


def diff_rows(before, after):
    def action(row):
        return None if row is None else [row[0], 'R' if row[1] == 1 else 'L', row[2]]
    return [dict(state=q, read=b, old=action(before.get((q, b))),
                 new=action(after.get((q, b))))
            for q, b in sorted(before.keys() | after.keys())
            if before.get((q, b)) != after.get((q, b))]


def expected_motion(site, positive):
    p, op, arg = site
    if op == 'CH':
        return None
    if op == 'CC':
        overflow = 0
    else:
        if op in ('CB', 'CD') and not (op == 'CD' and positive):
            needed = arg if op == 'CB' else 1
            found = [i for i, b in enumerate(p) if b == '0']
            p = p[:found[-needed]] if len(found) >= needed else ''
        overflow = int('0' not in p)
    return [-overflow] + [0] * 12


def verify(root):
    hashes, links, groups = {}, 0, []
    def raw(name):
        path = root / name
        require(path.is_file(), 'Missing packaged file: ' + name)
        data = path.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        if name in hashes:
            require(hashes[name] == digest, 'Packaged file changed during check: ' + name)
        hashes[name] = digest
        return data
    def load(name):
        return json.loads(raw(name))
    def pin(name, expected):
        nonlocal links
        raw(name)
        require(hashes[name] == expected, 'SHA-256 mismatch: ' + name)
        links += 1
    def status(receipt, expected, label):
        require(receipt.get('status') == expected, label + ': expected PASS status')
    def fields(receipt, expected, label):
        for key, value in expected.items():
            require(receipt.get(key) == value, label + ': inconsistent ' + str(key))

    old_name, canonical_name = 'machines/zfc238_old.tm', 'machines/zfc238.tm'
    source_name = 'source/sites_logical.json'
    baseline_name = 'vendor/boundary239/baseline/rotation240/sites_logical.json'
    boundary_name = 'vendor/boundary239/candidate239/zfc_boundary239_old.tm'
    reference_name = 'vendor/boundary239/boundary240/boundary240_old.tm'
    rotation_name = 'vendor/boundary239/baseline/rotation240/zfc_rotation240_old.tm'
    pin(old_name, FINAL_OLD); pin(canonical_name, FINAL_CANONICAL)
    pin(source_name, SOURCE); pin(baseline_name, BASE_SOURCE)
    old, start = table(raw(old_name), old_name)
    canonical, canonical_start = table(raw(canonical_name), canonical_name)
    boundary, _ = table(raw(boundary_name), boundary_name, 95)
    reference, _ = table(raw(reference_name), reference_name, 95)
    rotation, _ = table(raw(rotation_name), rotation_name, 95)
    states = {q for q, b in old}
    require(len(states) == 238 and len(old) == 476 and start == 95,
            'Wrong inherited-label table census/start')
    require({r[2] for r in old.values()} - states == {254}, 'Wrong inherited halt')
    require(not {169, 218} & states, 'Deleted state remains')
    require({q for q, b in canonical} == set(range(238)) and canonical_start == 0,
            'Wrong canonical state range/start')
    require({r[2] for r in canonical.values()} - set(range(238)) == {238},
            'Wrong canonical halt')
    renumbering = {int(k): v for k, v in load('machines/renumbering.json').items()}
    require(set(renumbering) == states | {254}
            and set(renumbering.values()) == set(range(239)), 'Invalid state bijection')
    fields(renumbering, {95: 0, 96: 84, 254: 238}, 'State bijection')
    require(canonical == {(renumbering[q], b): (w, d, renumbering[n])
                          for (q, b), (w, d, n) in old.items()},
            'Canonical rows do not match the exact action bijection')
    reached, todo = set(), [95]
    while todo:
        q = todo.pop()
        if q in reached:
            continue
        reached.add(q)
        if q != 254:
            todo.extend(old[q, b][2] for b in (0, 1))
    require(reached == states | {254}, 'Recorded graph reachability is inconsistent')
    groups.append('literal tables, canonical bijection, and graph census')

    sites = load(source_name); baseline_sites = load(baseline_name)
    census = source_census(sites, source_name)
    baseline_census = source_census(baseline_sites, baseline_name)
    guards = [(i, positive) for i, site in enumerate(sites)
              for positive in ((False, True) if site[1] == 'CD' else (False,))]
    require(len(sites) == 6455 and len(guards) == 8386, 'Wrong source/guard census')
    require([s[1:] for s in sites] == [s[1:] for s in baseline_sites],
            'Recorded ordered instruction word differs')
    require((census['dag_nodes'], census['max_path'], census['max_zero_run']) == (224, 48, 6),
            'Wrong final source structure')

    construction = load('evidence/construction.json')
    status(construction, 'EXACT_238_CONSTRUCTION_PASS', 'Construction')
    fields(construction, dict(working_states=238, transition_rows=476,
           separate_halt_state=238, canonical_start=0, canonical_dispatcher=84,
           deleted_inherited_states=[169, 218], all_working_states_graph_reachable=True,
           canonical_sha256=FINAL_CANONICAL, inherited_sha256=FINAL_OLD,
           source_sha256=SOURCE, exact_blank_prefix_steps=409835), 'Construction')
    require(construction['changes_from_boundary239'] == diff_rows(boundary, old),
            'Construction boundary-table row differences disagree')
    require(construction['changes_from_rotation240'] == diff_rows(rotation, old),
            'Construction rotation-table row differences disagree')

    runtime = load('evidence/universal_runtime.json')
    status(runtime, 'UNIVERSAL_MATHEMATICAL_PASS', 'Runtime')
    fields(runtime, dict(working_states=238, transition_rows=476, cases=8386,
           symbolic_steps=2255513, minimum_actual_steps=13, table_sha256=FINAL_OLD,
           sites_sha256=SOURCE), 'Runtime')
    for key, name in [('checker_sha256', 'check_literal_runtime.py'),
                      ('engine_sha256', 'symbolic_runtime.py'),
                      ('helper_sha256', 'independent_runtime.py')]:
        pin('vendor/boundary239/validation/' + name, runtime[key])
    require(runtime['directly_used_rows'] == [list(row) for row in sorted(old)],
            'Runtime used-row list is not exactly all 476 packaged table rows')
    schemas = [(73, 1, 'B', 'B'), (95, 1, 'B', 'C'),
               (48, -1, 'B', 'B'), (112, -1, 'C', 'B')]
    require(len(runtime['blocks']) == 4, 'Wrong list-schema count')
    for block, schema in zip(runtime['blocks'], schemas):
        require(tuple(block[k] for k in ('entry', 'direction', 'before', 'after')) == schema,
                'Wrong list-schema interface')
        fields(block, dict(steps='v+2', arbitrary_contexts=True), 'List schema')
        for event in block['trace']:
            require(event[0] in ('literal', 'unary'), 'Unexpected event in list schema')
            q, b, w, d, n = event[1]
            require(old.get((q, b)) == (w, d, n), 'List-schema row differs from table')
    cases = load('evidence/universal_runtime_cases.json')
    require(isinstance(cases, list) and len(cases) == 8386, 'Incomplete runtime case array')
    symbolic_total = 0; kind_totals = Counter(); duration_min = None
    for number, (case, expected) in enumerate(zip(cases, guards)):
        label = f'Runtime case {number}'
        require(integer(case['site_index'], 0) and type(case['positive']) is bool,
                label + ': invalid guard identity')
        require((case['site_index'], case['positive']) == expected,
                label + ': missing, duplicated, reordered, or wrong guard')
        require(integer(case['symbolic_steps'], 1), label + ': nonpositive symbolic count')
        affine(case['duration'], label + ' duration', nonnegative=True)
        require(case['duration'][0] >= 1, label + ': no positive clock constant')
        affine(case['motion'], label + ' motion')
        kinds = case['kinds']
        require(isinstance(kinds, dict) and set(kinds) <= {'literal', 'unary', 'list'}
                and all(integer(v, 0) for v in kinds.values()), label + ': invalid rule census')
        require(sum(kinds.values()) == case['symbolic_steps'], label + ': rule-count sum')
        require(case['duration'][0] >= kinds.get('literal', 0), label + ': literal clock subtotal')
        wanted_motion = expected_motion(sites[expected[0]], expected[1])
        if wanted_motion is not None:
            require(case['motion'] == wanted_motion, label + ': recorded source-interface motion')
        symbolic_total += case['symbolic_steps']; kind_totals.update(kinds)
        duration_min = case['duration'][0] if duration_min is None else min(duration_min, case['duration'][0])
    require(symbolic_total == runtime['symbolic_steps'] and duration_min == runtime['minimum_actual_steps'],
            'Runtime summary does not aggregate the complete case array')
    groups.append('completed runtime receipt, all 476 listed rows, four schemas, and all 8386 case records')

    guard = load('evidence/boundary239_selector_guard.json')
    status(guard, 'FRESH_BOUNDARY239_UNBOUNDED_SELECTOR_GUARD_PASS', 'Selector guard')
    fields(guard, dict(working_states=239, transition_rows=478, complete_cases=8386,
           symbolic_steps=2247513, sites_sha256=SOURCE, boot_steps=409691,
           positive_runtime_entries=32, minimum_right_one_run=23,
           four_list_schemas_rederived_without_selector_visits=True,
           no_self_loop_at169=True), 'Selector guard')
    pin(boundary_name, guard['table_sha256'])
    pin('vendor/guard239/symbolic_runtime.py', guard['engine_sha256'])
    pin('verification/check_boundary_selector_guard.py', guard['wrapper_sha256'])
    require(len(boundary) == 478 and len({q for q, b in boundary}) == 239,
            'Selector-guard table census')
    require(all(boundary[169, b][2] != 169 for b in (0, 1)), 'Selector table has a hidden self-loop')
    fields(guard['input_validation'], dict(working_states=239, complete_binary_tree=True,
           leaves=6455, maximum_depth=48, exact_boundary_source_pin=SOURCE), 'Guard input receipt')
    fields(guard['boot_endpoint'], dict(state=96, head=-5, one_cells=351), 'Guard boot endpoint')
    boot_entries = guard['boot_selector_entries']
    require(len(boot_entries) == 18, 'Wrong recorded boot-selector entry count')
    ticks = []
    for entry in boot_entries:
        require(integer(entry['tick'], 0) and entry['tick'] < guard['boot_steps']
                and integer(entry['head']), 'Invalid boot-selector event location')
        require(entry['read'] in (0, 1) and entry['right_bit'] in (0, 1), 'Invalid boot-selector bits')
        require(entry['read'] == 0 or entry['right_bit'] == 1, 'Recorded boot-selector guard failure')
        ticks.append(entry['tick'])
    require(ticks == sorted(set(ticks)), 'Repeated or unordered boot-selector events')
    entries = guard['runtime_selector_entries']; margins = []
    require(len(entries) == 96, 'Wrong recorded runtime-selector event count')
    guard_ids = set(guards)
    for number, entry in enumerate(entries):
        active = entry['case']; i = active['index']; positive = active['positive']
        require(integer(i, 0) and i < len(sites) and type(positive) is bool
                and (i, positive) in guard_ids and active['site'] == sites[i],
                f'Selector event {number}: case/source identity mismatch')
        require(entry['read'] in (0, 1), 'Invalid selector read bit')
        if 'right_run_length' in entry:
            length = entry['right_run_length']
            affine(length, f'Selector event {number} run length', nonnegative=True)
            require(length[0] >= 1, 'Recorded selector run might be empty')
            if entry['read'] == 1:
                require(length[0] >= 2, 'Recorded selector one-run violates guard')
                margins.append(length[0])
                require(length[1:] == [1] + [0] * 11, 'Unexpected recorded guard variable margin')
        else:
            require(entry.get('right_word') == 'zero exterior' and entry['read'] == 0,
                    'Unrecognized selector exterior event')
    require(len(margins) == guard['positive_runtime_entries'] == 32
            and min(margins) == guard['minimum_right_one_run'] == 23 and max(margins) == 59,
            'Selector margin summary disagrees with recorded entries')
    groups.append('completed selector-guard receipt and all 18 boot / 96 runtime event records')

    composition = load('evidence/composition_certificate.json')
    status(composition, 'INDEPENDENT_238_COMPOSITION_PASS', 'Composition')
    fields(composition, dict(working_states=238, transition_rows=476, deleted_states=[169, 218],
           all_states_graph_reachable=True, commuting_square=True, independently_replayed_blocks=24,
           distinct_block_identities=12, no_cross_patch_block_interference=True), 'Composition')
    pin('verification/check_composition.py', composition['checker_sha256'])
    # Historical path strings identify inputs only; no absolute historical path is opened.
    input_map = {'boundary240_old.tm': reference_name,
                 'zfc_boundary239_old.tm': boundary_name, 'zfc238_old.tm': old_name}
    require(len(composition['input_sha256']) == 3, 'Composition input count')
    seen_inputs = set()
    for historical_name, digest in composition['input_sha256'].items():
        name = Path(historical_name).name
        require(name in input_map and name not in seen_inputs, 'Unknown/repeated composition input')
        seen_inputs.add(name); pin(input_map[name], digest)
    # The unnamed fourth corner is obtained by the recorded three row changes
    # and deletion; this is literal table-data comparison, not execution.
    partner = {k: v for k, v in reference.items() if k[0] != 169}
    for row in [(80, 0), (91, 1), (147, 0)]:
        partner[row] = old[row]
    stored_rows = []
    for key, before, after in [('delayed_on_boundary239', boundary, old),
                               ('boundary_after_delayed', partner, old)]:
        item = composition[key]; status(item, 'PASS', key)
        require(len(item['blocks']) == 6, key + ': wrong stored block count')
        used = set()
        for block in item['blocks']:
            require(block['complete_tapes_equal'] is True, key + ': failed stored block')
            for side, tab in [('old', before), ('new', after)]:
                trace = block[side + '_trace']; steps = block[side + '_steps']
                require(integer(steps, 1) and len(trace) == steps, key + ': trace duration mismatch')
                q, h = block[side + '_state'], 0
                for event in trace:
                    require(isinstance(event, list) and len(event) == 6, key + ': malformed stored trace')
                    eq, eh, b, w, d, n = event
                    require((eq, eh) == (q, h), key + ': discontinuous stored trace')
                    require(tab.get((q, b)) == (w, d, n), key + ': trace action does not match exact table')
                    used.add((q, b)); q, h = n, h + d
                require((q, h) == (block['endpoint_state'], block['endpoint_head']),
                        key + ': trace endpoint metadata mismatch')
        stored_rows.append(used)
    delayed_changed = {k for k in reference.keys() | partner.keys() if reference.get(k) != partner.get(k)}
    boundary_changed = {k for k in reference.keys() | boundary.keys() if reference.get(k) != boundary.get(k)}
    for name, values in [('delayed_changed_rows', delayed_changed), ('boundary_changed_rows', boundary_changed),
                         ('delayed_block_rows', stored_rows[0]), ('boundary_block_rows', stored_rows[1])]:
        require(composition[name] == [list(x) for x in sorted(values)], 'Composition row set mismatch: ' + name)
    require(not stored_rows[0] & boundary_changed and not stored_rows[1] & delayed_changed,
            'Recorded cross-patch trace separation fails')
    groups.append('composition input hashes, 12 stored block identities, and trace/table row consistency')

    equivalence = load('evidence/source_equivalence.json')
    status(equivalence, 'PASS_EXACT_SOURCE_CONTROL_CERTIFICATE', 'Source equivalence')
    fields(equivalence, dict(baseline_sha256=BASE_SOURCE, candidate_sites_sha256=SOURCE,
           stages=13, local_rotations=25, guards_or_edges_checked_per_stage=8385,
           halt_descriptors_checked_per_stage=1, canonical_successor_paths=True,
           initial=baseline_census, final=census), 'Source equivalence')
    cert_name = 'vendor/boundary239/formalism/extra/rotation_certificate.json'
    pin(cert_name, equivalence['certificate_sha256'])
    certificate = load(cert_name)
    require(certificate['baseline_sha256'] == BASE_SOURCE, 'Rotation certificate baseline mismatch')
    steps = certificate['steps']; stage_results = equivalence['stage_results']
    require(len(steps) == len(stage_results) == 13, 'Source stage census')
    for number, (step, receipt) in enumerate(zip(steps, stage_results), 1):
        require(step['number'] == receipt['stage'] == number
                and len(step['paths']) == receipt['simultaneous_rotations']
                and step['direction'] == receipt['direction'], 'Source stage metadata mismatch')
        require(receipt['leaves'] == 6455 and receipt['operations'] == census['operations'],
                'Source stage instruction census mismatch')
    require(sum(len(step['paths']) for step in steps) == 25, 'Source rotation total mismatch')
    require(all(stage_results[-1][k] == census[k] for k in census), 'Source final-stage census mismatch')
    for name, digest in [('vendor/boundary239/formalism/extra/baseline_sites.json', BASE_SOURCE),
                         ('vendor/boundary239/formalism/extra/boundary224_sites.json', SOURCE)]:
        pin(name, digest)

    interface = load('evidence/source_interface.json')
    status(interface, 'EXACT_LEAN_SOURCE_DATA_AND_SEED_IDENTITY_PASS', 'Source interface')
    fields(interface, dict(source_sites_sha256=BASE_SOURCE, root=202, declared_storage_bound=203,
           raw_lookup_all_203_indices_verified=True, reachable_internal_nodes=202,
           unreachable_internal_nodes=[4], row169_occurrences=4,
           ordered_source_triples_exactly_equal=6455, guards=8386, max_path_length=51,
           max_path_zero_run=6, distinct_leaf_kinds=23, blank_prefix_steps=409691,
           bootstrap_frame_literal_shape_matches=True), 'Source interface')
    require(len(interface['source_files']) == 6, 'Source interface file count')
    blobs = {}
    for item in interface['source_files']:
        name = 'vendor/boundary239/source_interface/' + item['file']
        pin(name, item['sha256']); data = raw(name)
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode('ascii') + b'\0' + data).hexdigest()
        require(blob == item['git_blob_sha'], 'Packaged Lean source Git blob mismatch: ' + name)
        blobs[item['file']] = blob
    predecessor_name = 'vendor/boundary239/candidate239/blank_prefix.json'
    pin(predecessor_name, interface['blank_prefix_sha256'])
    compatibility = load('evidence/current_pin_compatibility.json')
    status(compatibility, 'EXACT_CURRENT_PIN_COMPATIBILITY_PASS', 'Current pin compatibility')
    fields(compatibility, dict(repository_commit='ce192939372ac7944fe2a0208c68a96d49fb5e3b'), 'Current pin')
    require(len(compatibility['checks']) == 9, 'Current pin check count')
    for item in compatibility['checks']:
        require(item['equal'] is True, 'Failed current-pin comparison')
        if 'path' in item:
            blob = blobs[Path(item['path']).name]
            require(item['inherited_blob'] == item['current_blob'] == blob,
                    'Current-pin recorded blobs do not match packaged source')
        else:
            pin('vendor/boundary239/baseline/rotation240/' + item['baseline_file'], item['sha256'])
    groups.append('source equivalence/interface/current-pin receipts and exact packaged source bytes')

    boot = load('evidence/blank_prefix.json'); predecessor = load(predecessor_name)
    status(boot, 'EXACT_238_SPARSE_DENSE_CANONICAL_BOOT_PASS', 'Startup')
    status(predecessor, 'EXACT_SPARSE_DENSE_AND_CANONICAL_AGREEMENT', 'Predecessor startup')
    fields(boot, dict(steps=409835, initial_state=0, initial_head=0, final_state=84,
           final_state_old=96, final_head=-5, marker=-6, header=176, header_distance=181,
           additional_gap=117, pc='', one_count=351, all_other_cells_zero=True,
           head_range=[-15, 701], agrees_with_boundary239_complete_configuration=True,
           predecessor_steps=409691, additional_steps=144, table_sha256=FINAL_OLD,
           canonical_table_sha256=FINAL_CANONICAL), 'Startup')
    require(boot['steps'] - predecessor['steps'] == boot['additional_steps'] == 144,
            'Startup clock comparison mismatch')
    for key in ['final_state_old', 'final_head', 'marker', 'header', 'header_distance', 'pc',
                'logical_registers', 'physical_registers', 'spare_values',
                'all_one_positions', 'all_other_cells_zero', 'one_count', 'head_range']:
        require(boot[key] == predecessor[key], 'Complete predecessor startup data differs: ' + key)
    require(boot['all_one_positions'] == sorted(set(boot['all_one_positions']))
            and len(boot['all_one_positions']) == boot['one_count'], 'Startup one-cell inventory')
    logical = [boot['physical_registers'][i] for i in PHY]
    require(logical == boot['logical_registers'] == [3, 0, 0, 0, 3, 0, 0, 0, 0],
            'Startup physical/logical seed permutation mismatch')
    require(boot['spare_values'] == [1] * 167, 'Startup spare suffix mismatch')
    expected_ones = {boot['marker'], boot['header']}; cursor = boot['header'] + 1
    for value in boot['physical_registers'] + boot['spare_values']:
        require(integer(value, 0), 'Invalid recorded unary value')
        expected_ones.update(range(cursor + 1, cursor + value + 2)); cursor += value + 2
    require(sorted(expected_ones) == boot['all_one_positions'],
            'Startup complete one-cell inventory does not encode the reported frame')
    seed = interface['seed']
    fields(seed, dict(pc='', logical_registers=logical, physical_registers=boot['physical_registers'],
           registers_at_indices_ge_9=0, spare_count=167, spare_value=1), 'Source/startup seed')
    require(list(seed['record'].values()) == logical, 'Named logical seed record mismatch')
    groups.append('complete 351-cell startup inventory, seed encoding, and predecessor clock/frame receipts')

    audit = load('evidence/audit_summary.json')
    status(audit, 'INDEPENDENT_COMPOSITION_AND_GUARD_AUDIT_PASS', 'Audit summary')
    fields(audit, dict(literal_candidate_old_sha256=FINAL_OLD, working_states=238,
           transition_rows=476, guard_fully_discharged_for_exact_boundary239_source=True,
           finite_local_status=composition['status'], selector_guard_status=guard['status']), 'Audit summary')
    fields(audit['new_source_one_run_margin'], dict(constant_minimum=min(margins),
           constant_maximum=max(margins), variable_term='nonnegative header gap G'), 'Audit margin')
    audit_files = {'boundary239_selector_guard.json': 'evidence/boundary239_selector_guard.json',
                   'boundary239_selector_guard.log': 'evidence/boundary239_selector_guard.log',
                   'check_boundary_selector_guard.py': 'verification/check_boundary_selector_guard.py',
                   'check_composition.py': 'verification/check_composition.py',
                   'composition_certificate.json': 'evidence/composition_certificate.json',
                   'composition_proof.tex': 'sections/composition.tex'}
    require(set(audit['audit_files']) == set(audit_files), 'Audit inventory mismatch')
    for name, digest in audit['audit_files'].items():
        pin(audit_files[name], digest)
    groups.append('independent audit summary and all six linked audit files')

    provenance = load('file_provenance.json')
    require(isinstance(provenance, list), 'File provenance must be a list')
    provenance_pins = {}
    for item in provenance:
        name = item['file']
        require(isinstance(name, str) and not Path(name).is_absolute()
                and '..' not in Path(name).parts and name not in provenance_pins,
                'Invalid or repeated provenance file name')
        provenance_pins[name] = item['sha256']
    # The runtime summary does not itself include a case-array digest. Bind the
    # complete array to the separate packaged provenance record before reporting
    # that its exact duration data agree with the completed evidence.
    for name in ['evidence/universal_runtime.json', 'evidence/universal_runtime_cases.json',
                 'evidence/source_equivalence.json', 'evidence/source_interface.json']:
        require(name in provenance_pins, 'Missing completed-receipt provenance pin: ' + name)
    provenance_links = 0
    for name in sorted(set(hashes).intersection(provenance_pins)):
        pin(name, provenance_pins[name]); provenance_links += 1
    groups.append('packaged provenance pins for inspected files, including the complete duration case array')

    return dict(status='PACKAGED_EVIDENCE_INTEGRITY_AND_CONSISTENCY_PASS', scope=SCOPE,
                fresh_runtime_replay=False, fresh_guard_replay=False,
                fresh_source_transformation_replay=False, fresh_Lean_replay=False,
                working_states=238, transition_rows=476, canonical_halt=238,
                source_leaves=6455, complete_guard_cases_checked=len(cases),
                exact_used_row_inventory_checked=len(runtime['directly_used_rows']),
                affine_duration_vectors_checked=len(cases), affine_vector_width=13,
                affine_slot_order=['constant', 'header_gap'] + ['R' + str(i) for i in range(9)]
                                  + ['first_spare_value', 'remaining_spare_list_width'],
                all_duration_coefficients_nonnegative=True, minimum_duration_constant=duration_min,
                symbolic_rule_total_from_cases=symbolic_total, rule_kind_totals=dict(kind_totals),
                guard_boot_events_checked=len(boot_entries), guard_runtime_events_checked=len(entries),
                positive_guard_events_checked=len(margins), guard_constant_margin=[min(margins), max(margins)],
                stored_composition_block_identities_checked=12, recorded_blank_prefix_steps=boot['steps'],
                complete_startup_one_positions_checked=len(expected_ones),
                hash_links_checked=links, provenance_hash_links_checked=provenance_links,
                completed_case_array_sha256=hashes['evidence/universal_runtime_cases.json'],
                distinct_packaged_files_read=len(hashes),
                groups=groups, packaged_file_sha256=dict(sorted(hashes.items())),
                checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                limitation='Consistent hashes and receipt contents do not independently establish the '
                           'mathematical soundness of the previously executed proof checkers.')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, default=ROOT, help='Packaged construction directory')
    ap.add_argument('--output', type=Path, help='Defaults to ROOT/evidence/evidence_consistency.json')
    args = ap.parse_args(); root = args.root.resolve()
    output = args.output if args.output is not None else root / 'evidence/evidence_consistency.json'
    try:
        result = verify(root)
        code = 0
    except (IntegrityError, OSError, ValueError, KeyError, TypeError) as error:
        result = dict(status='PACKAGED_EVIDENCE_INTEGRITY_AND_CONSISTENCY_FAIL', scope=SCOPE,
                      reason=str(error), checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
        code = 1
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items() if k not in ('packaged_file_sha256', 'groups')}, indent=2))
    return code


if __name__ == '__main__':
    sys.exit(main())
