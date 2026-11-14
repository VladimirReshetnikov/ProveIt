#!/usr/bin/env python3
"""Reconstruct the source-26 zero-jump certificate using Python 3.10+ only.

The symbolic executor summarizes unbounded register files using the unchanged
M6 engine lemmas. This is not a new Lean build or a sub-196 construction.
"""
from collections import defaultdict, deque
from pathlib import Path
import argparse
import hashlib
import json
import time

import symbolic as S

ROOT = Path(__file__).resolve().parent
REFERENCE = ROOT / 'reference'
PROGRAM_SHA256 = '8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872'
TABLE_SHA256 = 'e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8'
INVARIANT_SHA256 = '604a7915edb973658c1be8655751824a9424d26da180e45254cd82e13007b8ff'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_inputs():
    manifest = json.loads((ROOT / 'reference_manifest.json').read_text())
    for path, digest in manifest['sha256'].items():
        require(sha(REFERENCE / path) == digest, ('reference hash mismatch', path))
    require(sha(REFERENCE / 'PA196/Program.lean') == PROGRAM_SHA256, 'pinned source')
    require(sha(REFERENCE / 'data/pa196.tm') == TABLE_SHA256, 'pinned table')
    require(len(S.LABELS) == 197 and len(set(S.LABELS)) == 197, 'bijective labels')
    require((S.LABELS[0], S.LABELS[S.ROOT], S.LABELS[S.HALT]) == (74, 84, 254), 'control labels')
    return manifest


def interval_graph(sites):
    """A second CFG resolver, using ancestor leaf intervals rather than carry."""
    intervals = {}
    for i, (path, _) in enumerate(sites):
        for n in range(len(path) + 1):
            prefix = path[:n]
            if prefix not in intervals:
                intervals[prefix] = [i, i]
            else:
                intervals[prefix][1] = i

    def ancestor(path, bit, depth):
        positions = [j for j, b in enumerate(path) if b == bit]
        require(depth > 0 and len(positions) >= depth, ('invalid ancestor', path, bit, depth))
        return path[:positions[-depth]]

    def after(prefix):
        target = intervals[prefix][1] + 1
        require(target < len(sites), ('unexpected root exit', prefix))
        return target

    graph = []
    for i, (path, op) in enumerate(sites):
        tag = op[0]
        if tag == 'inc':
            graph.append(('inc', op[1], i + 1))
        elif tag == 'dec':
            graph.append(('dec', op[1], after(ancestor(path, 0, 1)), i + 1))
        elif tag == 'breakTo':
            graph.append(('jump', i + 1 if op[1] == 0 else after(ancestor(path, 0, op[1]))))
        elif tag == 'continueTo':
            graph.append(('jump', i if op[1] == 0 else intervals[ancestor(path, 1, op[1])][0]))
        elif tag == 'halt':
            graph.append(('halt',))
        else:
            raise ValueError(('unknown source instruction', op))
    return graph


def abstract_successors(row, mask):
    """Bit r is one precisely when the represented register r is positive."""
    if row[0] == 'halt':
        return ()
    if row[0] == 'jump':
        return ((row[1], mask),)
    if row[0] == 'inc':
        return ((row[2], mask | (1 << row[1])),)
    require(row[0] == 'dec', ('unknown resolved instruction', row))
    bit = 1 << row[1]
    if mask & bit:
        # Decrementing a positive natural can produce zero or remain positive.
        return ((row[3], mask & ~bit), (row[3], mask))
    return ((row[2], mask),)


def reconstruct_invariant(sites):
    graph = S.instructions(sites)
    require(graph == interval_graph(sites), 'independent CFG resolvers disagree')
    require(len(graph) == 3812, 'source-site count')
    initial = (25, 1)
    seen = {initial}
    pending = deque([initial])
    while pending:
        pc, mask = pending.popleft()
        for nxt in abstract_successors(graph[pc], mask):
            require(0 <= nxt[0] < len(graph) and 0 <= nxt[1] < 512, 'abstract state bounds')
            if nxt not in seen:
                seen.add(nxt)
                pending.append(nxt)
    require(initial in seen, 'initial abstract configuration missing')
    require(all(nxt in seen for pc, mask in seen for nxt in abstract_successors(graph[pc], mask)),
            'invariant not closed under every abstract successor')
    canonical = json.dumps(sorted(seen), separators=(',', ':')).encode()
    digest = hashlib.sha256(canonical).hexdigest()
    require(len(seen) == 274880 and digest == INVARIANT_SHA256, 'joint invariant changed')
    masks = defaultdict(set)
    for pc, mask in seen:
        masks[pc].add(mask)
    eligible = []
    for i, (path, op) in enumerate(sites):
        if op != ('breakTo', 1) or not masks[i]:
            continue
        possible_positive = 0
        for mask in masks[i]:
            possible_positive |= mask
        zero = [r for r in range(9) if not ((possible_positive >> r) & 1)]
        if zero:
            eligible.append(dict(site=i, path=''.join(map(str, path)), zero_registers=zero,
                                 mask_count=len(masks[i])))
    require(len(eligible) == 14, 'eligible jump-site count')
    site26 = next(row for row in eligible if row['site'] == 26)
    require(site26['zero_registers'] == [3, 6, 7], 'source26 zero-register invariant')
    require(graph[26] == ('jump', 34), 'source26 destination')
    unreachable = [i for i in range(len(graph)) if not masks[i]]
    require(unreachable == [3774, 3775], 'unreachable source-site inventory')
    return dict(source_sites=len(graph), seed_site=25, initial_registers=[2]+[0]*8,
                initial_mask=1, invariant_pairs=len(seen), invariant_sha256=digest,
                seed_included=True, every_abstract_successor_included=True,
                independent_resolvers_agree=True, unreachable_sites=unreachable,
                eligible_forward_jumps=eligible, site26_masks=sorted(masks[26]))


ORIGINAL_ORACLE = S.oracle


def known_zero_oracle(q, branch, box):
    """Use a conjunction of zero hypotheses instead of one branch hypothesis."""
    if isinstance(branch, frozenset):
        _, effect, reg = box
        if effect == 'mark' and q == S.LITERAL[0]:
            if reg in branch:
                return S.LITERAL[97], S.box(), False
            return None
        return ORIGINAL_ORACLE(q, None, box)
    return ORIGINAL_ORACLE(q, branch, box)


S.oracle = known_zero_oracle
ZERO26 = frozenset(S.PHYSICAL[r] for r in (3, 6, 7))


def execute_contract(machine, contract, trace=None):
    site, _, branch, initial, target = contract
    if site == 26:
        branch = ZERO26
    return S.execute(machine, branch, initial, target, fuel=1024, record=trace)


def census(machine):
    states = {q for q, b in machine}
    require(set(machine) == {(q, b) for q in states for b in (0, 1)}, 'two rows per state')
    require(all(w in (0, 1) and d in (-1, 1) for w, d, t in machine.values()), 'binary L/R table')
    terminal = {t for w, d, t in machine.values()} - states
    require(terminal == {S.HALT}, 'unique terminal')
    seen = {0}
    pending = [0]
    for q in pending:
        for b in (0, 1):
            t = machine[q, b][2]
            if t in states and t not in seen:
                seen.add(t)
                pending.append(t)
    return dict(working_states=len(states), rows=len(machine), graph_reachable=len(seen),
                start=0, root=S.ROOT, terminal=S.HALT)


def concrete_frame(sites, site, registers, gap=48, spares=(0,), head=0):
    """The complete finite support of a clean frame; the rest is all blank."""
    require(len(registers) == 9 and len(spares) >= 1, 'valid physical register file')
    path = sites[site][0]
    require(len(path) < gap, 'frame padding')
    ones = {head - 1, head + gap} | {head + i for i, b in enumerate(path) if b}
    physical = [0] * 9
    for i, value in enumerate(registers):
        physical[S.PHYSICAL[i]] = value
    pos = head + gap + 1
    for value in physical + list(spares):
        require(value >= 0, 'natural register value')
        pos += 1
        ones.update(range(pos, pos + value + 1))
        pos += value + 1
    return ones


def step(machine, q, head, ones):
    key = q, int(head in ones)
    require(key in machine, ('literal machine halted', q, head))
    write, move, target = machine[key]
    if write:
        ones.add(head)
    else:
        ones.discard(head)
    return target, head + move


def startup(machine, sites, bound=100000):
    expected = concrete_frame(sites, 25, [2]+[0]*8, spares=[1]*26, head=-2)
    ones = set()
    q = head = 0
    for count in range(1, bound + 1):
        q, head = step(machine, q, head, ones)
        if q == S.ROOT and head == -2 and ones == expected:
            return dict(steps=count, state=q, head=head, gap=48, site=25,
                        logical_registers=[2]+[0]*8, spares=[1]*26,
                        complete_tape_ones=sorted(ones))
    raise ValueError('specified whole-tape startup frame not reached within bound')


def contracts_receipt(machine, contracts):
    require(S.check_engine(machine), 'register-engine oracle rows changed')
    failures = []
    lengths = []
    for contract in contracts:
        result = execute_contract(machine, contract)
        if result is None:
            failures.append(list(contract[:2]))
        else:
            lengths.append(result[0])
    return dict(contracts_checked=len(contracts), failures=failures,
                max_symbolic_steps=max(lengths), sum_symbolic_steps=sum(lengths),
                unchanged_engine_rows=len(S.ENGINE_ROWS))


def synthesize_actions(baseline, contracts, sites):
    contract = next(c for c in contracts if c[0] == 26)
    machine = dict(baseline)
    actions = []
    for target in range(197):
        for write in (0, 1):
            for move in (-1, 1):
                machine[S.LITERAL[27], 1] = (write, move, target)
                if execute_contract(machine, contract) is not None:
                    actions.append(dict(dense_action=[write, move, target],
                                        native_action=[write, move, S.LABELS[target]],
                                        startup_steps=startup(machine, sites)['steps']))
    expected = [[1,-1,9],[0,-1,10],[1,1,17],[1,1,21],[0,-1,40],[1,-1,77],
                [1,-1,87],[1,-1,93],[1,-1,103],[1,1,103],[1,1,113],[0,-1,302]]
    require([row['native_action'] for row in actions] == expected, 'recognized action set changed')
    return dict(row_native=[27,1], row_dense=[S.LITERAL[27],1], actions_tested=788,
                symbolic_fuel=1024, recognized_actions=actions,
                scope='All accepted actions in this finite synthesis grammar; no completeness claim for arbitrary correct implementations.')


def rejection_witness(baseline, wrong_parent, rejected, sites):
    initial = concrete_frame(sites, 26, [0]*9)
    desired = concrete_frame(sites, 34, [0]*9)
    wrong = concrete_frame(sites, 27, [0,0,0,0,0,0,1,0,0], spares=(0,1))
    records = []
    for name, machine, expected, expected_steps in [
            ('baseline196', baseline, desired, 120),
            ('wrong_opcode_parent196', wrong_parent, wrong, 558),
            ('rejected195', rejected, wrong, 558)]:
        q, head, ones = S.ROOT, 0, set(initial)
        for count in range(1, 10001):
            q, head = step(machine, q, head, ones)
            if q == S.ROOT and head == 0 and ones == expected:
                require(count == expected_steps, ('counterexample step count', name))
                records.append(dict(machine=name, steps=count, state=q, head=head,
                                    complete_tape_ones=sorted(ones)))
                break
        else:
            raise ValueError(('counterexample endpoint missing', name))
    # The same incorrect branch also occurs on this candidate's literal blank run.
    blank_before = concrete_frame(sites, 26, [3,0,0,0,0,1,0,0,0],
                                  gap=52, spares=[1]*32, head=-2)
    blank_after = concrete_frame(sites, 27, [3,0,0,0,0,1,1,0,0],
                                 gap=52, spares=[1]*33, head=-2)
    q = head = 0
    ones = set()
    snapshots = []
    for count in range(1, 55187):
        q, head = step(rejected, q, head, ones)
        if count in (54392, 55186):
            expected = blank_before if count == 54392 else blank_after
            require(q == S.ROOT and head == -2 and ones == expected,
                    ('literal blank-run counterexample', count))
            snapshots.append(dict(step=count, site=26 if count == 54392 else 27,
                                  state=q, head=head, gap=52,
                                  complete_tape_ones=sorted(ones)))
    return dict(initial_site=26, initial_registers=[0]*9, initial_gap=48, initial_spares=[0],
                initial_complete_tape_ones=sorted(initial), intended_site=34,
                intended_registers=[0]*9, intended_complete_tape_ones=sorted(desired),
                wrong_site=27, wrong_registers=[0,0,0,0,0,0,1,0,0],
                wrong_spares=[0,1], finite_frame_runs=records, literal_blank_run=snapshots,
                scope='Refutes the advertised source26 zero-decrement binding. It does not prove this rejected machine halts or fails some unrelated consistency equivalence.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'receipts/reproduced.json')
    args = parser.parse_args()
    began = time.monotonic()
    manifest = check_inputs()
    sites = S.all_sites()
    invariant = reconstruct_invariant(sites)
    print('Invariant: 274880 pairs, 14 eligible forward-jump sites.', flush=True)
    baseline = S.load_machine()
    contracts = list(S.contracts())
    require(len(contracts) == 4959, 'uniform contract count')
    chosen = dict(baseline)
    chosen[S.LITERAL[27], 1] = (1, 1, S.LITERAL[21])
    wrong_parent = dict(baseline)
    wrong_parent[S.LITERAL[27], 1] = (1, 1, S.LITERAL[62])
    drop, keep = S.LITERAL[27], S.LITERAL[46]
    rejected = {(q,b):(w,d,keep if t == drop else t)
                for (q,b),(w,d,t) in wrong_parent.items() if q != drop}
    rejected[keep,0] = (0,-1,S.LITERAL[81])
    machines = [('zerojump196.tm', chosen, 196),
                ('wrong_opcode_parent196.tm', wrong_parent, 196),
                ('rejected195.tm', rejected, 195)]
    counts = {}
    for name, machine, expected_count in machines:
        require(S.load_machine(ROOT/'machines'/name) == machine, ('supplied artifact mismatch',name))
        counts[name] = census(machine)
        require(counts[name]['working_states'] == expected_count, ('state count', name))
        require(counts[name]['graph_reachable'] == expected_count, ('graph reachability', name))
    recognized = synthesize_actions(baseline, contracts, sites)
    print('Synthesis: 12 recognized row actions, each with exact clean startup.', flush=True)
    runtime = contracts_receipt(chosen, contracts)
    require(not runtime['failures'], 'chosen196 uniform runtime failure')
    seed = startup(chosen, sites)
    require(seed['steps'] == 58402, 'chosen196 exact startup duration')
    print('Zerojump196: 4959 symbolic contracts; whole-tape startup in 58402 steps.', flush=True)
    wrong_runtime = contracts_receipt(rejected, contracts)
    require(wrong_runtime['failures'] == [[26,'jump']], 'rejected195 failure set')
    witness = rejection_witness(baseline, wrong_parent, rejected, sites)
    print('Rejected195: source26 fails; exact counterexample also occurs on its blank run.', flush=True)
    out = dict(status='PASS', sub196_machine_certified=False,
               reference_commit=manifest['commit'], invariant=invariant,
               source26_synthesis=recognized, machine_counts=counts,
               chosen196=dict(runtime=runtime, startup=seed,
                              table_sha256=sha(ROOT/'machines/zerojump196.tm')),
               rejected195=dict(runtime=wrong_runtime, witness=witness),
               elapsed_seconds=time.monotonic()-began,
               scope='Finite inductive source invariant, symbolic runtime certificates using unchanged engine lemmas, exact finite startup, and a negative binding witness. No new formal PA endpoint or smaller valid machine is claimed.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2)+'\n')
    print('PASS; receipt:', args.output, flush=True)


if __name__ == '__main__':
    main()
