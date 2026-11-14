#!/usr/bin/env python3
"""Complete the two previously partial archived 196-state certificates.

Requires the original archive extraction under ./extracted (as listed in
196_frontier.json), or --extracted PATH. Uses only Python's standard library
and the symbolic checkers supplied in those archives. Each case runs in a
fresh subprocess to keep identically named imported modules separate.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

BASE = Path(__file__).resolve().parent


def zerojump(extracted, output):
    folder = extracted / 'pa_tm_research_2026-11-13 (2)/pa_tm_research_2026-11-13/verification/zero_jump_machine'
    sys.path.insert(0, str(folder))
    import verify as verifier
    verifier.check_inputs()
    sites = verifier.S.all_sites()
    machine = verifier.S.load_machine()
    machine[verifier.S.LITERAL[27], 1] = (1, 1, verifier.S.LITERAL[17])
    table = folder.parent / 'low_level_search/inputs/cd3_parent196.tm'
    assert machine == verifier.S.load_machine(table)
    runtime = verifier.contracts_receipt(machine, list(verifier.S.contracts()))
    startup = verifier.startup(machine, sites)
    assert runtime['contracts_checked'] == 4959 and not runtime['failures']
    assert startup['steps'] == 58366
    result = {'name': 'zerojump_cd3', 'literal_sha256': hashlib.sha256(table.read_bytes()).hexdigest(),
              'runtime': runtime, 'startup': startup,
              'scope': 'Fresh full replay of all 4959 contracts under the documented source 26 zero invariant, plus exact whole-tape blank startup.'}
    (output / 'zerojump_cd3_fresh_audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print('Zerojump CD3: 4959 contracts, exact 58366-step startup.')


def combined(extracted, output):
    folder = extracted / 'conpa_tm_study_2026-11-13/conpa_tm_study'
    sys.path.insert(0, str(folder / 'verification'))
    import symbolic as symbol
    table = folder / 'research/helper_search/rebracket_combined196.tm'
    machine = symbol.load_machine(table)
    def sites(path):
        return [(tuple(address), tuple(opcode)) for address, opcode in json.loads(path.read_text())]
    current = sites(table.parent / 'rebracket_combined196_sites.json')
    reference = sites(folder / 'machines/h_only_mp_h_sites.json')
    assert [entry[1] for entry in current] == [entry[1] for entry in reference]
    assert symbol.instructions(current) == symbol.instructions(reference)
    assert symbol.check_engine(machine)
    symbol.all_sites = lambda: current
    runtime, _ = symbol.verify(machine)
    assert runtime['contracts'] == 4928
    head = -2
    target = {head - 1, head + 48} | {head + i for i, bit in enumerate(current[25][0]) if bit}
    pos = head + 49
    for value in [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26:
        pos += 1
        target.update(range(pos, pos + value + 1))
        pos += value + 1
    state = head = 0
    ones = set()
    for ticks in range(1, 150001):
        write, direction, state = machine[state, int(head in ones)]
        (ones.add if write else ones.discard)(head)
        head += direction
        if state == 75 and head == -2 and ones == target:
            break
    else:
        raise ValueError('Exact clean startup seed not reached')
    assert ticks == 57922
    result = {'name': 'rebracket_combined196', 'literal_sha256': hashlib.sha256(table.read_bytes()).hexdigest(),
              'source_sites': len(current), 'runtime': runtime, 'startup_literal_steps': ticks,
              'complete_startup_ones': sorted(ones), 'head': head, 'state': state,
              'ordered_primitive_word_and_all_CFG_edges_identical_to_Combined196': True,
              'all_protected_engine_rows_equal': True,
              'scope': 'Fresh full runtime and exact complete-tape seed replay; retains the Combined196 command-calibration argument.'}
    (output / 'rebracket_combined196_fresh_audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print('Rebracketed Combined196: 4928 contracts, exact 57922-step startup, full word/CFG identity.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--extracted', type=Path, default=BASE / 'extracted')
    parser.add_argument('--output', type=Path, default=BASE)
    parser.add_argument('--case', choices=['zerojump', 'combined'])
    args = parser.parse_args()
    assert __debug__, 'Run without Python -O'
    args.output.mkdir(parents=True, exist_ok=True)
    if args.case:
        globals()[args.case](args.extracted.resolve(), args.output.resolve())
    else:
        for case in ('zerojump', 'combined'):
            subprocess.run([sys.executable, str(Path(__file__).resolve()), '--case', case,
                            '--extracted', str(args.extracted.resolve()), '--output', str(args.output.resolve())], check=True)


if __name__ == '__main__':
    main()
