#!/usr/bin/env python3
"""Read-only replay of the literal macro audit; Python standard library only.

This checks recorded hashes, source bindings, literal pair identities, and
three-transition dispatch traces. It neither searches for machines nor proves
the inherited arithmetic calibration.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[2]
RECEIPT = Path(__file__).with_name('macro_audit.json')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def verified_bytes(item):
    payload = (ROOT/item['path']).read_bytes()
    require(hashlib.sha256(payload).hexdigest() == item['sha256'], 'Hash mismatch: '+item['path'])
    return payload


def parse(payload):
    rows = {}
    for line in payload.decode().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        q, bit, write, target = map(int, (q, bit, write, target))
        require(bit in (0, 1) and write in (0, 1) and direction in ('L', 'R'), 'Invalid literal row')
        require((q, bit) not in rows, 'Duplicate literal row')
        rows[q, bit] = [write, direction, target]
    require(len(rows) == 2*len({q for q, _ in rows}), 'Incomplete literal table')
    return rows


def main():
    audit = json.loads(RECEIPT.read_text())
    pairs_checked = 0
    main_rows = None
    for item in audit['input_tables']:
        rows = parse(verified_bytes(item))
        require(len(rows)//2 == item['working_controls'], 'Control count mismatch')
        if item['path'] == 'machine/raw.native.tm':
            main_rows = rows
        for pair in audit['pair_identities']:
            q = pair['native']
            if pair.get('only_if_present') and (q, 0) not in rows:
                continue
            require(rows[q, 0] == [0, 'R', pair['left']], 'Pair read0 mismatch: '+pair['name'])
            require(rows[q, 1] == [1, 'R', pair['right']], 'Pair read1 mismatch: '+pair['name'])
            pairs_checked += 1
    require(main_rows is not None, 'Main literal table missing')
    require(pairs_checked == audit['pair_checks_passed'], 'Pair-check count mismatch')
    dictionary = json.loads(verified_bytes(audit['source_dictionary']))
    for name, definition in audit['source_dictionary']['bindings'].items():
        require(dictionary[name] == definition, 'Source binding changed: '+name)
    for entry in audit['transparent_entries']:
        q = entry['native']
        require([main_rows[q, 0], main_rows[q, 1]] == entry['rows'], 'Entry rows changed')
        require(all(main_rows[q, bit][:2] == [bit, 'R'] for bit in (0, 1)), 'Entry is not transparent')
    traces_checked = 0
    for requirement in audit['incoming_bit_requirements']:
        bit = requirement['distinguishing_read_bit']
        endpoints = []
        for expected in requirement['three_step_traces']:
            preceding = expected['preceding_bit']
            tape = {-1:preceding, 0:bit}
            state, head, steps = requirement['native'], 0, []
            for _ in range(3):
                require(head in tape, 'Trace reads an exterior cell')
                scanned = tape[head]
                write, direction, target = main_rows[state, scanned]
                steps.append([state, head, scanned, write, direction, target])
                tape[head] = write
                head += 1 if direction == 'R' else -1
                state = target
            require(steps == expected['steps'], 'Dispatch trace changed')
            require(state == expected['final_state'] and head == expected['final_head'], 'Dispatch endpoint changed')
            require(tape == {-1:preceding, 0:bit}, 'Dispatch did not restore both cells')
            endpoints.append((state, head))
            traces_checked += 1
        require(len(set(endpoints)) == 2, 'Recorded history-sensitive entry is no longer distinguished')
    require(main_rows[166, 1] == [1, 'R', 179], 'copyH correction no longer matches literal rows')
    print(json.dumps({'ok':True, 'input_tables':len(audit['input_tables']),
                      'pair_checks':pairs_checked, 'dispatch_traces':traces_checked,
                      'source_bindings':len(audit['source_dictionary']['bindings']),
                      'scope':'Literal macro identities and recorded finite dispatch facts; no search or arithmetic-calibration claim.'}, indent=2))


if __name__ == '__main__':
    main()
