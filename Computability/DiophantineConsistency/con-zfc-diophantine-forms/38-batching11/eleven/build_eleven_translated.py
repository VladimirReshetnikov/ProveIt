#!/usr/bin/env python3
"""Optional lower-degree carrier translation; main construction is unchanged."""
import json
from collections import Counter
from pathlib import Path
from build_eleven import build, audit_live

HERE = Path(__file__).resolve().parent

def build_translated(kind='product'):
    packet = build(kind)
    additions = [
        ['tr_twoc', '*', 2, 'c'],
        ['tr_add', '+', 'ell', 'tr_twoc'],
        ['tr_argument', '-', 'tr_add', 'X'],
        ['tr_multiply', '*', 'M', 'tr_argument'],
        ['sigma', '-', 'tr_multiply', 'b'],
        ['t_translated', '+', 't', 'sigma'],
    ]
    found = False
    source = []
    for row in packet['source']:
        if row[1:] == ['*', 'E', 't']:
            source.extend(additions)
            source.append([row[0], '*', 'E', 't_translated'])
            found = True
        else:
            source.append(row)
    if not found: raise ValueError('main carrier gate changed')
    packet['source'] = source
    packet['name'] = 'absorbed_index_eleven_translated_' + kind
    packet['carrier_translation'] = 'old t = t + M*(ell+2*c-X)-b'
    packet['proof'] = 'OPTIONAL_TRANSLATION_PROOF.md'
    if kind == 'product': packet['exact_degree'] = 1140
    else: packet['residual_exact_degrees'] = [2, 1138]
    counts = Counter(row[1] for row in source)
    packet['ledger'] = {'operations': len(source), 'multiplications': counts['*'],
                        'additions_subtractions': counts['+'] + counts['-']}
    audit_live(packet)
    return packet

def main():
    folder = HERE/'generated'
    folder.mkdir(exist_ok=True)
    for kind in ('product', 'system', 'shifted_system'):
        packet = build_translated(kind)
        (folder/(packet['name']+'.json')).write_text(json.dumps(packet, indent=2)+'\n')
        print(packet['name'], packet['ledger'])

if __name__ == '__main__': main()
