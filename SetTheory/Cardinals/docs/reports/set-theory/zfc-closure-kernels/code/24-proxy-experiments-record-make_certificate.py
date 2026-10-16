#!/usr/bin/env python3
"""Generate shortest output/finality distinction words for ZFC253.

This establishes only the absence of a strict literal one-step state quotient.
It does not establish minimality among behaviorally equivalent Turing machines.
"""
from collections import defaultdict, deque, Counter
from pathlib import Path
import hashlib, json

ROOT = Path(__file__).resolve().parent
EXPECTED = '84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95'

def parse(path):
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != EXPECTED:
        raise ValueError('machine hash mismatch')
    rows = {}
    for line in data.decode('ascii').splitlines():
        if not line or line.startswith('#'): continue
        q,b,w,d,r = line.split()
        key = int(q),int(b)
        if key in rows: raise ValueError('duplicate row')
        rows[key] = int(w),d,int(r)
    if set(rows) != {(q,b) for q in range(253) for b in range(2)}:
        raise ValueError('machine is not a complete 253-state binary table')
    return rows

def pair(a,b): return min(a,b),max(a,b)

def generate(rows,support):
    terminal = 253
    words = {pair(q,terminal):'' for q in range(terminal)}
    output_conflicts = {}
    reverse = defaultdict(list)
    for a in range(terminal):
        for b in range(a+1,terminal):
            for bit in (0,1):
                if (a,bit) not in support or (b,bit) not in support: continue
                wa,da,ra = rows[a,bit]; wb,db,rb = rows[b,bit]
                if (wa,da) != (wb,db):
                    output_conflicts.setdefault((a,b),str(bit))
                elif ra != rb:
                    reverse[pair(ra,rb)].append(((a,b),str(bit)))
    # The queue begins with all length-zero witnesses, then all length-one
    # output conflicts. Newly reached predecessors therefore have shortest
    # word length (ordinary breadth-first search).
    todo = deque(words)
    for key,word in sorted(output_conflicts.items()):
        words[key]=word; todo.append(key)
    while todo:
        key = todo.popleft()
        for predecessor,bit in reverse[key]:
            if predecessor not in words:
                words[predecessor] = bit+words[key]
                todo.append(predecessor)
    missing = [[a,b] for a in range(terminal) for b in range(a+1,terminal)
               if (a,b) not in words]
    return {'supported_rows':len(support),
            'unseparated_pairs':missing,
            'words':{f'{a},{b}':word for (a,b),word in sorted(words.items())},
            'word_length_histogram':dict(sorted(Counter(map(len,words.values())).items())),
            'maximum_word_length':max(map(len,words.values()))}

def main():
    rows=parse(ROOT/'zfc_253.tm')
    result={'source_commit':'0d544f2a2e3c18f12278441a74b7879f31cbe856',
            'machine_sha256':EXPECTED,
            'state_labels':'compact: working 0..252, terminal 253',
            'scope':'Exact one-step quotients preserving write, direction, and halting',
            'complete_table':generate(rows,set(rows)),
            'omit_initializer_row':generate(rows,set(rows)-{(0,0)})}
    (ROOT/'quotient_certificate.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    summary={name:{k:v for k,v in result[name].items() if k!='words'}
             for name in ('complete_table','omit_initializer_row')}
    (ROOT/'quotient_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__': main()
