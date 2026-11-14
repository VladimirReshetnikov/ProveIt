#!/usr/bin/env python3
"""Encode the fresh 68-reader/8-fold PA194 grammar for the unchanged search.

Runs from its own directory. S uses the packet's literal fixed controls;
C changes exactly the six independently justified cached-controller rows.
The emitted templates are postorder hash-consed syntax, with no parameter
renaming or change of the emitter word. The search itself expands inc pairs
into the inherited double/quadruple-increment macro controls.
"""
from pathlib import Path
import hashlib
import json

P = Path(__file__).resolve().parent
MACROS = {'node65':90, 'node55':98, 'node58':12, 'node70':166,
          'node49':19, 'node72':69, 'node75':213, 'node142':194,
          'node150':221, 'node60':99, 'node61':190}
EDITS = {(38,0):(0,1,11), (38,1):(1,1,122), (164,1):(1,1,130),
         (214,0):(0,1,312), (214,1):(1,1,20), (312,0):(0,1,188)}

def main():
    grammar = json.loads((P/'new194.grammar.json').read_text())
    raw = {}
    for line in (P/'new194.unfolded202.native.tm').read_text().splitlines():
        q,b,w,d,n = line.split()
        raw[int(q),int(b)] = (int(w), int(d=='R'), int(n))
    fixed = {(q,b):a for (q,b),a in raw.items() if q < 1300}
    controls = sorted({q for q,b in fixed})
    assert len(controls) == 134 and len(fixed) == 268
    assert len(raw) == 404
    nodes, cache = [], {}
    def emit(x):
        if isinstance(x,str) and x in grammar['rules']:
            x = grammar['rules'][x]
        if isinstance(x,str):
            key = (0,MACROS[x],-1,-1)
        elif x == ['leaf','inc',1]:
            key = (0,61,-1,-1)
        elif x == ['leaf','breakTo',1]:
            key = (0,-1,-1,-1)
        else:
            assert isinstance(x,list) and len(x)==2, x
            key = (1,emit(x[0]),emit(x[1]),0)
        if key not in cache:
            cache[key] = len(nodes)
            nodes.append(key)
        return cache[key]
    root = emit(grammar['root'])
    for tag, edits in [('S',{}),('C',EDITS)]:
        rows = fixed | edits
        lines = [str(len(controls))]
        for q in controls:
            lines.append(' '.join(map(str,(q,*rows[q,0],*rows[q,1]))))
        lines += ['1',f'0 {len(nodes)} {root}']
        lines += [' '.join(map(str,n)) for n in nodes]
        (P/f'start194alt{tag}.txt').write_text('\n'.join(lines)+'\n')
    receipt = {'fixed_controls':len(controls), 'raw_reader_controls':68,
               'syntax_dag_records':len(nodes), 'root_record':root,
               'C_fixed_row_edits':len(EDITS),
               'sha256':{f:hashlib.sha256((P/f).read_bytes()).hexdigest()
                         for f in ['new194.grammar.json', 'new194.unfolded202.native.tm',
                                   'new194.folds.json', 'start194altS.txt',
                                   'start194altC.txt', 'leaf_attrs.txt',
                                   'search193_occ.cpp', 'screen.cpp']}}
    (P/'input_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__ == '__main__':
    main()
