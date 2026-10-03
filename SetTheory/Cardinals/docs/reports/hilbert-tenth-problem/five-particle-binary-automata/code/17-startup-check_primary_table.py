#!/usr/bin/env python3
"""Primary Table16 transcription checked against pinned TM rows."""
from verify_pins import verify_inputs
verify_inputs()
import json,hashlib
from pathlib import Path
R=Path(__file__).resolve().parent
# Independently read by columns from rendered printed121, c-row then b-row.
c=['cRB','bRC','cLG','cLF','bRA','bLD','cLH','bLI','cRA','bLK','cRL','cRM','cLB','cLC','cRN']
b=['bRA','bRA','cLE','bLE','bLD','bLD','bLG','bLG','bLJ',None,'bRN','bRL','bRL','cRO','bRN']
tm=json.loads((R/'dependency/tm_table.json').read_text())
for i in range(15):
    for bit,t in enumerate((c[i],b[i])):
        q=chr(65+i)+str(bit);expected=None if t is None else [0 if t[0]=='c' else 1,t[1],t[2]]
        if tm[q]!=expected:raise RuntimeError((q,tm[q],expected))
out=dict(status='passed',entries=30,primary_url='https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf',historically_inspected_printed_pages=[112,121], replay_scope='Compare 30 bundled transcription cells with pinned TM table; no fresh paper/PDF inspection',table=16,initial_state='u1=A',initial_head_symbol='rightmost G=bc symbol is c=0',undefined_entry='u10,b = J1',compact_source_sha256=hashlib.sha256((R/'dependency/UniversalTM15x2.tm.txt').read_bytes()).hexdigest())
(R/'primary-table-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
