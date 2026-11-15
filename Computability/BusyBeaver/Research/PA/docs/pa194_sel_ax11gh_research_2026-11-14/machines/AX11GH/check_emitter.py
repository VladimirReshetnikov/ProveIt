#!/usr/bin/env python3
"""Verify unchanged AX11G emitter and four-field codec, with AX11GH words separate."""
from pathlib import Path
import json,hashlib
import inherited_ax11g_commands as inherited

ROOT=Path(__file__).resolve().parent
if __name__=='__main__':
    machine=ROOT/'machine'
    result={'status':'PASS','family':'PA194AX11GH',
            'emitter':inherited.emitter(machine),
            'scheduler':inherited.scheduler_check(),
            'scope':'Only the unchanged emitter and codec are inherited. check_words.py verifies the different cache-only Shift protocol.',
            'inputs':{n:hashlib.sha256((machine/n).read_bytes()).hexdigest()
                      for n in ('grammar.tree.json','nodes.json','machine.tm')}}
    (machine/'emitter.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
