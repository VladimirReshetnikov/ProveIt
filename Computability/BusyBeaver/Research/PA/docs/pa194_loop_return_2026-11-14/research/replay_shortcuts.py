#!/usr/bin/env python3
"""Reproduce the three bounded closure/shortcut searches in the report."""
from pathlib import Path
import json,sys,hashlib
from local_shortcuts import parse,closure,shortcuts
ROOT=Path(__file__).resolve().parents[1]
out=Path(sys.argv[1]) if len(sys.argv)>1 else ROOT/'research/replayed_shortcuts'
out.mkdir(parents=True,exist_ok=True)
a=parse(ROOT/'inputs/PA194AX11GH/machine.native.tm');a.update({(26,1):(1,1,91),(101,0):(0,1,17)})
b=parse(ROOT/'machines/PA194LCG/loop_parent.native.tm');b.update({(26,1):(1,1,91),(101,0):(0,1,17)})
c=parse(ROOT/'machines/PA194LCG/machine.native.tm')
for name,rows,count,hits in [('AX11GHF',a,912456,0),('LC_AX11GHF',b,915400,1),('PA194LCG',c,913352,0)]:
 seen=closure(rows,74,7);found=shortcuts(rows,seen,7,31)
 assert sum(map(len,seen.values()))==count and len(found)==hits and all(seen.values())
 receipt={'name':name,'radius':7,'old_step_bound':31,'abstract_configurations':count,'empty_states':[],'shortcuts':found}
 (out/(name+'.json')).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
