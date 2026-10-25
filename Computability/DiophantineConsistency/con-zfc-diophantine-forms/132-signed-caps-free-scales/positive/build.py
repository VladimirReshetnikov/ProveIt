#!/usr/bin/env python3
"""Polynomial radical-centering circuits; all arithmetic gates count."""
from pathlib import Path
from collections import Counter
from hashlib import sha256
import json,sys
H=Path(__file__).resolve().parent
parent=json.loads((H/'prior/sharp.json').read_text())
for kind,count,degree in [('first',102,253),('second',104,252)]:
    rows=[]
    for n,op,a,b in parent['source']:
        if n=='I':
            rows.extend([['E0','*','i','c2'],['I','*',2,'E0']]);continue
        if n=='Cg':
            rows.append(['Cg0',op,a,b])
            rows.append(['pk','*','muY','k'])
            if kind=='first':rows.append(['Qapprox','*','pk','V0k'])
            else:rows.extend([['vminus','-','V0','muY2'],['vminusk','*','vminus','k'],['Qapprox','*','pk','vminusk']])
            rows.extend([['correction','*','E0','Qapprox'],['Cg','-','Cg0','correction']]);continue
        rows.append([n,op,a,b])
    obj={k:parent[k] for k in ['domain','witnesses','fixed_numerals','coefficient_binding']}
    deg={n:1 for n in obj['witnesses']}|{n:0 for n in obj['fixed_numerals']}
    for n,op,a,b in rows:
        da=deg[a] if isinstance(a,str) else 0;db=deg[b] if isinstance(b,str) else 0
        deg[n]=da+db if op=='*' else max(da,db)
    if len(rows)!=count:raise ValueError((kind,len(rows)))
    obj.update(name='polynomial_radical_center_'+kind,operations=len(rows),operation_breakdown=dict(Counter(r[1] for r in rows)),exact_degree=degree,syntactic_degree=deg['N'],output='N',source=rows,register_degrees=deg,parent_sha256=sha256((H/'prior/sharp.json').read_bytes()).hexdigest(),proof_status='Ordinary unbounded arithmetic reduction relative to the retained coherent source calibration; not a new machine-checked endpoint.')
    s=json.dumps(obj,indent=2)+'\n';path=H/(kind+'.json')
    if '--check' in sys.argv:
        if path.read_text()!=s:raise ValueError('Rebuild mismatch: '+str(path))
    else:path.write_text(s)
    print(kind,count,degree,obj['operation_breakdown'])
