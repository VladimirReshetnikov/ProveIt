#!/usr/bin/env python3
"""Reproducible fused, auxiliary-majorant positive circuits; stdlib only."""
from pathlib import Path
from collections import Counter
from hashlib import sha256
import json,sys
H=Path(__file__).resolve().parent
p=json.loads((H/'source/prior96_equation.json').read_text())
for kind,count,degree in [('uncentered',94,262),('upper',96,258),('sharp',97,254)]:
    rows=[]
    for n,op,a,b in p['source']:
        if n in {'HI','L'}:continue
        if n=='LB':a='cTR'
        if n=='nVL' and kind!='uncentered':a='nVCg'
        rows.append([n,op,a,b])
        if n=='DtauI' and kind!='uncentered':
            if kind=='sharp':rows.append(['Afull','+','Am1',1])
            rows.append(['Cg','*','Afull' if kind=='sharp' else 'Ap1','DtauI'])
        if n=='nV' and kind!='uncentered':rows.append(['nVCg','+','nV','Cg'])
    deg={n:1 for n in p['witnesses']}|{n:0 for n in p['fixed_numerals']}
    for n,op,a,b in rows:
        da=deg[a] if isinstance(a,str) else 0;db=deg[b] if isinstance(b,str) else 0
        deg[n]=da+db if op=='*' else max(da,db)
    obj={k:p[k] for k in ['domain','witnesses','fixed_numerals','coefficient_binding']}
    obj.update(name='fused_auxiliary_majorant_'+kind,operations=len(rows),operation_breakdown=dict(Counter(r[1] for r in rows)),exact_degree=degree,syntactic_degree=deg['N'],output='N',source=rows,register_degrees=deg,parent_sha256=sha256((H/'source/prior96_equation.json').read_bytes()).hexdigest(),proof_status='Ordinary unbounded arithmetic reduction relative to retained coherent source calibration; not a newly machine-checked endpoint.')
    if len(rows)!=count:raise ValueError((kind,len(rows)))
    text=json.dumps(obj,indent=2)+'\n';path=H/(kind+'.json')
    if '--check' in sys.argv:
        if path.read_text()!=text:raise ValueError(str(path)+' differs from rebuild')
    else:path.write_text(text)
    print(kind,count,degree,obj['operation_breakdown'])
# The ordinary multiplicative chart reuses exactly the same coherent port tuple.
for kind,count,degree in [('uncentered',89,288),('upper',91,283),('sharp',92,278)]:
    direct=json.loads((H/(kind+'.json')).read_text());rows=[]
    for name,op,a,b in direct['source']:
        if name in {'qK0','qK0X','qK0XC','qF','qbJ','lowX','inner'}:continue
        if name=='B':
            rows.extend([['K0w','+','K0','w'],['K0wC','*','K0w','C'],['Bt','-','K0wC','F']]);continue
        if name=='X':op,a,b='*','q','w'
        if name=='P1':b='bJ'
        if name=='lowY':a='bJ'
        if name=='inner0':name='inner'
        a='Bt' if a=='B' else a;b='Bt' if b=='B' else b
        rows.append([name,op,a,b])
    obj={k:direct[k] for k in ['domain','fixed_numerals','coefficient_binding','proof_status']}
    obj['witnesses']=['w' if n=='x' else n for n in direct['witnesses']]
    deg={n:1 for n in obj['witnesses']}|{n:0 for n in obj['fixed_numerals']}
    for name,op,a,b in rows:
        da=deg[a] if isinstance(a,str) else 0;db=deg[b] if isinstance(b,str) else 0
        deg[name]=da+db if op=='*' else max(da,db)
    obj.update(name='ordinary_fused_auxiliary_majorant_'+kind,operations=len(rows),operation_breakdown=dict(Counter(r[1] for r in rows)),exact_degree=degree,syntactic_degree=deg['N'],output='N',source=rows,register_degrees=deg,parent_sha256=sha256((H/(kind+'.json')).read_bytes()).hexdigest())
    if len(rows)!=count:raise ValueError((kind,len(rows)))
    text=json.dumps(obj,indent=2)+'\n';path=H/('ordinary_'+kind+'.json')
    if '--check' in sys.argv:
        if path.read_text()!=text:raise ValueError(str(path)+' differs from rebuild')
    else:path.write_text(text)
    print('ordinary_'+kind,count,degree,obj['operation_breakdown'])
