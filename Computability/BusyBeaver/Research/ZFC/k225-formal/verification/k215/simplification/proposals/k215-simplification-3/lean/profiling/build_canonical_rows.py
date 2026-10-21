#!/usr/bin/env python3
"""Generate and check a canonical-site certificate; no kernel proof claim."""
import collections, contextlib, copy, io, json, runpy, sys
from pathlib import Path
if not __debug__: raise SystemExit('Do not run with -O/-OO: assertions are required.')
ROOT=Path(__file__).resolve().parent
with contextlib.redirect_stdout(io.StringIO()):
    m=runpy.run_path(str(ROOT/'verify_lean_canonical_cfg.py'))
A,B=m['A'],m['B'];site=m['site'];roots=m['roots'];inc,brk,cont=m['inc'],m['brk'],m['cont']
left=sorted(A['ti'],key=A['ti'].get);right=sorted(B['ti'],key=B['ti'].get)
assert len(left)==len(right)==1426
encode=lambda path:int('1'+''.join(map(str,path)),2)
decode=lambda n:tuple(int(b) for b in bin(n)[3:])
rows=[]
for i,((kind,reg),edges) in enumerate(A['block']):
    row={'kind':kind,'register':reg,'left':encode(left[i]),'right':encode(right[i])}
    if kind=='decnz':row.update(positive=edges[0][0],zero=edges[1][0])
    else:assert kind=='halt' and not edges
    rows.append(row)
cert={'format':'canonical-site-rows-v1-research','commit':m['out']['commit'],
 'source_sha256':m['out']['source_sha256'],'initial_row':A['start_block'][0],
 'rows':rows}
counts=collections.Counter()
def checked_site(root,path):
    counts['site_calls']+=1
    return site(root,path)
def segment(root,path):
    counts['segment_calls']+=1;increments=[]
    for fuel in range(1000,0,-1):
        counts['segment_sites']+=1
        (kind,reg),q=checked_site(root,path)
        if kind in ('decnz','halt'):return increments,path
        if kind=='inc':increments.append(reg);path=inc(q)
        elif kind=='brk':path=brk(q,reg)
        elif kind=='cont':path=cont(q,reg)
        else:raise AssertionError(kind)
    raise AssertionError('Segment fuel exhausted')
def match(row,a,b):
    edge=(row['kind'],row['register'])
    assert checked_site(roots[0],a)==(edge,decode(row['left']))
    assert checked_site(roots[1],b)==(edge,decode(row['right']))
def branch(rows,a,b,j):
    counts['branch_checks']+=1
    la,pa=segment(roots[0],a);lb,pb=segment(roots[1],b)
    assert collections.Counter(la)==collections.Counter(lb)
    assert 0<=j<len(rows)
    match(rows[j],pa,pb)
def check(cert):
    rs=cert['rows'];assert len(rs)==1426
    branch(rs,(),(),cert['initial_row'])
    for row in rs:
        a,b=decode(row['left']),decode(row['right'])
        # Explicit row self-check is redundant for semantic soundness but
        # makes malformed or unreachable rows fail rather than go unnoticed.
        match(row,a,b)
        if row['kind']=='halt':continue
        assert row['kind']=='decnz'
        branch(rs,inc(a),inc(b),row['positive'])
        branch(rs,brk(a,1),brk(b,1),row['zero'])
check(cert);good_counts=dict(counts)
negative=[]
for name,mutate in [
 ('wrong_initial',lambda c:c.update(initial_row=(c['initial_row']+1)%1426)),
 ('wrong_left_path',lambda c:c['rows'][0].update(left=c['rows'][0]['left']+1)),
 ('wrong_positive_target',lambda c:c['rows'][0].update(positive=(c['rows'][0]['positive']+1)%1426)),
 ('wrong_test_register',lambda c:c['rows'][0].update(register=(c['rows'][0]['register']+1)%9))]:
    bad=copy.deepcopy(cert);mutate(bad)
    try:check(bad)
    except AssertionError:negative.append(name)
    else:raise AssertionError('Bad certificate accepted: '+name)
encoded=json.dumps(cert,separators=(',',':'))+'\n'
(ROOT/'canonical_rows.json').write_text(encoded)
out={'status':'PASS_PYTHON_CANONICAL_CERTIFICATE_NOT_LEAN',
 'rows':len(rows),'bytes':len(encoded.encode()),'counters':good_counts,
 'negative_mutations_rejected':negative,'semantic_adapter':'CanonicalRows.uncompiled.lean',
 'limitations':['Python checker is not a trusted proof or a Lean implementation.',
   'The new finite Lean checker still needs its soundness theorem and compilation.']}
(ROOT/'canonical_rows_result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
