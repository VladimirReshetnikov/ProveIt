#!/usr/bin/env python3
"""Check an inert overlay and lexical imports; never materialize modules or run Lean."""
from pathlib import Path
import hashlib,json,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):
    raise SystemExit('Run with python3 -I -S -B')
P=Path(__file__).resolve().parent
D=P.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
def pinned(path, digest):
    data=path.read_bytes()
    assert sha(data)==digest,(str(path),sha(data))
    return data
invpath=D/'research/ordinary14-natural81-endpoint-import-inventory/inventory.json'
slimpath=D/'research/ordinary14-root74-slim-overlay/inventory.json'
inv=json.loads(pinned(invpath,'bfb90445976aed586a849295ddd5afa5c706b7da7c8b6519bb2bd022491e5f40'))
slim=json.loads(pinned(slimpath,'b3317a1aa674fd67708aef94685af953126fcd1f30ead3bd43a9afb95467583e'))
old={r['module']:r for r in inv['drafts_topological']}
prev={r['module']:r for r in slim['drafts_topological']}
assert len(old)==173 and len(prev)==159
shared=set(old)&set(prev); extra=set(old)-set(prev)
assert len(shared)==158 and len(extra)==15 and set(prev)-set(old)=={'Root74Endpoint'}
assert extra==set(inv['slim_overlay_comparison']['endpoint_drafts_not_in_overlay'])
fixdir=D/'research/ordinary14-natural-predecessor-order-patch'
patches={'Natural81JShift':('f8e6436236c850e013ea9b9f9bbfe2ce48c45625a1d58ac1865e0413d96a5ca6','697dcee2a09998b978870b34dd0c34dbe3e86051a74808f79d61ea9ea86ad198',b'simpa [w] using hj',b'simpa [w, add_comm] using hj'),
 'Predecessors82':('9b17307ba0245cf02d3f944510daab2560f34b1ba31f2b93323c279bf12d0d3e','08ae139bb040b077bd8459ad879b8e229dcfdcdaabcc836c9ce0b72c1ecfe314',b'  exact \xe2\x9f\xa8f, r, y, hf, hr, hy\xe2\x9f\xa9',b'  exact \xe2\x9f\xa8f, r, y, by simpa [add_comm] using hf, by simpa [add_comm] using hr,\n    by simpa [add_comm] using hy\xe2\x9f\xa9')}
assert set(patches)<=extra
assert all(p.is_file() and not p.is_symlink() and p.name.endswith('.lean.src') for p in (P/'source').iterdir())
files={p.name[:-9]:p for p in (P/'source').glob('*.lean.src')}
assert set(files)==set(old),(sorted(set(old)-set(files)),sorted(set(files)-set(old)))
assert all(p.is_file() and not p.is_symlink() for p in files.values())
old_import=b'import DiophantineConsistency.Compact44.C44Short15Facts'
new_import=b'import CompactPortBoundsSlim'
old_ref=b'C44Short15Facts.port_bounds';new_ref=b'CompactPortBoundsSlimDraft.port_bounds'
def imports(data):
    # All endpoint draft snapshots use simple one-line initial import headers.
    result=[]
    for line in data.decode().splitlines():
        if not line.strip():continue
        m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*',line)
        if not m:break
        result.extend(m.group(1).split())
    return result
rows={};changed=[];direct=set()
for n,row in old.items():
    original=pinned(D/row['path'],row['sha256'])
    actual=files[n].read_bytes()
    if n in shared:
        x=prev[n]
        assert x['source_sha256']==row['sha256'],n
        expected=pinned(D/'research/ordinary14-root74-slim-overlay'/x['path'],x['overlay_sha256'])
        assert expected==original.replace(old_import,new_import).replace(old_ref,new_ref),n
        kind='root74-slim-snapshot'
    elif n in patches:
        original_hash,alternative_hash,before,after=patches[n]
        assert row['sha256']==original_hash and original.count(before)==1,n
        expected=pinned(fixdir/(n+'.lean.src'),alternative_hash)
        assert expected==original.replace(before,after),n
        kind='predecessor-order-alternative'
    else:
        expected=original;kind='new-endpoint-draft'
    assert actual==expected,n
    imps=imports(actual);bare=[x for x in imps if '.' not in x];qual=[x for x in imps if '.' in x]
    assert all('.' not in x for x in bare)
    # The witness-order edits must not change module imports; the prior overlay's
    # saved headers have already recorded its deliberate slim import edits.
    if n in shared: assert bare==prev[n]['bare_imports'] and qual==prev[n]['qualified_imports'],n
    else: assert bare==row['bare_imports'] and qual==row['qualified_imports'],n
    if original!=actual:
        changed.append({'module':n,'kind':kind,'original_sha256':row['sha256'],'overlay_sha256':sha(actual),'import_replacements':original.count(old_import),'reference_replacements':original.count(old_ref)})
    direct.update(qual)
    rows[n]={'module':n,'kind':kind,'original_path':row['path'],'original_sha256':row['sha256'],'overlay_path':'source/'+n+'.lean.src','overlay_sha256':sha(actual),'bare_imports':bare,'qualified_imports':qual}
expected={'CompactEquivalence':(1,1),'Compact78To85':(0,1),'Compact78To86':(0,1),'CompactEquivalence8687':(1,1),'CompactEquivalence8788':(1,1),'Quotient88PositiveBridge':(1,1)}
assert {x['module']:(x['import_replacements'],x['reference_replacements']) for x in changed if x['kind']=='root74-slim-snapshot'}==expected
assert {x['module'] for x in changed if x['kind']=='predecessor-order-alternative'}==set(patches)
order=[];visited=set();active=set()
def visit(n):
    assert n in rows,('unresolved bare import',n)
    if n in visited:return
    assert n not in active,('cycle',n)
    active.add(n)
    for dep in rows[n]['bare_imports']:visit(dep)
    active.remove(n);visited.add(n);order.append(n)
visit('Natural81Endpoint')
assert visited==set(rows),('unreachable snapshots',sorted(set(rows)-visited))
qualified=[]
for n in sorted(direct):
    p=D/'Lean'/('/'.join(n.split('.'))+'.lean')
    assert p.is_file(),('missing directly named source',n)
    qualified.append({'module':n,'path':str(p.relative_to(D)),'sha256':sha(p.read_bytes())})
original_qualified={x['module']:x for x in inv['qualified_direct_sources']}
current_qualified={x['module']:x for x in qualified}
assert set(original_qualified)-set(current_qualified)=={'DiophantineConsistency.Compact44.C44Short15Facts'}
assert set(current_qualified)<=set(original_qualified)
assert all(original_qualified[n]==current_qualified[n] for n in current_qualified)
prevdirect=set(slim['direct_qualified'])
assert 'DiophantineConsistency.Compact44.C44Short15Facts' not in direct
output={'scope':'inert draft snapshots and simple initial-header graph only; no Lean/provider/axiom/physical binding claim',
 'natural81_inventory_sha256':sha(invpath.read_bytes()),'root74_slim_inventory_sha256':sha(slimpath.read_bytes()),
 'root':'Natural81Endpoint','draft_count':len(order),'shared_root74_slim':len(shared),'extra_endpoint_modules':sorted(extra),
 'omitted_root74_module':sorted(set(prev)-set(old)), 'order': [rows[n] for n in order],
 'changed_snapshots':sorted(changed,key=lambda x:x['module']),
 'qualified_direct_count':len(qualified),'qualified_direct_sources':qualified,
 'additional_direct_qualified_vs_root74_slim':sorted(direct-prevdirect),
 'omitted_direct_qualified_vs_root74_slim':sorted(prevdirect-direct)}
print(json.dumps(output,sort_keys=True,indent=2))
