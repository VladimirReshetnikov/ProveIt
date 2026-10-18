#!/usr/bin/env python3
"""Independent static metadata review only; imports/executes no supplied program."""
from pathlib import Path
import ast, hashlib, json, re

BASE=Path('/tmp/zfc243-combined-lean')
OUT=Path('/tmp/zfc243-calibration-plan')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(Path(p)),sha256=sha(p))
imports=lambda p:re.findall(r'^import\s+(\S+)\s*$',Path(p).read_text(),re.M)
tracked={}
def pin(p,h):
    p=Path(p).resolve();assert p.is_file() and sha(p)==h,(p,h)
    assert str(p) not in tracked or tracked[str(p)]==h
    tracked[str(p)]=h
def literals(p):
    return {n.targets[0].id:ast.literal_eval(n.value) for n in ast.parse(p.read_text()).body
            if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name)
            and n.targets[0].id in {'MODULE','PREFIX','PROBES','SOURCE_SHA','AUDIT_SHA','BOUNDARY_SHA','PARENT_SHA'}}
result=[]
for label,expected,counts,pc in [('invariant','754da77c20e690d71cf7f5814739a5a0bdda8aba76e070d82a83bc746c357c94',(5,8),2),('blocks','ce10f6ea5df6ca3e924c29e396ebc7c2ec6c1c0b657b32bb8ce777b6a15b06a7',(14,14),3)]:
    d=BASE/label;g=d/'check.py';pin(g,expected);v=literals(g)
    b=json.loads((d/'boundary.json').read_text());pin(d/'boundary.json',v['BOUNDARY_SHA'])
    epath=Path(b['parent']['path']);pin(epath,v['PARENT_SHA']);e=json.loads(epath.read_text())
    assert e['status']=='PASS' and e['before']==e['after']
    for q in b['static_inputs']:pin(q['path'],q['sha256'])
    S=d/(v['MODULE'].split('.')[-1]+'.lean');A=d/'Audit.lean'
    pin(S,v['SOURCE_SHA']);pin(A,v['AUDIT_SHA'])
    assert len(v['PROBES'])==counts[0]
    assert re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[v['PREFIX']+n for n in v['PROBES']]
    assert len(re.findall(r'^example\b',A.read_text(),re.M))==counts[1]
    pairs={q['module']:q for q in b['reused_modules']};assert len(pairs)==pc
    for q in pairs.values():
        for k in ('source','object'):pin(q[k],q[k+'_sha256'])
        if q['module']==e['fresh_modules'][0]['module']:
            f=e['fresh_modules'][0]
            assert q['source_sha256']==e['source']['sha256']==f['source_sha256']
            assert q['object']==f['path'] and q['object_sha256']==f['sha256']
            assert e['source_object_recorded_before_audit']
            assert all(e['source_pass_object'][k]==f[k] for k in ('module','path','sha256','source_sha256'))
            first=e['fresh_first_provider_before_audit'];assert first['sha256']==f['sha256'] and Path(first['path']).resolve()==Path(f['path']).resolve()
        else:
            assert q==next(p for p in e['reused_modules'] if p['module']==q['module'])
            first=next(p for p in e['actual_first_providers'] if p['module']==q['module'])
            assert first['sha256']==q['object_sha256'] and Path(first['actual_first']).resolve()==Path(q['object']).resolve()
    tools={q['module']:q for q in b['toolchain_providers']};seen=set();wanttools={'Init'}
    def visit(n):
        if n in ('Init','Lean.Elab.Tactic.Omega'):wanttools.add(n);return
        assert n in pairs,n
        if n in seen:return
        seen.add(n)
        for m in imports(pairs[n]['source']):visit(m)
    for n in imports(S):visit(n)
    assert seen==set(pairs) and wanttools==set(tools)
    assert b['toolchain_providers']==e['toolchain_providers'] and b['compiler']==e['compiler']
    pin(b['compiler']['path'],b['compiler']['sha256'])
    for q in tools.values():pin(q['object'],q['object_sha256'])
    for k in ('source','audit'):pin(e[k]['snapshot'],e[k]['sha256'])
    for c in e['commands']:
        assert c['exit_code']==0 and not c.get('timed_out') and not c.get('interrupted')
        pin(c['log'],c['log_sha256']);assert Path(c['log']).read_text()==c['output']
    txt=g.read_text();assert "obj.parent.mkdir(parents=True,exist_ok=True);run('source',ss,obj)" in txt
    assert "deadline=time.monotonic()+120" in txt and "'-j1','-M4096'" in txt
    assert 'subprocess.run' not in txt and 'check_output' not in txt
    result.append(dict(unit=label,guard=desc(g),source=desc(S),audit=desc(A),boundary=desc(d/'boundary.json'),actual_parent=desc(epath),project_modules=sorted(seen),tools=sorted(tools),probes=counts[0],callers=counts[1]))
for p,h in tracked.items():assert sha(p)==h
receipt=dict(status='SOURCE_AND_EXISTING_PARENT_BINDING_REVIEW_PASS',scope='Full guard and focused delta read plus own static hash/provider/import checks. No invariant/block guard, preparation, or compiler executed; no result claimed for those targets.',reviewer_role='Independent of these guards and ports; author of the two imported table sources and earlier execution template.',reviewer_source=desc(__file__),units=result,current_inputs=tracked,findings=[])
(OUT/'dependent-guards-source-review.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(desc(OUT/'dependent-guards-source-review.json')))
