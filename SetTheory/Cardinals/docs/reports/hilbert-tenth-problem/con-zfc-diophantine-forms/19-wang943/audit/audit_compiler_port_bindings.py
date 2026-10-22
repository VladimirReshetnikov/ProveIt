"""Read-only structural interface audit for newly authored circuit JSONs.
No circuit builder or upstream program is imported or executed.
"""
from pathlib import Path
from hashlib import sha256
import json
ROOT=Path(__file__).resolve().parents[1]
results=[]
for directory in ('roots','arithmetic','integers'):
    for path in sorted((ROOT/directory).glob('*.json')):
        record=json.loads(path.read_text())
        if not isinstance(record,dict) or not isinstance(record.get('source'),list):continue
        source=record['source']
        fixed=set(record.get('fixed_numerals',[]))
        if not fixed:continue
        assert fixed in ({'beta','K0','MC','MF'},{'Bm1','Kconstant','MC','MF'}),path
        beta='beta' if 'beta' in fixed else 'Bm1'
        K='K0' if 'K0' in fixed else 'Kconstant'
        witnesses=set(record['witnesses'])
        definitions={}
        available=fixed|witnesses
        for name,operation,left,right in source:
            assert name not in available and operation in ('+','-','*'),(path,name)
            for operand in (left,right):assert isinstance(operand,int) or operand in available,(path,operand)
            definitions[name]=(operation,left,right);available.add(name)
        outputs=[record['output']] if 'output' in record else [x for pair in record.get('comparisons',[]) for x in pair if isinstance(x,str)]
        assert outputs,path
        live=set(); todo=outputs[:]
        while todo:
            name=todo.pop()
            if name in live or not isinstance(name,str):continue
            live.add(name)
            if name in definitions:todo.extend(definitions[name][1:])
        assert fixed<=live,path
        assert set(definitions)<=live,path
        # Verify the literal familiar four-port sites, rather than metadata claims.
        rep=[name for name,(op,a,b) in definitions.items() if op=='*' and beta in (a,b)]
        assert len(rep)==1
        q=[name for name,(op,a,b) in definitions.items() if op=='+' and {a,b}=={rep[0],1}]
        assert len(q)==1
        qMF=[name for name,(op,a,b) in definitions.items() if op=='*' and {a,b}=={q[0],'MF'}]
        assert len(qMF)==1
        mask=[name for name,(op,a,b) in definitions.items() if op=='+' and {a,b}=={'MC',qMF[0]}]
        assert len(mask)==1
        transport=[name for name,(op,a,b) in definitions.items() if op=='+' and K in (a,b) and 'w' in (a,b)]
        assert len(transport)==1
        results.append(dict(file=str(path.relative_to(ROOT)),source_sha256=sha256(json.dumps(source,separators=(',',':')).encode()).hexdigest(),
            all_four_ports_live=True,all_gates_live=True,port_roles_verified=True,
            aliases={beta:'beta',K:'K','MC':'MC','MF':'MF_source'},
            binding_metadata=record.get('coefficient_binding')))
receipt=dict(status='PASS',scope='Structural four-port compatibility only; separate arithmetic proofs remain required',circuits_checked=len(results),circuits=results,
    recommended_backend='../compiler/WANG943_COMPACT_LAYOUT.md',source_mask_warning='MF always means MF_source, never MF_native')
(ROOT/'audit/COMPILER_PORT_BINDINGS_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':'PASS','circuits_checked':len(results),'files':[r['file'] for r in results]},indent=2))
