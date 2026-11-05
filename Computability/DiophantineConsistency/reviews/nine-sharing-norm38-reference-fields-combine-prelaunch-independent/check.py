import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-reference-fields-combine-check';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();run=q/'run.py';man=q/'source-manifest.json';survey=q/'field_preflight.py'
assert sha(man)=='6884049f228492c7e63bf26c22295249e595fb7ee719748e6cad38e13ba9d6bc' and sha(survey)=='4874dede3ed41c8502933a6b2b9a4303557ea203ef13a58a52f18888235e32f4' and sha(run)=='b6b077ec97b366014b7740e250fa5caeed49cb713cce67961f50350c9a694830'
rows=json.loads(man.read_text())['rows'];assert [r['module'] for r in rows]==['DiophantineConsistency.Norm38ReferenceFieldsAll','DiophantineConsistency.Norm38StaticCarrierConditional'];pins=['981f54ae6a0fcebff2445ddc7caee9aa2e36a1102f80ea9592d415b830c738cc','e12205b7f006824130a8c43189f99aa5de8f18a3ff1aadb2db3ba903e8779fa4'];texts=[]
for i,r in enumerate(rows):
 p=q/'src/DiophantineConsistency'/(r['module'].split('.')[-1]+'.lean');assert sha(p)==r['source_sha256']==pins[i] and D.parents[1]/r['source']==p;t=p.read_text();texts.append(t);assert re.findall(r'^import ([A-Za-z0-9_.]+)$',t,re.M)==r['imports'] and 'sorry' not in t and t.count('#print axioms')==1
assert rows[0]['imports']==['DiophantineConsistency.'+n for n in ('Norm38ReferenceFields01','Norm38ReferenceW','Norm38ReferenceDelta','Norm38ReferenceUFactored','Norm38ReferenceZFactored')] and rows[1]['imports']==[rows[0]['module']]
for idx,field in [(61,'P'),(44,'Q'),(78,'U'),(66,'W'),(80,'Z'),(36,'delta')]:
 assert f'reference p x {idx} = d.{field}' in texts[0] and f'pairValue ι (v {idx}) = ref {idx}' in texts[1]
assert 'NormAssignment38.fiveNorms ι ports w' in texts[1] and 'Carrier65.value (fun j => ι (ports j))' in texts[1] and '+ 1' in texts[1]
norm=(R/'nine-sharing-norm38-check-sequence/src/DiophantineConsistency/NormAssignment38.lean').read_text();part=norm[norm.index('def fiveNorms'):norm.index('-- Unresolved',norm.index('def fiveNorms'))]
for f in ['pairValue embed (v 61) = 1','pairValue embed (v 44) = 1','pairValue embed (v 78) = 1','pairValue embed (v 66) = 1','pairValue embed (v 80) = pairValue embed (v 36)']:assert f in part
carrier=(D/'Lean/DiophantineConsistency/Carrier65.lean').read_text();assert 'b.P * b.Q * b.U * b.W * b.Z - b.delta' in carrier
x=subprocess.run([sys.executable,'-I','-S','-B',str(survey)],capture_output=True,text=True,timeout=90);z=json.loads(x.stdout);assert x.returncode==0 and not x.stderr and z['status']=='PASS_FIVE_FIELD_PRODUCER_SURVEY' and z['producer_count']==5 and z['recorded_direct_guard_slots']==750
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=90);assert x.returncode==0 and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT' and not x.stderr,(x.stdout,x.stderr)
for name in ('nine-sharing-norm38-reference-fields01-terminal-independent','nine-sharing-norm38-reference-w-delta-terminal-independent','nine-sharing-norm38-reference-u-factored-terminal-independent','nine-sharing-norm38-reference-z-factored-terminal-independent'):
 p=D/'reviews'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),(name,x.stderr)
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','manifest_sha256':sha(man),'runner_sha256':sha(run),'field_producers':5,'recorded_producer_guard_slots':750,'scope':'Source only; stage two assumes all six terminal agreements and fiveNorms; no Lean or gate/reference bridge.'},indent=2,sort_keys=True))
