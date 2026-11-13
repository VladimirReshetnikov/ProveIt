from pathlib import Path
import contextlib,copy,hashlib,io,json,runpy,tempfile
root=Path(__file__).resolve().parents[2];h=root/'research/trace75-bfs-decimal-display';script=h/'check_lean_graph.py';receipt=h/'observations/lean-graph.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(script)=='857fafd44b6c32aaab37ff8418fc54f4e123338445ce78a8158784c11ad3d6f6' and sha(receipt)=='3cde4a71ee34e090f60395f1a92740a565b0aff9fc3f4eef8c18f763ed71d1f0'
ns=runpy.run_path(str(script));main=ns['main'];g=main.__globals__;out=io.StringIO()
with contextlib.redirect_stdout(out):main()
assert json.loads(out.getvalue())==json.loads(receipt.read_text())
original=json.loads(g['GRAPH'].read_text());lean=g['LEAN'].read_text()
with tempfile.TemporaryDirectory(prefix='trace75-structural-audit-') as tmp:
 tmp=Path(tmp); graph=tmp/'graph.json';lpath=tmp/'lean.lean';lpath.write_text(lean)
 cases=[]
 x=copy.deepcopy(original);x['source'][-1][1]='-';cases.append(('final operation changed',x,lean))
 x=copy.deepcopy(original);x['source'][0][2]='UNKNOWN';cases.append(('unknown operand',x,lean))
 x=copy.deepcopy(original);x['source'][1][0]=x['source'][0][0];cases.append(('duplicate register',x,lean))
 cases.append(('unsupported lean division',original,lean.replace('let h := p 0 * J','let h := p 0 / J',1)))
 cases.append(('lean output changed',original,lean.replace('(r.M * r.M * r.Gn - r.Z * r.Z)','(r.M * r.M * r.Gn + r.Z * r.Z)',1)))
 for label,data,source in cases:
  assert label not in ('unsupported lean division','lean output changed') or source!=lean,label
  graph.write_text(json.dumps(data));lpath.write_text(source);g['GRAPH']=graph;g['LEAN']=lpath;g['PINS']={graph:sha(graph),lpath:sha(lpath)}
  try:
   with contextlib.redirect_stdout(io.StringIO()):main()
  except (RuntimeError,ValueError,SyntaxError,KeyError):print(label,'rejected')
  else:raise AssertionError(label+' accepted')
print('PASS original result reproduced and five actual-parser mutations rejected; no Lean replay')
