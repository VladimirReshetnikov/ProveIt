import ast,hashlib,tempfile
from pathlib import Path
script=Path('Computability/DiophantineConsistency/research/ha87_full_source_rebuild_transitive.py')
tree=ast.parse(script.read_text());fn=next(n for n in ast.walk(tree) if isinstance(n,ast.FunctionDef) and n.name=='transitive_environment');ns={};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(script),'exec'),ns)
root=Path(tempfile.mkdtemp(prefix='ha87-transitive-guard-test-'));origin=root/'origin';lib=root/'current';origin.mkdir();lib.mkdir()
def digest(data):return hashlib.sha256(data).hexdigest()
def put(parent,name,data):
 p=parent/'lib'/(name+'.olean') if parent==origin else parent/(name+'.olean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);return digest(data)
b=put(origin,'B',b'b');c=put(origin,'C',b'old-c');put(lib,'B',b'b');put(lib,'C',b'old-c')
edges={'A':['B'],'B':['C'],'C':['E']};sources={'A':'a','B':'b','C':'c'};eh={'E':'external'};ec={'E.olean.server':{'sha256':'companion'}}
st={'graph':{'edges':edges.copy(),'sources':sources.copy(),'external_hashes':eh.copy(),'external_companions':ec.copy()},'records':[{'module':'B','verified':True,'object_sha256':b},{'module':'C','verified':True,'object_sha256':c}]}
ns.update(edges=edges,sources=sources,lib=lib,external_hashes=eh,external_companions=ec,anchored_hash=lambda p:digest(Path(p).read_bytes()))
f=ns['transitive_environment'];fp,why=f(origin,st,'A');assert why is None and fp['B']['sha256']==b and fp['C']['sha256']==c and fp['E']['companions']=={'E.olean.server':'companion'}
put(lib,'C',b'new-c');fp,why=f(origin,st,'A');assert fp is None and why=='transitive project object changed: C'
put(lib,'C',b'old-c');ec['E.olean.server']={'sha256':'different'};fp,why=f(origin,st,'A');assert fp is None and why=='external companion changed: E.olean.server'
ec['E.olean.server']={'sha256':'companion'};edges['C']=['F'];fp,why=f(origin,st,'A');assert fp is None and why=='declared imports changed: C'
edges['C']=['E'];put(origin,'C',b'tampered')
try:f(origin,st,'A')
except RuntimeError as e:assert str(e)=='original transitive object changed: C'
else:raise AssertionError('tampered origin accepted')
print('PASS: identical closure accepted; changed transitive object, external companion, import edges and tampered origin rejected')
