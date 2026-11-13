from pathlib import Path
import hashlib, re, json
root = Path(__file__).resolve().parents[2]
draft = root/'research/current14-k215-wf-chunk-probe-draft'
original = root.parent/'BusyBeaver/Lean/BusyBeaver/ZFC/KSource215Data.lean'
rm = root.parent/'BusyBeaver/Lean/BusyBeaver/ZFC/RMEquiv.lean'
frozen = Path('/tmp/current14-coherent490-rebuild-20261110/src/BusyBeaver/ZFC/KSource215Data.lean')
base = Path('/tmp/current14-standard-fresh-build-20261104/lib/BusyBeaver/ZFC')
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
pins = {
 original:'23b670c2b6ffd08fa173bbbe54faaf8989aac9b410a41a3332dee3f5fcaa5554',
 frozen:'23b670c2b6ffd08fa173bbbe54faaf8989aac9b410a41a3332dee3f5fcaa5554',
 rm:'61f807d4327a1e39ad441e1e737f5affd9fd7004476e12bb378c9c6663dc909c',
 draft/'KSource215WfTables.lean':'c739b661b284358791f7b38259ea60d05ccc2ee74a206ba55ce9e103f8ab4c53',
 draft/'KSource215WfChunk00.lean':'095986b8cbfdad47f8740983db20e59ecb366098f343f35efeee64c6891b170e',
 base/'RMEquiv.olean':'51fd5571c94774f848e0d41c7c4c425bb15fa91bb690781482c585276821a3d9',
 base/'DagPerm.olean':'501b7380b3089a2026507fe41d7958afd163044bb0860e59d819dc107eda2b63',
}
for p,h in pins.items(): assert digest(p)==h, str(p)
a=original.read_text(); b=(draft/'KSource215WfTables.lean').read_text(); c=(draft/'KSource215WfChunk00.lean').read_text(); r=rm.read_text()
assert re.findall(r'^import (\S+)',b,re.M)==['BusyBeaver.ZFC.RMEquiv','BusyBeaver.ZFC.DagPerm']
assert re.findall(r'^import (\S+)',c,re.M)==['BusyBeaver.ZFC.KSource215WfTables']
for name in ('tH','tB','tC'):
 pattern=rf'def {name}\s*:\s*List Nat\s*:=\s*\[(.*?)\]'
 x=re.search(pattern,a,re.S); y=re.search(pattern,b,re.S)
 assert x and y and x.group(1)==y.group(1)
 assert len(re.findall(r'\d+',x.group(1)))==487
assert re.search(r'RMEquiv\.wfCheck\s+DagPerm\.dagPerm\s+487\s+\(fun n => tH\.getD n 0\)\s+\(fun n => tB\.getD n 0\)\s+\(fun n => tC\.getD n 0\)',a)
assert re.search(r"\(List\.range' 0 32\)\.all\s+\(RMEquiv\.nodeOkb DagPerm\.dagPerm 487\s+\(fun n => tH\.getD n 0\) \(fun n => tB\.getD n 0\) \(fun n => tC\.getD n 0\)\)",c)
assert 'decide +kernel' in c and c.count('theorem ')==1
node=r.split('def nodeOkb ',1)[1].split('\ndef wfCheck',1)[0]
assert node.count('edgeOkb nn')==2 and node.count('decide (')==6
assert '(List.range nn).all (nodeOkb p nn H B C)' in r
print(json.dumps({'status':'PASS_SOURCE_ONLY','tables_length':487,'checked_node_indices':'0..31','remaining_nodes':455,'node_clauses':8,'lean_executed':False},indent=2))
