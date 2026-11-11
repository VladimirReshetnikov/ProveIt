from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parents[2];orig=root/'Lean/DiophantineConsistency/WangTiles942Core.lean';d=root/'research/current14-wang942core-staged-draft'
pins={orig:'27eae9953d2938690af39d5b52b30520bc99d8e013181962c38b7810c82e5304',d/'WangTiles942CoreA.lean':'b2813e0e8a82ebb2fdded05cc36bec61818a68119b189072358e8b24f75b82d1',d/'WangTiles942CoreB.lean':'2625e58be3ad19941111161f1bae827e8d58fa7480e0bf9fa64b462ca88cd13c',d/'WangTiles942Core.lean':'10b17e29974c474345eb6d8ac574f8b24324eca5955a12170841164f8663eec5'}
for p,h in pins.items():assert hashlib.sha256(p.read_bytes()).hexdigest()==h,str(p)
o=orig.read_text();a=(d/'WangTiles942CoreA.lean').read_text();b=(d/'WangTiles942CoreB.lean').read_text();c=(d/'WangTiles942Core.lean').read_text();end='end DiophantineConsistency.WangTiles942\n';s1=o.index('def ColorsBounded');s2=o.index('theorem all_rows_tight');assert a==o[:s1]+end
opts='namespace DiophantineConsistency.WangTiles942\n\nset_option Elab.async false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 20000000\nset_option exponentiation.threshold 1024\n\n'
assert b=='import DiophantineConsistency.WangTiles942CoreA\n\n'+opts+o[s1:s2]+end
assert c=='import DiophantineConsistency.WangTiles942CoreB\n\n'+opts+o[s2:]
assert re.findall(r'^import (\S+)',a,re.M)==['DiophantineConsistency.WangTiles942TableData','DiophantineConsistency.WangTiles942Data','Mathlib.Tactic'];assert len(re.findall(r'^instance\b',o,re.M))==2 and len(re.findall(r'^instance\b',b,re.M))==2
assert not re.search(r'^(?:private|protected|local|scoped|section|variable|open|attribute)\b',o,re.M)
print(json.dumps({'status':'PASS_SOURCE_ONLY','segments':3,'original_declaration_bytes':'unchanged in original order','instances':2,'lean_run':False,'scope':'Module staging; import elaboration and resources untested'},indent=2))
