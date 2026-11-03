from pathlib import Path
import hashlib,json,os,re
root=Path(__file__).resolve().parents[2];h=root/'research/trace75-bfs-syntax';a=h/'observations/attempt01';t=json.loads((a/'terminal.json').read_text());src=h/'TenPositiveTrace75Syntax.lean';canonical=root/'Lean/DiophantineConsistency/TenPositiveTrace75Syntax.lean';obj=Path(t['output'])
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'terminal.json')=='a337790dd0dc729ffba6cee5c20e6c926fd24a9b9c1acf101b47e4ae48a81b0b' and t['status']=='PASS' and t['exit']==0 and t['reason'] is None
assert sha(src)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))==t['source_sha256']=='46aacc7b43fc5e42095a36265e6ba34853b7aeae70f053b289553ed4dcb18068'
assert src.read_bytes()==canonical.read_bytes()+b'\n#print axioms DiophantineConsistency.TenPositiveTrace75.evalRing_expression\n'
assert sha(h/'run.py')==t['runner_sha256']=='d0bc3a6b30e82d5860d8bdfc35abb0025dfa7704e2a739504201283047c8948b'
assert obj.is_file() and not obj.is_symlink() and sha(obj)==t['output_sha256']=='8349c9a4d22b2bdd2b3cb475570430b1df30a8e7f4e5e8ede9f40fb13a361d68'
for n in ('stdout','stderr'):assert sha(a/n)==t[n+'_sha256']
assert (a/'stdout').read_text()=="'DiophantineConsistency.TenPositiveTrace75.evalRing_expression' depends on axioms: [propext]\n" and not (a/'stderr').read_bytes()
assert len(t['pins'])==7
for p,d in t['pins'].items():assert Path(p).is_file() and str(Path(p).resolve())==d['resolved'] and sha(p)==d['sha256']
mods=re.findall(r'^import\s+([^\s]+)',src.read_text(),re.M);assert mods==['DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.WeightedExpressionDegree']
for mod in mods:
 candidates=[Path(p)/(mod.replace('.','/')+'.olean') for p in t['lean_path'].split(':') if os.path.lexists(Path(p)/(mod.replace('.','/')+'.olean'))];assert candidates and candidates[0].is_file() and str(candidates[0]) in t['pins'];print(mod,'first',candidates[0])
for snap in [t['preflight'],t['postflight'],*t['samples']]:assert snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2
print('PASS canonical source relation, terminal/source/object/report, seven pins and two direct first selections')
