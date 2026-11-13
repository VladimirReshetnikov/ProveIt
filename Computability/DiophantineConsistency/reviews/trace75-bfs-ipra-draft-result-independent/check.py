from pathlib import Path
import hashlib,json,os,re
root=Path(__file__).resolve().parents[2];h=root/'research/trace75-bfs-ipra-draft';a=h/'observations/attempt01';t=json.loads((a/'terminal.json').read_text());src=h/'Trace75BFSIPRA.lean';obj=Path(t['output']);inv=h/'overlay-inventory.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'terminal.json')=='ebdbbfa570fd7f15ddbfb8dd29c64fbe5600c357ea359c7789da17b72b2ccc73' and t['status']=='PASS' and t['exit']==0 and t['reason'] is None
assert sha(src)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))==t['source_sha256']=='8f80194ef34f3031bb60b603cc8cd18c8e487083df85957fe846cc2b72a75f89'
assert sha(h/'run.py')==t['runner_sha256']=='45c1e512f3307ebaabdf0ca0b86fd0213cb8b463a425f1d1c027dc1dbce84c7e'
assert obj.is_file() and not obj.is_symlink() and sha(obj)==t['output_sha256']=='75d2988695d143e0e26035d0d977197c4aa1c43d29b671f525c823ec323b6212'
for n in ('stdout','stderr'):assert sha(a/n)==t[n+'_sha256']
names=['positive_bridge','native_consistency','standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency'];expected=''.join("'Trace75BFSIPRA."+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in names);assert (a/'stdout').read_text()==expected and not (a/'stderr').read_bytes()
assert len(t['pins'])==14
for p,d in t['pins'].items():assert Path(p).is_file() and str(Path(p).resolve())==d['resolved'] and sha(p)==d['sha256']
v=json.loads(inv.read_text());base=Path(v['base']);ns=Path(v['overlay'])/'DiophantineConsistency';entries=dict(v['entries']);assert len(entries)==1508 and {p.name for p in ns.iterdir()}==set(entries)
for n,target in entries.items():
 p=ns/n;assert p.is_symlink() and os.readlink(p)==target and p.is_file()
 if n!='TenPositiveTrace75Syntax.olean':assert target==str(base/n)
for mod in ('Trace75BFSModelIff','Trace75BFSSyntax','PositiveModelIPRAReferenceTranslated'):
 candidates=[Path(p)/(mod+'.olean') for p in t['lean_path'].split(':') if os.path.lexists(Path(p)/(mod+'.olean'))];assert candidates and candidates[0].is_file() and str(candidates[0]) in t['pins'];print(mod,'first',candidates[0])
for snap in [t['preflight'],t['postflight'],*t['samples']]:assert snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2
print('PASS source/object, six exact named reports, fourteen pins, 1508 links, three first selections and resource samples')
