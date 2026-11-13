from pathlib import Path
import hashlib,json,os
root=Path(__file__).resolve().parents[2];h=root/'research/trace75-bfs-ipra-draft';a=h/'observations/fixed-attempt02';t=json.loads((a/'terminal.json').read_text());src=h/'Trace75BFSFixedIPRA.lean';obj=Path(t['output']);inv=h/'overlay-inventory.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'terminal.json')=='30ee9ad59a2ee1289d8bfe35cc5d5fb352ed86e886577d3c393e115435e457d9' and t['status']=='PASS' and t['exit']==0 and t['reason'] is None
assert sha(src)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))==t['source_sha256']=='4a9f03a96a10bd2b52cb828506c4d89d97524e06e6180476547554a72262fa8d'
assert sha(h/'run-fixed.py')==t['runner_sha256']=='6aec6a4c13a94ae410209ddbcf379627bab736598921a97219923879279ca622'
assert obj.is_file() and not obj.is_symlink() and sha(obj)==t['output_sha256']=='a824917dde516e283a8046dd36e7e77df599cb997849e5c0ffb4eb88beccf909'
for n in ('stdout','stderr'):assert sha(a/n)==t[n+'_sha256']
names=['native_consistency','standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency'];expected=''.join("'Trace75BFSFixedIPRA."+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in names);assert (a/'stdout').read_text()==expected and not (a/'stderr').read_bytes()
assert len(t['pins'])==16
for p,d in t['pins'].items():assert Path(p).is_file() and str(Path(p).resolve())==d['resolved'] and sha(p)==d['sha256']
v=json.loads(inv.read_text());base=Path(v['base']);ns=Path(v['overlay'])/'DiophantineConsistency';entries=dict(v['entries']);assert len(entries)==1508 and {p.name for p in ns.iterdir()}==set(entries)
for n,target in entries.items():
 p=ns/n;assert p.is_symlink() and os.readlink(p)==target and p.is_file()
 if n!='TenPositiveTrace75Syntax.olean':assert target==str(base/n)
for mod in ('Trace75BFSIPRA','Trace75BFSModelIff','Trace75BFSSyntax','PositiveModelIPRAReferenceTranslated'):
 candidates=[Path(p)/(mod+'.olean') for p in t['lean_path'].split(':') if os.path.lexists(Path(p)/(mod+'.olean'))];assert candidates and candidates[0].is_file() and str(candidates[0]) in t['pins'];print(mod,'first',candidates[0])
for snap in [t['preflight'],t['postflight'],*t['samples']]:assert snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2
bad=json.loads((h/'observations/fixed-attempt01/terminal.json').read_text());assert bad['exit']!=0 and 'excessive memory' in (h/'observations/fixed-attempt01/stdout').read_text()
print('PASS source/object, five exact named reports, sixteen pins, 1508 links, four first selections and excluded failed attempt')
