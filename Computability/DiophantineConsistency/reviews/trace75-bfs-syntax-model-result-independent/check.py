from pathlib import Path
import hashlib,json,os,re
root=Path(__file__).resolve().parents[2];h=root/'research/trace75-bfs-syntax';a=h/'observations/model-attempt02';t=json.loads((a/'terminal.json').read_text());src=h/'Trace75BFSSyntax.lean';obj=Path(t['output']);inv=h/'overlay-inventory.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'terminal.json')=='89b3d9896560c50a6c82a4babf2380b7a6dac90ea3200aa60be11fbeadfdaa15' and t['status']=='PASS' and t['exit']==0 and t['reason'] is None
assert sha(src)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))==t['source_sha256']=='f71d277d0e04a9e516f91df0ebdcd233306f5c82200607faec93e444148ef3c4'
assert sha(h/'run-model.py')==t['runner_sha256']=='aa368b858432b6b68b1fdad86b1220b3f4f2c289224f08ab3cdd6c0e3adc3ee3'
assert obj.is_file() and not obj.is_symlink() and sha(obj)==t['output_sha256']=='15c89721715979a0071a7e5fa1bfca8d4188fd38b22480f4008532a09b5e3e9c'
for n in ('stdout','stderr'):assert sha(a/n)==t[n+'_sha256']
assert (a/'stdout').read_text()=="'Trace75BFSSyntax.literal_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (a/'stderr').read_bytes()
assert len(t['pins'])==8
for p,d in t['pins'].items():assert Path(p).is_file() and str(Path(p).resolve())==d['resolved'] and sha(p)==d['sha256']
v=json.loads(inv.read_text());base=Path(v['base']);ns=Path(v['overlay'])/'DiophantineConsistency';entries=dict(v['entries']);assert len(entries)==999 and {p.name for p in ns.iterdir()}==set(entries)
for n,target in entries.items():
 p=ns/n;assert p.is_symlink() and os.readlink(p)==target and p.is_file()
 if n!='TenPositiveTrace75Syntax.olean':assert target==str(base/n)
for mod in ('DiophantineConsistency.TenPositiveTrace75Syntax','Trace75Factors'):
 candidates=[Path(p)/(mod.replace('.','/')+'.olean') for p in t['lean_path'].split(':') if os.path.lexists(Path(p)/(mod.replace('.','/')+'.olean'))];assert candidates and candidates[0].is_file();print(mod,'first',candidates[0],'target',candidates[0].resolve())
for snap in [t['preflight'],t['postflight'],*t['samples']]:assert snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2
bad=json.loads((h/'observations/model-attempt01/terminal.json').read_text());assert bad['exit']!=0 and 'sorryAx' in (h/'observations/model-attempt01/stdout').read_text()
print('PASS source/object/report, eight pins, 999 overlay links, selected direct objects, resource samples and excluded failed attempt')
