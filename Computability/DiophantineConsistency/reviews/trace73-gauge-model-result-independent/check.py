from pathlib import Path
import hashlib,json,os,re
root=Path(__file__).resolve().parents[2]; h=root/'research/trace73-gauge-model'; a=h/'observations/attempt02'; t=json.loads((a/'terminal.json').read_text()); src=h/'Trace73GaugeModel.lean'; run=h/'run.py'; obj=Path(t['output'])
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'terminal.json')=='7aa6777d803be2abd7e6c69ae754933fb4ba902360de4a15ea088666a4e7826e'
assert t['status']=='PASS' and t['exit']==0 and t['reason'] is None
assert sha(src)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))==t['source_sha256']=='3fabcd4855d35807b053f2a647a139f1fd46bbc8005866b6724846461d6ced7e'
assert sha(run)==t['runner_sha256']=='5369625f82d04877f969d32791b31dec31ecc515028d58651e9f34c36817ed50'
assert obj.is_file() and not obj.is_symlink() and sha(obj)==t['output_sha256']=='f7f468617d7925be67c798ba19f82ce9c03508e41b333ff569e10eac76bae65f'
for n in ('stdout','stderr'): assert sha(a/n)==t[n+'_sha256']
assert (a/'stdout').read_text()=="'Trace73GaugeModel.positive_zero_to_negative_B' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (a/'stderr').read_bytes()
assert len(t['pins'])==12
for p,d in t['pins'].items():assert Path(p).is_file() and str(Path(p).resolve())==d['resolved'] and sha(p)==d['sha256']
mods=re.findall(r'^import\s+([^\s]+)',src.read_text(),re.M); assert mods==['Trace73GaugeSign','Trace73ModelTransfer']
for mod in mods:
 candidates=[Path(p)/(mod+'.olean') for p in t['lean_path'].split(':') if os.path.lexists(Path(p)/(mod+'.olean'))]; assert candidates and candidates[0].is_file() and str(candidates[0]) in t['pins']; print(mod,'first',candidates[0])
for snap in [t['preflight'],t['postflight'],*t['samples']]:assert snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2
bad=json.loads((h/'observations/attempt01/terminal.json').read_text()); assert bad['exit']!=0 and 'sorryAx' in (h/'observations/attempt01/stdout').read_text()
print('PASS source/copy, object, report, twelve pins, first direct selections, resource samples and excluded failed attempt')
