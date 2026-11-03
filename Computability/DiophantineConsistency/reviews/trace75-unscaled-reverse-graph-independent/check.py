from pathlib import Path
import hashlib,json,os,re
root=Path(__file__).resolve().parents[2]; h=root/'research/trace75-unscaled-reverse-graph-prototype'; a=h/'observations/data-attempt04'; om=h/'observations/overlay-attempt01/result.json'
t=json.loads((a/'terminal.json').read_text()); overlay=json.loads(om.read_text()); s=h/'Trace75UnscaledReverseGraph.lean'; runner=h/'run-v4.py'; obj=Path(t['output_root'])/'Trace75UnscaledReverseGraph.olean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'terminal.json')=='20367a786cc783f56fc996ba497ce9348cfb44079cbf443c0c42a53a58bbee12'
assert sha(om)==t['pins']['overlay_manifest']=='60f41f892354d0fb1fab6b07e15c1881a34a1e1fc9d3e9da6f2c5079d33e6845'
assert t['exit']==0 and t['reason'] is None and t['pins']==t['after']
assert sha(s)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))==t['pins']['source']=='3491fbe0d8b0cf550ab20c6dce165fff9707437faefb6c82e4f234ee85d58aa5'
assert sha(runner)==t['pins']['runner']=='93d2f6189ade7779f06d1c222ad6fe9b84c28ddec8cc0bcc46831b5993dcceed'
assert obj.is_file() and not obj.is_symlink() and sha(obj)==t['object_sha256']=='50e65bb13f008d7efd3e6e4b9806251bdd87014e88e8e714aa92b51631aad6a3'
for n in ('stdout','stderr'): assert sha(a/n)==t[n+'_sha256']
assert (a/'stdout').read_text()=="'Trace75UnscaledReverseGraph.graph_zero_of_source' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (a/'stderr').read_bytes()
mods=re.findall(r'^import\s+([^\s]+)',s.read_text(),re.M); assert mods==['Trace75UnscaledReverseData','Trace75NaturalPartsBinding']
for mod in mods:
    candidates=[Path(p)/(mod+'.olean') for p in t['lean_path'].split(':') if os.path.lexists(Path(p)/(mod+'.olean'))]; first=candidates[0]; entry=t['pins']['direct_imports'][mod]
    assert first.is_file() and str(first)==entry['path'] and str(first.resolve())==entry['real_path'] and sha(first)==entry['sha256']
    print(mod,'first',first)
old,fresh=overlay['old'],overlay['fresh']; assert (len(old),len(fresh),len(set(old)&set(fresh)))==(1506,998,997)
diff=sorted(n for n in set(old)&set(fresh) if old[n]['sha256']!=fresh[n]['sha256']); assert diff==overlay['differences'] and len(diff)==5
assert set(overlay['selected'])==set(old)|set(fresh)
for label in ('old','fresh'):
    rec=overlay[label]; base=Path(overlay[label+'_root'])
    assert {str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()}==set(rec)
    for n,x in rec.items():
        p=base/n; assert str(p)==x['path'] and str(p.resolve(strict=True))==x['target'] and sha(p)==x['sha256']
for n,x in overlay['selected'].items():
    want=old.get(n,fresh.get(n)); assert x==want
    p=Path(overlay['root'])/'DiophantineConsistency'/n; assert p.is_symlink() and str(p.resolve(strict=True))==x['target'] and sha(p)==x['sha256']
assert len([p for p in (Path(overlay['root'])/'DiophantineConsistency').rglob('*') if p.is_file()])==len(overlay['selected'])
for snap in [t['preflight'],*t['samples']]: assert snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2
for i in (1,2): assert 'error:' in (h/f'observations/data-attempt0{i}/stdout').read_text()
old3=(h/'observations/data-attempt03/stdout').read_text(); t3=json.loads((h/'observations/data-attempt03/terminal.json').read_text()); assert t3['exit']==0 and 'warning:' in old3 and 'error:' not in old3 and 'sorryAx' not in old3
print('PASS source, terminal, direct selections, overlay inventories, five old-first differences, retained rejected attempts')
print('differences',', '.join(diff))
