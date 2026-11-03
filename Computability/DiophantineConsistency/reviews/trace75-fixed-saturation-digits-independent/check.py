from pathlib import Path
import hashlib,json,re
base=Path('research/trace75-root-probe')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name,attempt,runner,expected in [('FixedSaturation','fixedsaturation-attempt02','run-fixedsaturation-v2.py','9ee977a04a2623fd6e7d5701a62ac2dc324158141ea5b708880d68668fdec0eb'),('FixedDigits','fixeddigits-attempt01','run-fixeddigits.py','314a64671e7842d8d25fc2ff8ba1df9599b5c0e5edb1173acc8882f6b9aab885')]:
 o=base/'observations'/attempt; j=json.loads((o/'terminal.json').read_text()); src=base/('Trace75'+name+'.lean'); code=src.read_text()
 assert j['exit']==0 and j['reason'] is None and j['object_sha256']==expected
 assert sha(Path(j['output_root'])/('Trace75'+name+'.olean'))==expected
 assert sha(src)==sha(o/'source.txt')==j['inputs'][str(src.resolve())]
 assert sha(base/runner)==j['runner_sha256']
 assert sha(o/'stdout')==j['stdout_sha256'] and sha(o/'stderr')==j['stderr_sha256']
 log=(o/'stdout').read_text()+(o/'stderr').read_text()
 assert not re.search(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b',log)
 assert log.strip()==f"'Trace75{name}.graph_{'fixed_saturation' if name=='FixedSaturation' else 'fixed_digits'}' depends on axioms: [propext, Classical.choice, Quot.sound]"
 for p,h in j['inputs'].items(): assert sha(p)==h,(p,h)
 paths=j['lean_path'].split(':')
 for module in re.findall(r'^import (\S+)',code,re.M):
  rel=module.replace('.','/')+'.olean'; selected=next((Path(x)/rel for x in paths if (Path(x)/rel).is_file()),None)
  assert selected is not None,(name,module)
  s=str(selected)
  if s not in j['inputs']:
   matches=[v for k,v in j['inputs'].items() if Path(k).resolve()==selected.resolve()]
   assert matches,(name,module,s,str(selected.resolve()))
   h=matches[0]
  else:h=j['inputs'][s]
  assert sha(selected)==h
  print(name,module,s,sha(selected))
 assert 'p 0=betaNat' in code and 'p 2=lowNat' in code and 'p 3=betaNat+highNat' in code
 assert not re.search(r'\b(sorry|admit)\b',code)
 print(name,'PASS',len(j['inputs']),'pins',expected)
assert "unknown module prefix 'Direct80RankLower'" in (base/'observations/fixedsaturation-attempt01/stdout').read_text()
