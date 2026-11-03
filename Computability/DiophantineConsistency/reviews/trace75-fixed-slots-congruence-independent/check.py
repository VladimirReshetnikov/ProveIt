from pathlib import Path
import hashlib,json,re
base=Path('research/trace75-root-probe')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name,attempt,runner,expected in [('FixedSlots','fixedslots-attempt01','run-fixedslots.py','63c29a06e1efa989917b77548c8362622a038fe0531373a7f86993343f80cda1'),('FixedCongruence','fixedcongruence-attempt01','run-fixedcongruence.py','c0f5362c02d9eb09f731d3a7c5ff178407991c8c252c2a57e23794084804a930')]:
 o=base/'observations'/attempt; j=json.loads((o/'terminal.json').read_text()); src=base/('Trace75'+name+'.lean'); code=src.read_text()
 assert j['exit']==0 and j['reason'] is None and j['object_sha256']==expected
 assert sha(Path(j['output_root'])/('Trace75'+name+'.olean'))==expected
 assert sha(src)==sha(o/'source.txt')==j['inputs'][str(src.resolve())]
 assert sha(base/runner)==j['runner_sha256']
 assert sha(o/'stdout')==j['stdout_sha256'] and sha(o/'stderr')==j['stderr_sha256']
 log=(o/'stdout').read_text()+(o/'stderr').read_text()
 assert not re.search(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b',log)
 expected_reports=(["'Trace75FixedSlots.increment_digits' depends on axioms: [propext, Classical.choice, Quot.sound]", "'Trace75FixedSlots.graph_fixed_slots' depends on axioms: [propext, Classical.choice, Quot.sound]"] if name=='FixedSlots' else ["'Trace75FixedCongruence.graph_fixed_congruence' depends on axioms: [propext, Classical.choice, Quot.sound]"])
 assert log.strip().splitlines()==expected_reports,log

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
 assert re.search(r'p 0=(?:CompactFixedBeta\.)?betaNat',code) and 'p 2=lowNat' in code and re.search(r'p 3=(?:CompactFixedBeta\.)?betaNat\+highNat',code)
 assert not re.search(r'\b(sorry|admit)\b',code)
 print(name,'PASS',len(j['inputs']),'pins',expected)
