#!/usr/bin/env python3
"""Reproduce the encoding proof patch and text counts, without Lean."""
from pathlib import Path
import json,hashlib,difflib
R=Path(__file__).resolve().parents[1]; D=R/'encoding'
rel='Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangMachineEncoding.lean'
old=(R/'sources'/rel).read_text(); c=(D/'StateNumberCandidate.lean').read_text()
a=old.index('theorem stateNumber_injective :'); b=old.index('\ntheorem bit_le_one',a)
old_decl=old[a:b].rstrip()+'\n'; old_header,old_body=old_decl.split(':= by',1)
ca=c.index('theorem stateNumber_injective_candidate :'); cb=c.index('\n-- Regression',ca)
new_body=c[ca:cb].split(':= by',1)[1].rstrip()+'\n'; new_decl=old_header+':= by'+new_body
new=old[:a]+new_decl+'\n'+old[b:]
new=new.replace('import DiophantineConsistency.DecimalMachineInitialization\n','import DiophantineConsistency.DecimalMachineInitialization\nimport Mathlib.Logic.Equiv.Fin.Basic\n',1)
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
(D/'StateNumber.patch').write_text(patch)
(D/'WangMachineEncodingCandidate.lean').write_text(new)
def count(s):return sum(bool(x.strip()) for x in s.splitlines())
result={'pin':'22e020937caa81d0cb72a4f63071d6c0bcc1eba9','target':rel,'source_sha256':hashlib.sha256(old.encode()).hexdigest(),'before_declaration_nonblank_lines':count(old_decl),'after_declaration_nonblank_lines':count(new_decl),'before_body_nonblank_lines':count(old_body),'after_body_nonblank_lines':count(new_body),'additional_import_lines':1,'header_text_unchanged':old_header==new_decl.split(':= by',1)[0],'compiled':False}
(D/'metrics.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
