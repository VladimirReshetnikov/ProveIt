#!/usr/bin/env python3
"""No-Lean positive and negative controls for source-pinned diagnostics."""
import json,sys
from pathlib import Path
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent;DC=HERE.parents[2];sys.path.insert(0,str(HERE));import diagnostic_policy as p
HIST=DC/'reviews/ha87-isolated-full-author-pass/logs';checked=[]
def reject(label,fn):
 try:fn()
 except ValueError:checked.append(label);return
 raise RuntimeError('accepted injected failure: '+label)
for name,(source_sha,_,count) in p.EXPECTED.items():
 log=(HIST/f'DiophantineConsistency_{name}-attempt-1.log').read_text();frozen=f'/tmp/synthetic/frozen/DiophantineConsistency/{name}.lean';out=log.replace(p.HISTROOT+name+'.lean',frozen)
 p.validate(name,source_sha,frozen,out,log);checked.append(name+': exact accepted')
 reject(name+': source SHA drift',lambda:p.validate(name,'0'*64,frozen,out,log))
 reject(name+': historical log drift',lambda:p.validate(name,source_sha,frozen,out,log+'changed'))
 reject(name+': extra warning',lambda:p.validate(name,source_sha,frozen,out+'warning: injected\n',log))
 reject(name+': error',lambda:p.validate(name,source_sha,frozen,out+'error: injected\n',log))
 reject(name+': sorryAx',lambda:p.validate(name,source_sha,frozen,out+'sorryAx',log))
 reject(name+': extra output',lambda:p.validate(name,source_sha,frozen,out+'extra output\n',log))
 if count:
  reject(name+': missing warning',lambda:p.validate(name,source_sha,frozen,'',log))
  reject(name+': modified warning',lambda:p.validate(name,source_sha,frozen,out.replace('warning:', 'warning: changed',1),log))
  reject(name+': different path',lambda:p.validate(name,source_sha,frozen,out.replace(frozen,'/tmp/other.lean',1),log))
reject('unknown module',lambda:p.validate('Unknown','0'*64,'/tmp/x.lean','',''))
client="'CompactHaltWord.halt_compact_word' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
p.validate_client(client);checked.append('client report accepted')
for label,bad in [('wrong name',client.replace('halt_compact_word','other')),('extra axiom',client.replace('Quot.sound','Quot.sound, extra')),('warning',client+'warning: injected\n'),('duplicate',client+client),('sorryAx',client+'sorryAx'),('missing report','')]:reject('client: '+label,lambda bad=bad:p.validate_client(bad))
print(json.dumps({'status':'PASS_NO_LEAN_DIAGNOSTIC_CONTROLS','checks':checked,'total':len(checked),'lean_launched':False,'scope':'isolated diagnostic-policy controls, not a compiler/provider test'},indent=2,sort_keys=True))
