#!/usr/bin/env python3
"""Mutation checks for the intended v2 diagnostic and axiom-report policy.

This checks the same policy on simulated output; it does not execute Lean or
authenticate the runner. An independent source audit must compare the policy
against run-v2.py.
"""
import re
NAMES=('rows_all','inverse_all','horizontal_all','vertical_all','inversebounds_all','horizontalbounds_all','verticalbounds_all')
ALLOWED={'propext','Classical.choice','Quot.sound'}
def accept(text):
 if re.search(r'\b(?:error|warning)(?:\([^)]*\))?:|sorryAx',text):return False
 for name in NAMES:
  reports=re.findall(r"'DirectBFSCoverageAggregate\."+name+r"' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",text)
  if len(reports)!=1 or not {x.strip() for x in reports[0].split(',') if x.strip()}<=ALLOWED:return False
 return True
ok='\n'.join("'DirectBFSCoverageAggregate."+n+"' depends on axioms: [propext]" for n in NAMES)
assert accept(ok)
for extra in ('error: failure','error(lean.unknownIdentifier): failure','warning: warning','warning(lean.linter): warning','sorryAx'):
 assert not accept(ok+'\n'+extra),extra
assert not accept(ok.replace("'DirectBFSCoverageAggregate.rows_all' depends on axioms: [propext]",''))
assert not accept(ok+'\n'+ok.splitlines()[0])
assert not accept(ok.replace('[propext]','[propext, badAx]',1))
print('PASS: allowed reports accepted; missing, duplicate, unexpected axioms and tagged/untagged diagnostics rejected')
