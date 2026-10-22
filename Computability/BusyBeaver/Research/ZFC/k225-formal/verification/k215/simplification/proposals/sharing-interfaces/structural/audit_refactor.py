"""Owned source-only refactoring audit. Does not run downloaded code or a prover."""
if not __debug__:raise SystemExit('Run without -O/PYTHONOPTIMIZE')
import json,hashlib,difflib
from pathlib import Path
B=Path(__file__).resolve().parent
P=B/'inputs'
D=P/'affine_core/source_deps'
plain=(D/'K230P/Bisim230.v').read_text();norm=(D/'NormalizedBisim.v').read_text()
a=plain[plain.index('Lemma branch_sim'):plain.index('End Sound.')]
b=norm[norm.index('Lemma nbranch_sim'):norm.index('End Sound.')]
sim1=plain[plain.index('Lemma sim N'):plain.index('End Sound.')]
sim2=norm[norm.index('Lemma nsim N'):norm.index('End Sound.')]
# The main induction is identical after renaming its checker-specific symbols.
renamed=sim2.replace('nsim','sim').replace('nentry_ok','entry_ok').replace('nbranch_sim','branch_sim')
assert renamed==sim1
# Standalone extraction keeps the utility proofs byte-identical.
utilities=norm[norm.index('Fixpoint zeros'):norm.index('Definition nbranch_ok')]
header='(** PROPOSED source-only extraction; not compiled in this environment. *)\nFrom Coq Require Import List Bool Arith Lia NArith.\nFrom K230 Require Import RM RMEquiv.\nImport ListNotations.\n\n'
(B/'proposed/PathEq.v').write_text(header+utilities)
bridge=(P/'affine_core/SourceGraphBridge.v').read_text()
new=bridge.replace('Require Import NormalizedBisim DrainCore.','Require Import PathEq DrainCore.').replace('NormalizedBisim.','PathEq.')
assert 'NormalizedBisim' not in new
assert new.replace('Require Import PathEq DrainCore.','Require Import NormalizedBisim DrainCore.').replace('PathEq.','NormalizedBisim.')==bridge
(B/'proposed/SourceGraphBridge.v').write_text(new)
(B/'path_eq_extraction.patch').write_text(''.join(difflib.unified_diff(bridge.splitlines(True),new.splitlines(True),fromfile='SourceGraphBridge.v',tofile='SourceGraphBridge.v')))
files=[D/'K230P/Bisim230.v',D/'NormalizedBisim.v',P/'affine_core/SourceGraphBridge.v',P/'lean_integration/source/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMBisim.lean']
out={'sources':[{'path':str(f.relative_to(B)),'bytes':len(f.read_bytes()),'sha256':hashlib.sha256(f.read_bytes()).hexdigest()} for f in files], 'plain_simulation_lines':len(a.splitlines()),'normalized_simulation_lines':len(b.splitlines()),'identical_main_induction_after_renaming':True,'identical_main_induction_lines':len(sim1.splitlines()),'extracted_utilities_lines':len(utilities.splitlines()),'bridge_edit_only_import_and_qualification':True,'status':'Text/provenance checks passed. Proposed extraction not prover-compiled.'}
(B/'AUDIT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
