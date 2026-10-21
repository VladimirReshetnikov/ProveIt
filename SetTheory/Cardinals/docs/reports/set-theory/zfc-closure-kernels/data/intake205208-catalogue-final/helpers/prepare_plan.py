"""Own scratch plan; captures current documentation and exact replacement hunks."""
from pathlib import Path
import hashlib,json,subprocess
R=Path('/home/codex/.codex/worktrees/ec20/Proofs'); O=Path(__file__).resolve().parent
F='Computability/BusyBeaver/Research/ZFC/k225-formal/'
H='SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/'
changes={}
def add(p,old,new,reason):
 changes.setdefault(p,[]).append(dict(old=old,new=new,reason=reason))
add('Computability/BusyBeaver/Research/ZFC/README.md',
'''204 project modules; the [current simplification checkpoint](k225-formal/verification/k215/simplification/phase5/README.md)
checks a 184-module closure and two explicit clients with standard axioms only.''',
'''204 project modules; the [current simplification checkpoint](k225-formal/verification/k215/simplification/phase6/README.md)
checks a 187-module closure and two explicit clients with standard axioms only.
Unchanged modules retain exact predecessor source, dependency, object and log bindings.''',
'Current endpoint pointer and closure; original fresh204 claim retained.')
add('Computability/BusyBeaver/Research/ZFC/README.md','The current formal task uses both Lean and Rocq.',
'The current simplification work is Lean-only; the checked Rocq endpoint is preserved.',
'Latest user scope is Lean-only; no new Rocq execution.')
add('Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md',
'''The [current Lean simplification checkpoint](../k225-formal/verification/k215/simplification/phase5/README.md)
checks the 184-module closure and both endpoint clients, retaining exact bindings
for reused predecessor objects. The literal machine and theorem statements are
unchanged.''',
'''The [current Lean simplification checkpoint](../k225-formal/verification/k215/simplification/phase6/README.md)
checks the 187-module closure: {{FRESH}} freshly compiled modules and {{REUSED}} reused
modules with exact predecessor bindings. Both endpoint clients pass; the ten
axiom reports use only the three standard axioms and have zero audit warnings.
The project logs retain {{WARNINGS}} linter warnings. The literal machine and theorem
statements are unchanged; this is an incremental check, not a new fresh 187-module build.''',
'Final metrics come only from actual PASS plus live audit.')
add(F+'README.md',
'''[proof simplification checkpoint](verification/k215/simplification/phase5/README.md)
checks the 184-module closure and two endpoint clients with only the three
standard foundational axioms.''',
'''[proof simplification checkpoint](verification/k215/simplification/phase6/README.md)
checks the 187-module closure and two endpoint clients with only the three
standard foundational axioms, with exact bindings for reused predecessor objects.''',
'Current checkpoint pointer and count.')
add(F+'README.md',
'''separate delivered normalized-certificate and transport proofs from uncompiled
balanced-lookup and import-splitting proposals. They preserve the completed
checkpoint above; they do not certify a new endpoint or alternate machine.''',
'''retain the delivered normalized-certificate, lookup, dependency and transport
proposals with their original status. The later phase-six checkpoint above
checks selected adaptations for the same K215 endpoint; the intake records do
not certify the other proposals or an alternate machine.''',
'Keep delivery chronology distinct from later maintained integration.')
add(F+'README.md',
'''storage. Selected phase-six integration is in progress; the completed
phase-five endpoint above remains the verified checkpoint.''',
'''storage. Phase six now checks normalized source correspondence, stable-program
imports, fast transition lookup and the seed-model cleanup. Decoder factoring,
relative transports and concrete zero-credit integration retain their separate gaps.''',
'Only the actually adopted interfaces are promoted.')
add(F+'README.md',
'''  2,240 certificate entries, none offset. The Lean source proof uses
  [`KSource215Data`](../../../Lean/BusyBeaver/ZFC/KSource215Data.lean), 32 independent kernel
  checks, and the unchanged public [`KSource215`](../../../Lean/BusyBeaver/ZFC/KSource215.lean)
  composition theorem.''',
'''  1,426 normalized certificate entries, preserving the 512-step decoder.
  The earlier phase-five ordinary certificate had 2,240 entries.
  [`KSource215Program`](../../../Lean/BusyBeaver/ZFC/KSource215Program.lean) holds the stable
  literal program/tree; [`KSource215Data`](../../../Lean/BusyBeaver/ZFC/KSource215Data.lean)
  supplies the relation to 16 independent kernel checks and the unchanged public
  [`KSource215`](../../../Lean/BusyBeaver/ZFC/KSource215.lean) composition theorem.''',
'Correct current certificate and16 forward checks without erasing historical2240.')
add(H+'README.md',
'''and both unchanged endpoint audits. The exact K215 machine remains fixed.
''',
'''and both unchanged endpoint audits. The exact K215 machine remains fixed.
The later [phase-six checkpoint](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase6/README.md)
checks 187 project modules and both endpoint clients. It replaces the ordinary
2,240-entry relation with 1,426 normalized entries, preserving the literal source
and the 512-step decoder; unchanged providers remain hash-bound to phase five.
''',
'Append current successor after exact historical phase-five addendum.')
add(H+'README.md',
'''Lean already has balanced certificate storage. The separate phase-six
integration is running; no complete phase-six result is claimed here.''',
'''Lean already has balanced certificate storage. The separate phase-six
integration now passes for the selected K215 changes linked above. The other
submitted adapters and alternative-machine claims keep their intake scope.''',
'Update only current integration status, not submitted scope.')
add('SetTheory/Cardinals/docs/reports/README.md',
'''The completed phase-five endpoint remains the reference while the selected
phase-six Lean integration runs. The two later `5314ca0e6b`/`b07002a86b` archives
remain pending. No new smaller machine, whole-endpoint proof or performance
result follows merely from placement or a source-level review.''',
'''The later [phase-six Lean checkpoint](../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase6/README.md)
now checks the same endpoint over 187 project modules and two typed clients.
It integrates the normalized 1,426-entry certificate, stable-program dependency
split, fast transition lookup and seed-model cleanup; reused providers remain
bound to phase five. The two later `5314ca0e6b`/`b07002a86b` archives remain pending.
These kernel checks are separate from intake. Placement or source review alone
still supplies no smaller machine, whole-endpoint proof or performance result.''',
'Current integration successor; historical collection paragraphs remain intact.')
add('docs/incoming/README.md',
'''The queue-clear statements below describe their earlier checkpoints.''',
'''The queue-clear statements, proof-status paragraphs and ledger rows below
retain their earlier checkpoints.''',
'Explicitly preserve historical running/queue claims below current summary.')
add('docs/incoming/README.md',
'''Phase five is complete; the selected phase-six Lean integration is running and has no full-check result yet. The two later arrivals listed above remain pending.''',
'''The later [phase-six Lean checkpoint](../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase6/README.md) now passes for 187 project modules and both typed endpoint clients, with unchanged machine and theorem statements. Its reused providers retain exact phase-five bindings. The two later arrivals listed above remain pending.''',
'Current top status only; all historical intake bodies and ledger rows untouched.')
add('SetTheory/Cardinals/docs/reports/manifest.tex',
'''normalized certificates, balanced lookup and relative transport are separated
from the completed phase-five 184-module Lean checkpoint. Sources~165--166
still await their written follow-up. Two later \\texttt{5314ca0e6b}/\\texttt{b07002a86b}
arrivals remain pending. Selected phase-six Lean integration is running; no
full phase-six result is claimed here. The collection remains 290 reports.''',
'''normalized certificates, balanced lookup and relative transport retain their
intake scope. A later phase-six check validates the same K215 endpoint over
187 project modules and two typed clients, with exact predecessor bindings.
Sources~165--166 still await their written follow-up. Two later
\\texttt{5314ca0e6b}/\\texttt{b07002a86b} arrivals remain pending.
The collection remains 290 reports.''',
'Current scope paragraph; report/source counts and pending items unchanged.')
add('SetTheory/Cardinals/docs/reports/manifest.tex',
'''the current phase-five checker still certifies the ordinary 2,240-row source.''',
'''at that intake, the phase-five checker certified the ordinary 2,240-row relation.
The later phase-six result below checks the normalized 1,426-row relation for the
same source; this does not erase or relabel the historical certificate.''',
'Remove ambiguous current2240 claim while retaining exact historical fact.')
add('SetTheory/Cardinals/docs/reports/manifest.tex',
'''Balanced transition lookup and stable-program import separation are further
proof-engineering opportunities, not newly checked endpoints.''',
'''At that intake, balanced transition lookup and stable-program import separation
remained proof-engineering proposals; their selected adaptations are checked in
phase six below.''',
'Root scope precision: make the pre-integration proposal status explicitly historical.')
add('SetTheory/Cardinals/docs/reports/manifest.tex',
'''290 reports. The completed phase-five K215 endpoint remains the reference
while selected phase-six Lean integration runs. No full phase-six result,
new smaller machine or internal-PA endpoint is claimed here. The two later
\\texttt{5314ca0e6b}/\\texttt{b07002a86b} archives remain pending.''',
'''290 reports. The later phase-six K215 check passes for 187 project modules:
{{FRESH}} freshly compiled and {{REUSED}} reused with exact predecessor bindings.
Both unchanged typed clients pass, with ten standard-axiom reports and zero
audit warnings; the project logs retain {{WARNINGS}} linter warnings. It checks
1,426 normalized certificate entries with the literal 512-step decoder,
all 16 certificate chunks and all nine site batches. Stable program data,
fast transition lookup and the seed-model cleanup are integrated separately
from the delivered proposals. This incremental check does not claim a fresh
187-module replay, a smaller machine or an internal-PA endpoint. The two later
\\texttt{5314ca0e6b}/\\texttt{b07002a86b} archives remain pending.''',
'Final verification paragraph with actual placeholders; all historical paragraphs and archive/placement lists preserved.')
add(F+'verification/k215/simplification/README.md',
'''are unchanged. The [latest Lean check](phase5/README.md) validates the 184-module''',
'''are unchanged. The [latest Lean check](phase6/README.md) validates the 187-module''',
'Latest simplification pointer and count.')
add(F+'verification/k215/simplification/README.md',
'''| Lean source data | 653,569 bytes | 432,131 bytes |''',
'''| Lean source data, including stable program | 653,569 bytes | 368,995 bytes |''',
'Count both moved data files together; do not claim a reduction from moving declarations alone.')
add(F+'verification/k215/simplification/README.md',
'''| Lean site-coverage facade | 107,243 bytes | 14,916 bytes |''',
'''| Lean site-coverage facade | 107,243 bytes | 14,956 bytes |''',
'Exact current facade size after import/lookup adapter.')
add(F+'verification/k215/simplification/README.md',
'''| Lean register determinism | 17,209 bytes | 12,988 bytes |''',
'''| Lean register determinism | 17,209 bytes | 12,988 bytes |
| Lean seed-model proof | 11,711 bytes | 10,710 bytes |''',
'Explicit seed cleanup source size; original is its phase-five predecessor.')
add(F+'verification/k215/simplification/README.md',
'''lemmas shorten semantic proofs. The import closure shrinks from 204 to 184
project modules. Four root interfaces and the retained offset checker pass a
separate refresh.

The [latest checkpoint](phase5/README.md),''',
'''lemmas shorten semantic proofs. Through phase five the import closure shrank
from 204 to 184 project modules. Phase six adds normalized correspondence,
stable program data and transition-lookup transport, for 187 modules. It checks
1,426 normalized entries rather than the earlier ordinary 2,240, preserving the
512-step decoder and all 4,751 leaves. The full source partition is 375,335 bytes
in 19 files; its additional generic normalized checker is 6,365 bytes.
Four root interfaces and the retained offset checker passed a separate phase-five
refresh; that historical result is distinct from the current primary check.

The [latest checkpoint](phase6/README.md),
[fifth checkpoint](phase5/README.md),''',
'Explain added modules/data split, retain older refresh scope and chain of checkpoints.')
add(F+'verification/k215/README.md',
'''[proof simplifications](simplification/phase5/README.md) also pass: affected modules were
rebuilt and the endpoint assumption reports rerun against that pinned baseline.
The current Lean endpoint closure contains 184 project modules.''',
'''[proof simplifications](simplification/phase6/README.md) also pass: affected modules were
rebuilt and both endpoint assumption audits rerun with explicit predecessor bindings.
The current Lean endpoint closure contains 187 project modules: {{FRESH}} freshly
compiled and {{REUSED}} reused from phase five. Both audits have zero warnings and
ten reports using only the same three standard axioms; the project logs retain
{{WARNINGS}} linter warnings. This is an incremental checkpoint, not a second full fresh build.''',
'Current final metrics; original full build table and records untouched.')
add(F+'verification/k215/README.md',
'''The [Lean reproduction driver](lean/README.md), using Lean 4.32.0, now selects 184''',
'''The [Lean reproduction driver](lean/README.md), using Lean 4.32.0, now selects 187''',
'Current fresh-reproduction closure count.')
add(F+'verification/k215/lean/README.md',
'''The [subsequent simplification check](../simplification/phase5/README.md) rebuilds affected
modules against this pinned baseline and reruns both endpoint audits. Its current
closure contains 184 project modules; the audits
still have zero warnings and only the same three allowed axioms.''',
'''The [subsequent simplification check](../simplification/phase6/README.md) rebuilds affected
modules with explicit predecessor bindings and reruns both endpoint audits. Its current
closure contains 187 project modules ({{FRESH}} fresh and {{REUSED}} reused); the audits
still have zero warnings and only the same three allowed axioms.''',
'Current incremental checkpoint; original receipts retain their scope.')
add(F+'verification/k215/lean/README.md',
'''the compiler trust boundary. The current closure contains 184 project modules''',
'''the compiler trust boundary. The current closure contains 187 project modules''',
'Current portable driver import closure.')
add(F+'verification/k215/lean/README.md',
'''16 checks and the generic symmetry theorem; see the
[second simplification checkpoint](../simplification/phase2/README.md). That original partition retained every declaration statement and proof body. Further repairs use one typed congruence lemma and
local irreducibility for the dominated-axiom certificate, and narrow namespace
openings in the dispatch and seed proofs. The endpoint statements, machine,
certificate nodes, and semantic assumptions are unchanged.''',
'''16 checks and the generic symmetry theorem. The
[second simplification checkpoint](../simplification/phase2/README.md) records that reduction;
[phase six](../simplification/phase6/README.md) checks 1,426 normalized entries using
512 decoding steps and separates the stable program/tree from certificate data.
The original partition retained every declaration statement and proof body.
The original elaboration repairs used one typed congruence lemma and local
irreducibility for dominated implication, and narrow namespace openings in the
dispatch and seed proofs. Those repairs left the endpoint statements, machine,
certificate nodes and semantic assumptions unchanged; later certificate reductions
are recorded in their respective simplification checkpoints.''',
'Keep historical partition/repair claims while accurately describing current normalized certificate.')
# Snapshot exact current bytes; all replacements are single, literal and reviewed.
files=[]
for rel,hunks in changes.items():
 b=(R/rel).read_bytes();s=b.decode(); before=O/'before'/rel;before.parent.mkdir(parents=True,exist_ok=True);before.write_bytes(b)
 for row in hunks:
  assert s.count(row['old'])==1,(rel,row['reason'],s.count(row['old']))
  row['line']=s[:s.index(row['old'])].count('\n')+1
  s=s.replace(row['old'],row['new'],1)
 target=O/'template'/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_text(s)
 files.append(dict(path=rel,before_sha256=hashlib.sha256(b).hexdigest(),template_sha256=hashlib.sha256(s.encode()).hexdigest(),hunks=hunks))
assert len(files)==10
plan=dict(status='SCRATCH_TEMPLATE_ONLY_AWAITING_FINAL_PASS_AND_ROOT_GO',base_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),files=files,actual_fields={'FRESH':'fresh_modules','REUSED':'reused_modules','WARNINGS':'project_linter_warnings'},primary_project_modules=187,basis_project_modules=184,typed_audits=2,axiom_reports=10,audit_warnings=0,source_count=178,report_count=290,pending_sources=[165,166],pending_arrivals=['5314ca0e6b','b07002a86b'],compiler_invocations=0,pdf_built=False,canonical_modified=False)
(O/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
print('10 files',sum(len(f['hunks']) for f in files),'exact hunks')
