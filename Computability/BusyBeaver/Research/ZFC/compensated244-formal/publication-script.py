from pathlib import Path
import difflib, hashlib, json, shutil

ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
Z=ROOT/'Computability/BusyBeaver/Research/ZFC'
L=ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
units=[
 ('positive-blocks','positive_block_bisimulation','PositiveBlockBisimulation',Path('/tmp/zfc244-positive-blocks'),'run2','39d7b8257fc41468782322c1131e81c8ffdef34edccd61ec539419a205bdd420'),
 ('invariant','routing245_invariant','Routing245Invariant',Path('/tmp/zfc244-routing245-invariant'),'run1','1ec56adfbe3e0df272aa82cf42f02ada7f9bb33bcedd334e73e509fc401030c9'),
 ('table','table_compensated244','TableCompensated244',Path('/tmp/zfc244-compensated-lean/table'),'run1','53745001227efd76940fa164e66dd78c34a0c276eca1deca83c56947d613f22e'),
]
entries=[]
def put(dst,data,origin=None):
 assert dst.is_relative_to(ROOT)
 assert not dst.exists(),str(dst)
 dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(data)
 entries.append(dict(path=str(dst.relative_to(ROOT)),sha256=sha(dst),origin=str(origin)if origin else'authored publication'))
def copy(src,dst):put(dst,src.read_bytes(),src)
for slug,stem,module,b,run,recordsha in units:
 record=b/run/'verification.json';assert sha(record)==recordsha
 d=json.loads(record.read_text());assert d['status']=='PASS' and d['warnings']==0
 assert sha(b/(module+'.lean'))==d['source']['sha256']
 assert sha(b/'Audit.lean')==d['audit']['sha256']
 copy(b/(module+'.lean'),L/(module+'.lean'))
 copy(b/'Audit.lean',Z/(stem+'_audit.lean'))
 archive=Z/'compensated244-formal'/slug
 # Keep original attempts and source snapshots, but never compiled caches.
 for f in sorted(b.rglob('*')):
  if not f.is_file() or f.is_symlink():continue
  rel=f.relative_to(b)
  if 'cache' in rel.parts or f.suffix not in {'.lean','.py','.json','.log','.diff'}:continue
  copy(f,archive/rel)
 raw=(b/'check.py').read_text()
 cooked=raw.replace("HERE=Path('"+str(b)+"')",'HERE=Path(__file__).resolve().parent\nREPO=HERE.parents[3]')
 cooked=cooked.replace("default=HERE/'"+module+".lean'","default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/"+module+".lean'")
 cooked=cooked.replace("default=HERE/'Audit.lean'","default=HERE/'"+stem+"_audit.lean'")
 cooked=cooked.replace("default=HERE/'boundary.json'","default=HERE/'compensated244-formal/"+slug+"/boundary.json'")
 assert raw!=cooked
 put(Z/('check_'+stem+'.py'),cooked.encode())
 delta=''.join(difflib.unified_diff(raw.splitlines(True),cooked.splitlines(True),fromfile='actual-executed-check.py',tofile='maintained-check.py'))
 put(archive/'publication-defaults.diff',delta.encode())
 copy(record,Z/'results'/('compensated244-'+slug+'-verification.json'))

reviewdir=Path('/tmp/zfc244-formal-unit-review')
for name in ['positive-block-actual-review.json','original245-invariant-actual-review.json','review_actual.py']:
 copy(reviewdir/name,Z/'compensated244-formal'/'reviews'/name)

doc='''# Lean foundations for the compensated 244-state machine

Three checked units support the transfer from the verified routed 245-state
machine to the compensated 244-state candidate from `248bc05936`.
The complete 244-state halting-equivalence theorem remains in progress.

| Unit | What Lean proves | Named probes / typed callers |
| --- | --- | --- |
| [PositiveBlockBisimulation](../../Lean/BusyBeaver/ZFC/PositiveBlockBisimulation.lean) | A relation that matches halting and advances both machines by positive blocks preserves halting, with an explicit blank-start specialization. | 4 / 4 |
| [Routing245Invariant](../../Lean/BusyBeaver/ZFC/Routing245Invariant.lean) | The original machine's local left-bit invariant holds at every time from the common start, for arbitrary head and finite-support tape. | 5 / 8 |
| [TableCompensated244](../../Lean/BusyBeaver/ZFC/TableCompensated244.lean) | The exact 244-state/488-row table, retained-state embedding, 482 common transitions and required literal local rows. | 53 / 6 |

All three actual source/audit runs pass with zero warnings and only standard
Lean axioms. The source/audit times are respectively 0.558/0.442,
9.369/0.275 and 14.023/0.434 seconds. Their exact records are
[generic](results/compensated244-positive-blocks-verification.json),
[invariant](results/compensated244-invariant-verification.json), and
[table](results/compensated244-table-verification.json).
The source and audit files are byte-identical to those executions.

The table is the principal compensated variant. Canonical states are 0–243,
start 0, dispatcher 88, with separate halt target 244. Its old labels delete
122 from Routing245 and change four retained rows. The embedding skips old
canonical state 113 and preserves the entire head and tape. The root's separate
parser comparison confirms all 488 delivered actions and all 244 old labels.
The old-label lookup has a total fallback on absent labels; those fallback
values are not extra states. Neither the alternative 244 tables nor a new
source theory are substituted.

The invariant says that old states 68 and 167 have a one immediately left
of the head, and at old state 81 a one on the left implies another one two
cells left. It is derived from the complete incoming transitions and preserved
by every step. The generic proof uses induction on an actual halting time;
absorbing halt handles a halt inside a block. No bound on the block clocks
or choice of an infinite sequence of blocks is assumed.

These formal units use `Core`'s finite-support `List Int` tapes, including
arbitrary list representations. The submitted ordinary proof has the broader
all-function-tapes formulation. Neither claim should be silently substituted
for the other. Blank tape is within the checked formal domain.

Each guard reuses exactly two selected project source/object pairs from the
actual checked BinaryRouting245 evidence. It pins the compiler and relevant
toolchain providers, captures the newly compiled object before auditing, and
checks inputs and first providers afterwards. Source and audit share 120 seconds,
run serially with `-j1 -M4096`, and use default proof limits. No dependency
build, download, compiler-version query, `sorry` or `native_decide` is used.
This does not re-execute the 851-module ancestor closure.

The generic first attempt remains a failed whole-unit check: both Lean commands
succeeded, but an unqualified audit name also printed an imported theorem,
producing five reports instead of four. Fully qualifying the four audit names
repaired the census; the source and typed callers were unchanged. Original
logs, failed record, earlier unexecuted drafts, repairs, exact guards and review
receipts are retained under [compensated244-formal](compensated244-formal/).
Review roles are stated in the receipts, including the invariant author's
review of the root's execution. The source's historical draft comment is
preserved; the actual execution record establishes its later checked status.

## Reproduction

From this directory, run one unit at a time with a new external output directory:

```sh
python3 -B check_positive_block_bisimulation.py --prepare-only --output /tmp/c244-generic-prepared
python3 -B check_positive_block_bisimulation.py --output /tmp/c244-generic-actual
python3 -B check_routing245_invariant.py --output /tmp/c244-invariant-actual
python3 -B check_table_compensated244.py --output /tmp/c244-table-actual
```

The maintained guards differ from the executed guards only in source, audit
and boundary path defaults; the exact changes are retained as publication
diffs. They require the exact existing cached providers and compiler named
in their boundaries, including historical scratch paths. Preparation invokes
no proof compiler. This is a check against recorded providers, not a standalone
dependency bootstrap for a fresh machine.

The remaining transfer obligations are the seven local execution blocks,
their global checkpoint simulation, and composition with
[BinaryRouting245](routing245_binary.md). Internal PA formalization remains
a separate open task. No absolute consistency or unconditional nonhalting
claim follows from these three units.
'''
put(Z/'compensated244_foundations.md',doc.encode())
record=dict(status='PUBLISHED_BYTE_IDENTICAL_CHECKED_SOURCES',proof_execution=False,
 actual_records={slug:recordsha for slug,_,_,_,_,recordsha in units},
 guard_changes='Only maintained source/audit/boundary path defaults; exact diffs shipped.',files=entries)
put(Z/'results/compensated244-foundations-publication.json',(json.dumps(record,indent=2)+'\n').encode())
Path('/tmp/zfc244-foundations-published-paths.json').write_text(json.dumps(entries,indent=2)+'\n')
print(json.dumps(dict(files=len(entries),publication=str(Z/'results/compensated244-foundations-publication.json'))))
