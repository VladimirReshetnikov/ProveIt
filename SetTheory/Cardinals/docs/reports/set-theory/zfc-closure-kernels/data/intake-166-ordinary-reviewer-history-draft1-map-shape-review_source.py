#!/usr/bin/env python3
"""Reviewer-owned static literal/provenance bindings; no machine execution."""
from pathlib import Path
import hashlib, json, re, subprocess

P = Path('/tmp/zfc244-248bc05936-inspection/zfc244-compensated-routing-20261018')
R = Path('/home/codex/.codex/worktrees/ec20/Proofs')
OUT = Path(__file__).resolve().parent
checks = []
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def desc(p): return {'path':str(p),'sha256':sha(p)}
def check(test, label):
    assert test, label
    checks.append(label)
def load(p): return json.loads(Path(p).read_text())
def table(p):
    rows = {}; start = None
    for line in Path(p).read_text().splitlines():
        if line.startswith('#! start '):
            check(start is None, f'unique start {p.name}')
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            q,b,w,m,t = line.split(); q,b,w,t=map(int,(q,b,w,t))
            check((q,b) not in rows and b in (0,1) and w in (0,1) and m in ('L','R'),f'literal {p.name}:{q}/{b}')
            rows[q,b]=(w,m,t)
    states={q for q,b in rows}
    check(set(rows)=={(q,b) for q in states for b in (0,1)}, f'total {p.name}')
    return start,states,rows

oldpath=P/'runtime/reference/zfc245_old.tm'
newpath=P/'machine/zfc_compensated244_old.tm'
canpath=P/'machine/zfc_compensated244.tm'
os,oq,old=table(oldpath); ns,nq,new=table(newpath); cs,cq,canonical=table(canpath)
check((os,ns,cs)==(95,95,0),'start metadata')
check(len(oq)==245 and len(nq)==244 and len(canonical)==488,'245/244/488 census')
check(oq-nq=={122} and nq-oq==set(),'removed working state only122')
check({x[2] for x in old.values()}-oq=={254},'old halt target only254')
check({x[2] for x in new.values()}-nq=={254},'new halt target only254')
check(cq==set(range(244)) and {x[2] for x in canonical.values()}-cq=={244},'canonical244 target-only halt')
expected={(92,1):((1,'L',24),(1,'R',66)),(104,1):((1,'R',122),(1,'R',92)),(106,1):((1,'R',122),(1,'R',92)),(167,1):((1,'L',92),(1,'L',151))}
changed={k:(old[k],new[k]) for k in new if old[k]!=new[k]}
check(changed==expected,'exact four retained row changes')
check(old[122,0]==(0,'R',25) and old[122,1]==(1,'R',66),'two removed rows')
mp=load(P/'machine/renumbering.json'); seq=mp['canonical_to_old']
check(seq==[95]+sorted(nq-{95}),'canonical ordering')
ren={int(k):v for k,v in mp['old_to_canonical'].items()}
check(ren=={q:i for i,q in enumerate(seq)},'inverse working map')
check((mp['halt_old'],mp['halt_canonical'])==(254,244),'halt map')
rename={**ren,254:244}
check(canonical=={(rename[q],b):(w,m,rename[t]) for (q,b),(w,m,t) in new.items()},'all488 rows conjugate under bijection')
check(ren[96]==88,'dispatch map88')
for a,b in [('runtime/candidate_1_244.tm','machine/zfc_compensated244.tm'),('runtime/candidate_1_244_old.tm','machine/zfc_compensated244_old.tm'),('runtime/candidate_1_renumbering.json','machine/renumbering.json')]:
    check((P/a).read_bytes()==(P/b).read_bytes(),f'principal duplicate {a}')
maintained=R/'Computability/BusyBeaver/Research/ZFC/candidate-routing245/zfc_routing245_old.tm'
check(oldpath.read_bytes()==maintained.read_bytes(),'baseline byte-identical maintained245')
facts=load(P/'machine/facts.json')
check(sha(canpath)==facts['canonical_sha256'] and sha(newpath)==facts['old_label_sha256'],'delivered exact machine digests')
texrows={}
for line in (P/'machine/transition-table.tex').read_text().splitlines():
    if not re.match(r'^\d+ & ',line): continue
    fields=line.removesuffix(' \\\\').split(' & ')
    check(len(fields)==6,'printed table six columns')
    for i in (0,3):
        q=int(fields[i])
        for b in (0,1):
            match=re.fullmatch(r'\$([01])\\,([LR])\\,(\d+)\$',fields[i+1+b])
            check(match is not None,f'printed table parse {q}/{b}')
            w,m,t=match.groups();texrows[q,b]=(int(w),m,int(t))
check(texrows==canonical,'printed appendix all488 literal rows')
expected_incoming={68:[(52,1,1,'R',68),(123,1,1,'R',68)],81:[(68,1,1,'R',81),(123,0,0,'R',81)],167:[(145,1,1,'R',167),(148,1,1,'R',167)]}
for q,edges in expected_incoming.items():
    for name,rows in [('old',old),('new',new)]:
        actual=sorted((s,b,*v) for (s,b),v in rows.items() if v[2]==q)
        check(actual==edges,f'complete {name} incoming{q}')
ordinary=[k for k in old if k[0] not in (92,122) and k not in {(81,1),(104,1),(106,1),(167,1)}]
check(len(ordinary)==482 and all(old[k]==new[k] and old[k][2] not in (92,122) for k in ordinary),'482 identical ordinary rows remain checkpoints')
audit=load(P/'runtime/local-stuttering-audit.json')
check(audit['local_cases']==len(audit['local_cases_detail'])==7,'seven recorded local cases')
for case in audit['local_cases_detail']:
    for side,rows in [('old',old),('new',new)]:
        for row in case[side]['rows']:
            check(rows[row['state'],row['read']]==(row['write'],row['move'],row['target']),f'recorded literal {case["name"]}/{side}/{row["state"]}')
check(sum(c['old']['steps'] for c in audit['local_cases_detail'])==18 and sum(c['new']['steps'] for c in audit['local_cases_detail'])==20,'recorded18/20 transition census; not replayed')
manifest=load(P/'provenance/source_manifest.json')
provenance=[]
for source in manifest['sources']:
    local=P/'provenance'/source['local_file']
    path=source['url'].split('/'+manifest['baseline_commit']+'/',1)[1]
    historical=subprocess.check_output(['git','show',manifest['baseline_commit']+':'+path],cwd=R)
    check(local.read_bytes()==historical and sha(local)==source['sha256'],f'exact pinned Git source {path}')
    provenance.append({**desc(local),'commit':manifest['baseline_commit'],'repository_path':path})
runtime=load(P/'runtime/candidate_1_full_symbolic.json')
for key,rel in [('table_sha256','machine/zfc_compensated244_old.tm'),('source_sha256','runtime/reference/context246/sources/Prog254.v'),('alternative_sites_sha256','runtime/certificate/sites_physical.json'),('invariant_sha256','runtime/results/interval-invariants.json')]:
    check(runtime[key]==sha(P/rel),f'archived runtime {key} binding')
check(runtime['counts']=={'cases':8391,'symbolic_rules':2315075} and len(runtime['cases'])==8391 and len(runtime['rows'])==488,'archived runtime counts only')
boot=load(P/'runtime/candidate_1_boot.json')
check(boot['table_sha256']==sha(newpath) and boot['steps']==407951,'archived boot exact machine/time')
check(boot['spare_values']==[1]*167 and len(set(boot['all_one_positions']))==351 and boot['all_other_cells_zero'],'archived complete support census only')
read_files=['README.md','report.tex','proof/contextual_fold.tex','proof/independent_audit.tex','equational/formalism_landscape.tex','equational/equational_reduction.tex','runtime/verify_local_stuttering.py','verify.py']
inventory=[{**desc(p),'relative_path':str(p.relative_to(P))} for p in sorted(P.rglob('*')) if p.is_file() and p.name!='SHA256SUMS']
result={
 'status':'SOURCE_ONLY_ORDINARY_PROOF_REVIEW_NO_OPEN_FINDINGS',
 'findings':[],
 'reviewer_role':'Independent ordinary-mathematical/source reviewer; no delivered program, simulator, proof compiler, guard or build executed.',
 'reviewer_source':desc(Path(__file__)),
 'arrival_commit':'248bc05936',
 'scope':'Principal candidate1, direct all-tape245-to244 theorem, printed literal table, baseline snapshots, and ancillary equational ordinary proof. Metadata parsing is independent and does not rerun the delivered checkers.',
 'manually_read_full_sources':[desc(P/f) for f in read_files],
 'machine':{'old':desc(oldpath),'new_old_labels':desc(newpath),'new_canonical':desc(canpath),'maintained_baseline':desc(maintained),'states':244,'rows':488,'start':0,'dispatch':88,'halt':244,'deleted_old_state':122,'retained_changes':[{'row':list(k),'before':list(v[0]),'after':list(v[1])} for k,v in expected.items()]},
 'provenance_snapshots':provenance,
 'mathematical_assessment':[
  'At start old95 the local invariant is vacuous for every head and tape. Complete incoming edges establish left-one at68/167 and the required two-cell implication at81.',
  'The checkpoint relation excludes92 and122 and equates all tape cells, head and surviving old control label. Exactly482 ordinary literal rows preserve checkpoints; the four exceptional entry rows split into seven exhaustive local cases.',
  'Manual derivation of all seven blocks confirms identical whole-tape endpoints. Only81/read1 with preceding11 erases cells h-1 and h; old6 versus new4 steps. Entries104/106 with next0 take old2 versus new4 with no tape change. Remaining blocks take2/2.',
  'All selected blocks have positive clocks and no exceptional halt. Finite paired-prefix induction transfers both halting directions; old6t bounds a reverse argument against a proposed new halt by t. No global choice or second-order all-tape principle is needed for the blank specialization.',
  'The clock identity new=old+2A-2B and bounds (2/3)old<=new<=2old follow by summing aligned complete blocks, not by matching every microstep.',
  'The principal theorem concerns every tape/head at shared start95, not arbitrary initial control states or an unconditional identification of92 and122. Variants2/3 do not inherit this principal all-tape proof automatically.',
  'The blank bootstrap407951 and whole-frame8391 certificate are corroborating artifacts; the direct stuttering proof transfers the already checked245 endpoint without reproving source grammar,3013-pair source bisimulation or8391 cases.',
  'The claimed ZFC-provable calibration composes the explicitly inherited ordinary baseline calibration with the arithmetically formalizable local reduction. The external Lean theorem is not itself an object-language PA proof. No new244 Lean endpoint or fullPA calibration is supplied.',
  'Ancillary equational forward construction correctly uses the singleton embedding/powerset retraction for arbitrary object assignments. Reverse construction keeps the full Boolean carrier and applies an ultrafilter only to predicate values; original functions need not preserve its kernel.',
  'Ground contextual rewriting completeness follows from the quotient of ground terms by bidirectional rewrite congruence, using the available constant and full ground substitutions for every equation variable. Equality completion permits quotienting by Q before returning to native equality.',
  'The equational argument retains the cited single-axiom Boolean-basis theorem and inherited FC13B calibration as dependencies. Finite truth tables do not establish the Boolean basis. The21-equation2324-bit packet and artificial contradiction demo do not constitute a smaller binary machine or a ZFC contradiction.'
 ],
 'next_checked_unit':'Literal244 table/bijection plus the generic positive-block halting lemma; then local tape invariant,482-row graph facts and seven full-tape identities, followed by composition with BinaryRouting245. No replacement of the entire checked source/runtime pipeline is mathematically necessary.',
 'execution_claims':{'supplied_execution':False,'compiler_execution':False,'new_Lean_or_PA_proof':False,'archived_runtime_counts_are_metadata_only':True,'root_replay_review_separate':True,'checksum_manifest_ignored':True},
 'static_checks':checks,'static_check_count':len(checks),'delivery_inventory_excluding_ignored_checksum_manifest':inventory
}
(OUT/'review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'review':desc(OUT/'review.json'),'checks':len(checks),'delivery_members_recorded':len(inventory)}))
