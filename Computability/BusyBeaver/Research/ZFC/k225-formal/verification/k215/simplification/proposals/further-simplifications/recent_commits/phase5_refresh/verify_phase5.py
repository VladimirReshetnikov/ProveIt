"""Review-owned static checks only. Never import or execute fetched source."""
import hashlib, json, re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
def read(p): return p.read_text(encoding='utf-8')
def js(p): return json.loads(read(p))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(p):
    b = p.read_bytes()
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
def require(test, message):
    if not test: raise ValueError(message)

pins = js(HERE/'SOURCE_PINS.json')
for p in pins:
    f = HERE/p['local']
    require(blob(f) == p['git_blob_sha'], 'Git blob mismatch: '+p['local'])
    require(sha(f) == p['sha256'], 'SHA256 mismatch: '+p['local'])

comparison = js(HERE/'COMPARISON.json')
changed = {x['path'] for x in comparison['files']}
require(len(changed) == comparison['total_files'] == 246, 'incomplete comparison')
tree = js(HERE/'ZFC_TREE.json')
require(not tree['truncated'], 'truncated ZFC tree')
blobs = {x['path']:x['sha'] for x in tree['tree']}
prefix = 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'
matches = []
for topic in ['wellformedness', 'calibration']:
    for p in js(ROOT/topic/'SOURCE_PINS.json')['files']:
        if p['path'].startswith(prefix):
            name = p['path'][len(prefix):]
            same = blobs[name] == p['sha']
            if name != 'RMEquiv.lean': require(same, topic+' unexpected change '+name)
            matches.append(dict(topic=topic,path=p['path'],baseline_blob=p['sha'],current_blob=blobs[name],byte_identical=same))
        else:
            require(p['path'] not in changed or p['path'].endswith('generate_source215_lean.py'), 'unexpected non-ZFC input change')
for name,p in js(ROOT/'runtime_contexts/INPUT_PINS.json')['files'].items():
    if name.endswith('.lean'):
        same = blobs[name] == p['git_blob']
        if name != 'KSource215Data.lean': require(same, 'runtime unexpected change '+name)
        matches.append(dict(topic='runtime',path=prefix+name,baseline_blob=p['git_blob'],current_blob=blobs[name],byte_identical=same))
require(blobs['KZip.lean']==blob(HERE/'baseline/KZip.lean'), 'KZip changed')
matches.append(dict(topic='runtime',path=prefix+'KZip.lean',baseline_blob=blob(HERE/'baseline/KZip.lean'),current_blob=blobs['KZip.lean'],byte_identical=True))
terminal=js(ROOT/'terminal_contract/SOURCE_PIN.json')
require(terminal['path'] not in changed, 'terminal proposal changed')
require(not any('/rocq/' in p or p.endswith('/rocq') for p in changed), 'Rocq production changed')

old=read(ROOT/'runtime_contexts/inputs/KSource215Data.lean')
new=read(HERE/'production'/prefix/'KSource215Data.lean')
def program_section(s): return s[s.index('def tH'):s.index('/-! ## Forward certificate')]
require(program_section(old)==program_section(new),'program/WF/tree definitions changed')
oldrm=read(ROOT/'wellformedness/sources/RMEquiv.lean')
newrm=read(HERE/'production'/prefix/'RMEquiv.lean')
a='theorem fwd '; b='/-! ## Path runs are simulated'
require(oldrm[:oldrm.index(a)]==newrm[:newrm.index(a)],'RMEquiv prefix changed')
require(oldrm[oldrm.index(b):]==newrm[newrm.index(b):],'RMEquiv suffix changed')
require(oldrm[oldrm.index(a):oldrm.index(':= by',oldrm.index(a))]==newrm[newrm.index(a):newrm.index(':= by',newrm.index(a))],'fwd statement changed')
oldsource=read(ROOT/'recent_commits/sources/production/KSource215.lean')
newsource=read(HERE/'production'/prefix/'KSource215.lean')
def statement(s):
    a=s.index('theorem p215_halts_iff'); return s[a:s.index(':=',a)]
require(statement(oldsource)==statement(newsource),'public source proposition changed')
require('decodeAux 512 n []' in new,'512 decoder missing')
leaf_old=re.findall(r'\.leaf \((\d+), (\d+), \((\d+) : Int\), (\d+), (\d+)\)',old[old.index('def fwd0'):])
leaf_new=re.findall(r'\.leaf \((\d+), (\d+), (\d+), (\d+)\)',new[new.index('def fwd0'):])
require(len(leaf_old)==len(leaf_new)==2240,'wrong certificate count')
require(all(z=='0' and (a,b,j,k)==n for (a,b,z,j,k),n in zip(leaf_old,leaf_new)),'ordinary entries differ')
long=sum(max(int(a).bit_length()-1,int(b).bit_length()-1)>128 for a,b,j,k in leaf_new)

r=js(HERE/'evidence/lean/result.json'); live=js(HERE/'evidence/lean/live-review.json'); saved=js(HERE/'evidence/lean/saved-review.json'); outer=js(HERE/'evidence/lean/outer-execution-observation.json')
require(live['result_sha256']==saved['result_sha256']==outer['result_sha256'],'original execution result references disagree')
publication=js(HERE/'evidence/lean/publication-finalization.json')
require(saved['summary_sha256']==publication['summary_sha256']==sha(HERE/'evidence/lean/result.json'),'published summary binding mismatch')
require(outer['root_read_only_review_sha256']==sha(HERE/'evidence/lean/independent/root-actual-review.json'),'root review binding mismatch')
require(r['status']=='PASS' and r['primary_project_modules']==184 and r['fresh_modules']==37 and r['reused_modules']==147,'wrong selected closure')
require(len(r['audits'])==2 and sum(len(a['reports']) for a in r['audits'])==10,'wrong audits/reports')
for audit in r['audits']:
    require(audit['exit_code']==0 and audit['status']=='PASS' and not audit['timed_out'],'audit did not pass')
    for report in audit['reports']:
        require(set(re.split(r',\s*',report)) <= {'propext','Classical.choice','Quot.sound'},'nonstandard recorded axiom')
require(outer['outer_session_reported_exit_code']==143 and outer['fresh_compilers_and_both_audits_exit_zero'],'outer observation mismatch')
semantic=js(HERE/'evidence/semantic-lemmas/result.json')['features']
require(semantic['ConstructibleAbs']['source_sha256']==sha(HERE/'production'/prefix/'ConstructibleAbs.lean'),'ConstructibleAbs source binding')
require(semantic['InternalSat']['source_sha256']==sha(HERE/'production/SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/InternalSat.lean'),'InternalSat source binding')

result=dict(status='PASS_STATIC_SOURCE_AND_RECEIPT_BINDINGS',baseline='beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc',comparison_base=comparison['base'],cutoff=comparison['head'],adoption_commit='de9fdb0873b36d049d075a5c0568f2dfcff28e7a',fetched_blobs_verified=len(pins),complete_changed_files=246,topic_source_matches=matches,program_WF_tree_section_byte_identical=True,program_WF_tree_section_characters=len(program_section(old)),RMEquiv_only_fwd_proof_changed=True,public_source_statement_identical=True,ordinary_entries_identical_after_zero_offset_removal=2240,entries_with_over_128_bit_path=long,primary_modules=184,fresh_modules=37,reused_modules=147,typed_clients=2,axiom_reports=10,outer_exit=143,outer_cause='Not established',terminal_proposal_unchanged=True,Rocq_production_unchanged=True,scope='Static comparison of fetched text and JSON only; no Lean/Rocq or incoming code executed; archived 184-module logs/objects not independently reopened here. Build, compiler and object-rehash facts remain recorded evidence, not this review rerunning them.')
(HERE/'STATIC_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='topic_source_matches'},indent=2))
