#!/usr/bin/env python3
"""Read-only source-composition audit. No Lean elaboration or kernel check is performed."""
from pathlib import Path
import argparse, difflib, hashlib, json, re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--baseline',type=Path,help='Pinned main Lean directory, Lean root, or repository snapshot')
p.add_argument('--output',type=Path,help='Optionally write JSON; default is stdout only')
a=p.parse_args()
def require(c,m):
    if not c:raise SystemExit('FAIL: '+m)
def find_baseline(root):
    return next((r for r in [root,root/'DiophantineConsistency',root/'Lean/DiophantineConsistency',
        root/'Computability/DiophantineConsistency/Lean/DiophantineConsistency']
        if (r/'WangTiles942RowStep.lean').is_file()),None)
roots=[a.baseline] if a.baseline else [ROOT/'baseline',ROOT/'upstream']
base=next((d for r in roots if (d:=find_baseline(r)) is not None),None)
require(base is not None,'baseline absent; supply --baseline PATH')
source=(base/'WangTiles942RowStep.lean').read_text()
sha=lambda t:hashlib.sha256(t.encode()).hexdigest()
require(sha(source)=='f4b6f60e4dece143de6d45120c8aa8ae84691d50b1b888e6e0dcb0226f17f84b','pinned source hash')
variants={'row_causality':(HERE/'candidate/WangTiles942RowStep.lean').read_text(),
          'canonical_row':(ROOT/'machine/patched/WangTiles942RowStep.lean').read_text()}
expected=(HERE/'combined/WangTiles942RowStep.lean').read_text()
metric=json.loads((HERE/'combined/metrics.json').read_text())
require(sha(variants['row_causality'])==metric['row_candidate_sha256'],'row candidate hash')
require(sha(variants['canonical_row'])==metric['machine_candidate_sha256'],'canonical candidate hash')
require(sha(expected)==metric['combined_candidate_sha256'],'combined candidate hash')
lines=source.splitlines(True);edits=[]
for name,text in variants.items():
    changed=text.splitlines(True)
    for tag,i1,i2,j1,j2 in difflib.SequenceMatcher(a=lines,b=changed,autojunk=False).get_opcodes():
        if tag!='equal':edits.append((i1,i2,changed[j1:j2],name))
edits.sort(key=lambda e:(e[0],e[1],e[3]))
result=[];cursor=0
for start,end,replacement,name in edits:
    require(start>=cursor,'proposal edits overlap')
    result.extend(lines[cursor:start]);result.extend(replacement);cursor=end
combined=''.join(result+lines[cursor:])
require(combined==expected,'combined candidate does not equal disjoint composition')
path='Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942RowStep.lean'
patch=''.join(difflib.unified_diff(source.splitlines(True),combined.splitlines(True),
    fromfile='a/'+path,tofile='b/'+path))
require(patch==(HERE/'combined/causality-and-canonical-row.patch').read_text(),'combined patch drift')
def size(text):
    return {'physical_lines':len(text.splitlines()),'nonblank_lines':sum(bool(l.strip()) for l in text.splitlines()),'utf8_bytes':len(text.encode())}
def declarations(text):
    return {m.group(1):(m.group(2),m.group(3).rstrip()) for m in re.finditer(
        r'(?m)^theorem (\w+)\b([\s\S]*?) := by\n([\s\S]*?)(?=\n/--|\nend )',text)}
before=declarations(source);after=declarations(combined)
for name,(sig,body) in before.items():require(sig==after[name][0],'existing statement drift '+name)
changed=[name for name in before if before[name][1]!=after[name][1]]
added=sorted(set(after)-set(before))
before_proof=sum(size(before[name][1])['nonblank_lines'] for name in changed)
after_proof=sum(size(after[name][1])['nonblank_lines'] for name in changed+added)
require(metric['module_before']==size(source),'before module metrics')
require(metric['module_after']==size(combined),'after module metrics')
require(metric['module_net_delta']=={k:size(combined)[k]-size(source)[k] for k in size(source)},'net module metrics')
require(metric['proof_body_nonblank_before_changed_consumers']==before_proof,'before proof metrics')
require(metric['proof_body_nonblank_after_changed_consumers_and_new_helpers']==after_proof,'after proof metrics')
require(metric['proof_body_net_delta_nonblank']==after_proof-before_proof,'net proof metrics')
require(metric['existing_statements_preserved']==list(before),'preserved declaration list')
require(metric['changed_existing_proofs']==changed,'changed proof list')
require(metric['new_declarations']==added,'new declaration list')
require('no_south438' in after['far_pass'][1],'derived no-finish dropped')
for name in ('receive_at_next_head','far_pass_or_finish'):
    require('hTime' not in ''.join(after[name]),'temporal premise leaked into causal theorem')
require(not re.search(r'\b(sorry|admit|axiom|native_decide)\b',combined),'unchecked proof escape')
receipt={'result':'PASS_STATIC_COMPOSITION_ONLY','pin':metric['pin'],
    'source_sha256':sha(source),'combined_candidate_sha256':sha(combined),
    'proposals_have_disjoint_source_edits':True,'original_statements_preserved':list(before),
    'module_before':size(source),'module_after':size(combined),
    'module_net_delta':metric['module_net_delta'],'proof_body_net_delta_nonblank':after_proof-before_proof,
    'counting':'Each changed original proof and each new helper counted once; no assumed-baseline savings claimed.',
    'lean_elaboration':'NOT RUN','lean_kernel':'NOT RUN'}
text=json.dumps(receipt,indent=2)+'\n'
if a.output is not None:
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(text)
print(text,end='')
