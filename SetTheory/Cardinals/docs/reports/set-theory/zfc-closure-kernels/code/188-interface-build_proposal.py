import sys
if not __debug__:
    raise SystemExit('Run without -O or -OO: source-audit assertions must remain enabled.')
from pathlib import Path
import json, hashlib, difflib
p=Path(__file__).parent
src={f:(p/'upstream'/f).read_text() for f in ('RMBisim.lean','RMNormalizedBisim.lean')}
def span(s,start,end):
 a=s.index(start); b=s.index(end,a); return a,b,s[a:b]
defs={}; proofs={}
for f,s in src.items():
 a,b,defs[f]=span(s,'def entryOk ','\n\n')
 a,b,proofs[f]=span(s,'theorem entryOk_good ','\n\n')
assert defs['RMBisim.lean']==defs['RMNormalizedBisim.lean']
body=lambda x:x.split(':= by\n',1)[1]
assert body(proofs['RMBisim.lean'])==body(proofs['RMNormalizedBisim.lean'])
common_def='''/-- Certificate entry checking is independent of the branch-check implementation. -/
def entryCheckWith (decode : Nat → List Bool) (t1 t2 : Tree)
    (branch : List Bool → List Bool → Nat → Bool) (x : Entry) : Bool :=
  match tsite t1 (decode x.1), tsite t2 (decode x.2.1) with
  | some (.halt, _), some (.halt, _) => true
  | some (.decnz r1, Q1), some (.decnz r2, Q2) =>
      Nat.beq r1 r2 && branch (incPath Q1) (incPath Q2) x.2.2.1 &&
        branch (breakPath 1 Q1) (breakPath 1 Q2) x.2.2.2
  | _, _ => false

theorem entryCheckWith_good (decode : Nat → List Bool)
    {t1 t2 : Tree} {S : List Bool → List Bool → Prop}
    (branch : List Bool → List Bool → Nat → Bool)
    (hbranch : ∀ {A B j}, branch A B j = true → BranchGood t1 t2 S A B)
    {x : Entry} (h : entryCheckWith decode t1 t2 branch x = true) :
    EntryGood t1 t2 S (decode x.1) (decode x.2.1) := by
'''+body(proofs['RMBisim.lean']).replace('unfold entryOk at h','unfold entryCheckWith at h').replace('branchOk_good decode hj','hbranch hj').replace('branchOk_good decode hk','hbranch hk')+'\n\n'
out={}
for f,s in src.items():
 newdef='''def entryOk (t1 t2 : Tree) (T : CTree) (x : Entry) : Bool :=
  entryCheckWith decode t1 t2 (branchOk decode t1 t2 T) x'''
 newproof=proofs[f].split(':= by',1)[0]+''':=
  entryCheckWith_good decode (branchOk decode t1 t2 T)
    (fun hb => branchOk_good decode hb) h'''
 s=s.replace(defs[f],newdef,1).replace(proofs[f],newproof,1)
 if f=='RMBisim.lean': s=s.replace('namespace WithDecoder\n',common_def+'namespace WithDecoder\n',1)
 out[f]=s
 (p/'proposed'/f).write_text(s)
patch=''.join(''.join(difflib.unified_diff(src[f].splitlines(True),out[f].splitlines(True),fromfile='a/'+f,tofile='b/'+f)) for f in src)
(p/'ENTRY_DISPATCH.patch').write_text(patch)
audit={'pin':'57541fe0cfe3af62b4cb58747d8d1d7c16b338d5','status':'static source audit; uncompiled proposal','identical_definition_lines':len(defs['RMBisim.lean'].splitlines()),'identical_proof_body_lines':len(body(proofs['RMBisim.lean']).splitlines()),'files':{f:{'before':len(src[f].splitlines()),'after':len(out[f].splitlines()),'sha256_snapshot':hashlib.sha256(src[f].encode()).hexdigest()} for f in src}}
audit['net_lines_removed']=sum(x['before']-x['after'] for x in audit['files'].values())
(p/'AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
print(json.dumps(audit,indent=2))
