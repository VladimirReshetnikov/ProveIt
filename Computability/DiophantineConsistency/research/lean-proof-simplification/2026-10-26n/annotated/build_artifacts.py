from pathlib import Path
import difflib, json, hashlib
root=Path(__file__).resolve().parent.parent
base=root/'sources/Computability/DiophantineConsistency/Lean/DiophantineConsistency'
out=root/'annotated'
candidate=(out/'AnnotatedCandidates.lean').read_text()
def section(s,a,b): return s[s.index(a):s.index(b)]
raw_body=section(candidate,'  constructor\n','\nend DiophantineConsistency.AnnotatedParents').rstrip()+'\n'
spec=section(candidate,'theorem decode_spec_short','\n/-- Optional public API:').replace('decode_spec_short','decode_spec').replace('decoded_depth_le_short','decoded_depth_le').replace('quote_of_decode_short','quote_of_decode').rstrip()+'\n'
raw_old=(base/'AnnotatedParents.lean').read_text()
a=raw_old.index('theorem check_raw_iff '); b=raw_old.index('\nattribute [local irreducible] check',a)
old_raw=raw_old[a:b].rstrip()+'\n'
header=old_raw[:old_raw.index(' := by')+len(' := by')]+'\n'
new_raw=header+raw_body
raw_new=raw_old[:a]+new_raw+raw_old[b:]
dec_old=(base/'AnnotatedProofCode.lean').read_text()
a=dec_old.index('theorem decoded_depth_le '); b=dec_old.index('\ntheorem quote_injective',a)
old_dec=dec_old[a:b].rstrip()+'\n'
dec_new=dec_old[:a]+spec+dec_old[b:]
patch=''
for name,old,new in [('AnnotatedParents.lean',raw_old,raw_new),('AnnotatedProofCode.lean',dec_old,dec_new)]:
 path='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+name
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
(out/'proposed.patch').write_text(patch)
def metric(old,new):
 return {'old_nonblank_declaration_lines':sum(bool(x.strip()) for x in old.splitlines()),'new_nonblank_declaration_lines':sum(bool(x.strip()) for x in new.splitlines()),'old_utf8_bytes':len(old.encode()),'new_utf8_bytes':len(new.encode()),'old_lines':len(old.splitlines()),'new_lines':len(new.splitlines())}
metrics={'pinned_commit':'b310142330df89e48413c8fce62e7de223e1c7d5','validation':'static only, uncompiled','counts_note':'Whole replaced declarations including signatures, excluding separating blank lines for nonblank counts. Optional decode_eq_some_iff theorem excluded from patch and counts. UTF-8 bytes are text size, not kernel proof size.','check_raw_iff':metric(old_raw,new_raw),'decoder_spec_with_both_wrappers':metric(old_dec,spec),'source_sha256':{n:hashlib.sha256((base/n).read_bytes()).hexdigest() for n in ['AnnotatedParents.lean','AnnotatedProofCode.lean']}}
(out/'static_metrics.json').write_text(json.dumps(metrics,indent=2)+'\n')
print(json.dumps(metrics,indent=2))
