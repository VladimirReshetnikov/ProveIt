"""Create bounded scratch inlining candidates, never execute a proof producer."""
from pathlib import Path
import re,json,hashlib,difflib
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs');OUT=Path(__file__).resolve().parent
B=ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC';C=OUT/'candidate';C.mkdir(exist_ok=True)
def digest(b):return hashlib.sha256(b).hexdigest()
def once(s,a,b):assert s.count(a)==1,(a,s.count(a));return s.replace(a,b)
name='KHomeReady.lean';old=(B/name).read_text();new=old
helper='''private theorem rowsCheck_sound {M : TMN} (h : rowsCheck M = true) : KHome.Rows M := by
  simp only [rowsCheck, Bool.and_eq_true, List.all_eq_true] at h
  constructor
  · intro i hi
    exact of_decide_eq_true (h.1 i (List.mem_range.mpr hi))
  · intro i hi
    exact of_decide_eq_true (h.2 i (List.mem_range.mpr (by omega)))

'''
new=once(new,helper,'')
new=once(new,'  exact ⟨rowsCheck_sound h.1, boundary_of_check h.2⟩','''  refine ⟨?_, boundary_of_check h.2⟩
  have hr := h.1
  simp only [rowsCheck, Bool.and_eq_true, List.all_eq_true] at hr
  constructor
  · intro i hi
    exact of_decide_eq_true (hr.1 i (List.mem_range.mpr hi))
  · intro i hi
    exact of_decide_eq_true (hr.2 i (List.mem_range.mpr (by omega)))''')
(C/name).write_text(new)
(OUT/(name+'.diff')).write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='baseline/'+name,tofile='candidate/'+name)))
name='DominatedImplication.lean';old=(B/name).read_text();new=old
items=[
 ('b12','''private theorem b12 (v0 : A) : T (wim (wim (wim v0 v0) v0) (wim v0 v0)) :=
  (h.mp (b10 h τ v0) h.truth)

''','(b12 h v0)','(h.mp (b10 h τ v0) h.truth)'),
 ('b15','''private theorem b15 (v0 : A) : T (wim (wim v0 v0) (wim v0 v0)) :=
  (h.mp (b14 h τ v0) h.truth)

''','(b15 h v1)','(h.mp (b14 h τ v1) h.truth)'),
 ('b60','''private theorem b60 (v0 v1 : A) : T (wim v0 (wim v1 v0)) :=
  (h.mp (b22 h v0 (wim v1 v0) v0) (b18 h v0 (wim v1 v0) v1))

''','private theorem basisK (a b : A) : T (wim a (wim b a)) := b60 h a b','''private theorem basisK (a b : A) : T (wim a (wim b a)) :=
  h.mp (b22 h a (wim b a) a) (b18 h a (wim b a) b)''')]
for n,block,call,replacement in items:
 assert len(re.findall(r'\b'+n+r'\b',new))==2,n
 new=once(new,block,'');new=once(new,call,replacement)
(C/name).write_text(new)
(OUT/(name+'.diff')).write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='baseline/'+name,tofile='candidate/'+name)))
# Parse exact byte spans of declarations. No arithmetic/definition body changes;
# only selected private proof deletions and selected retained proof-body changes.
pat=re.compile(r'^(?P<private>private\s+)?(?P<kind>theorem|lemma|def|abbrev|structure|inductive)\s+(?P<name>[\w.]+)\b',re.M)
def declarations(s):
 ms=list(pat.finditer(s));out={}
 for i,m in enumerate(ms):
  text=s[m.start():ms[i+1].start()if i+1<len(ms)else len(s)]
  end=re.search(r'^(?:end|namespace|section|#print|attribute|open|variable|include|omit|set_option)\b',text,re.M)
  if end:text=text[:end.start()]
  # Trim only inter-declaration comments/whitespace, preserving the actual body.
  text=re.sub(r'/\-[\s\S]*?\-/','',text).strip()
  out[m['name']]=dict(private=bool(m['private']),kind=m['kind'],text=text,header=text.split(':=',1)[0].strip())
 return out
records=[]
for name,removed,changed in [('KHomeReady.lean',{'rowsCheck_sound'},{'ready_sound'}),('DominatedImplication.lean',{'b12','b15','b60'},{'b13','b16','basisK'})]:
 old=(B/name).read_text();new=(C/name).read_text();a,b=declarations(old),declarations(new)
 assert set(a)-set(b)==removed and not(set(b)-set(a))
 assert all(a[n]['private'] for n in removed)
 for n in b:
  assert a[n]['header']==b[n]['header'],(name,n,'header')
  if n not in changed:assert a[n]['text']==b[n]['text'],(name,n,'body')
 assert [(n,x['text'])for n,x in a.items()if x['kind']not in('theorem','lemma')]==[(n,x['text'])for n,x in b.items()if x['kind']not in('theorem','lemma')]
 assert re.findall(r'^import .*$',old,re.M)==re.findall(r'^import .*$',new,re.M)
 assert re.findall(r'^#print axioms .*$',old,re.M)==re.findall(r'^#print axioms .*$',new,re.M)
 records.append(dict(file=name,before_sha256=digest(old.encode()),after_sha256=digest(new.encode()),before_bytes=len(old.encode()),after_bytes=len(new.encode()),before_lines=len(old.splitlines()),after_lines=len(new.splitlines()),removed_private=sorted(removed),changed_retained_proofs=sorted(changed),unchanged_public_headers=sum(not x['private']for x in b.values()),unchanged_executable_definitions=sum(x['kind']not in('theorem','lemma')for x in b.values())))
(OUT/'candidate-control.json').write_text(json.dumps(dict(status='PASS_SOURCE_ONLY_EXACT_API_AND_DEFINITION_CONTROL',records=records,total_byte_saving=sum(x['before_bytes']-x['after_bytes']for x in records),total_line_saving=sum(x['before_lines']-x['after_lines']for x in records),compiler_invocations=[],proof_producer_invocations=[],canonical_mutations=[]),indent=2)+'\n')
print(json.dumps(records,indent=2))
