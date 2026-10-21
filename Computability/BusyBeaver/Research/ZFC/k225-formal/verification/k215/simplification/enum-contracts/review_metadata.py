from pathlib import Path
import difflib,hashlib,json,re
p=Path(__file__).resolve().parent;old=(p/'EnumPerm.before.lean').read_text();full=(p/'EnumPerm.lean').read_text();new=full[:full.index('\n#print axioms')];(p/'EnumPerm.final.lean').write_text(new)
def strip(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;i+=2
  elif depth:i+=1
  elif s[i:i+2]=='--':
   i=s.find('\n',i)
   if i<0:break
  else:out.append(s[i]);i+=1
 return ''.join(out)
def decls(s):
 s=strip(s);matches=list(re.finditer(r"^(theorem|def|abbrev|structure|inductive) ([\w.']+)",s,re.M));r={}
 for j,m in enumerate(matches):
  text=s[m.start():matches[j+1].start() if j+1<len(matches) else len(s)]
  text=text.split('\nend ')[0]
  r[m[2]]=(m[1],text)
 return r
A,B=decls(old),decls(new);changed=[]
normalize=lambda s:re.sub(r'\s+',' ',s).strip()
for n,(kind,body) in A.items():
 assert n in B,n
 assert kind==B[n][0]
 newer=B[n][1]
 if kind=='theorem':
  head=lambda x:re.split(r'\s:=|\n  \|',x,maxsplit=1)[0]
  assert normalize(head(body))==normalize(head(newer)),n
  if normalize(body)!=normalize(newer):changed.append(n)
 else:assert normalize(body)==normalize(newer),(n,body,newer)
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
record={'status':'PASS','original_sha256':sha(p/'EnumPerm.before.lean'),'final_sha256':sha(p/'EnumPerm.final.lean'),'compiled_with_reports_sha256':sha(p/'run5/EnumPerm.lean'),'same_public_signatures':sorted(A),'all_existing_definitions_unchanged':True,'changed_proofs':changed,'new_helpers':sorted(set(B)-set(A)),'original_lines':len(old.splitlines()),'final_lines':len(new.splitlines()),'original_bytes':len(old.encode()),'final_bytes':len(new.encode()),'candidate_log_sha256':sha(p/'run5/compiler.log'),'baseline_log_sha256':sha(p/'run6/compiler.log'),'exact_axiom_reports_match':(p/'run5/compiler.log').read_bytes()==(p/'run6/compiler.log').read_bytes()};(p/'comparison.json').write_text(json.dumps(record,indent=2)+'\n');(p/'source.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='EnumPerm.before.lean',tofile='EnumPerm.final.lean')));print(json.dumps(record,indent=2))
