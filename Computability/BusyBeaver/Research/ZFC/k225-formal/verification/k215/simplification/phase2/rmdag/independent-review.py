from pathlib import Path
import hashlib,json,re
p=Path('/tmp/k215-concision-round2/root');o=Path(__file__).resolve().parent
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
old=(p/'RMDag.before.lean').read_text();new=(p/'RMDag.final.lean').read_text()
def remove_comments(s):
 out=[];depth=0;i=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;i+=2
  elif depth:i+=1
  elif s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:out.append(s[i]);i+=1
 return ''.join(out)
def parts(s):
 s=remove_comments(s);a=s.index('theorem run_det');b=s.index('variable {p : Prog}',a);return s[:a],s[a:b],s[b:]
a,b=parts(old),parts(new);norm=lambda s:re.sub(r'\s+',' ',s).strip();assert norm(a[0])==norm(b[0]) and norm(a[2])==norm(b[2]);assert norm(a[1].split(':=')[0])==norm(b[1].split(':=')[0]);assert not any(t in b[1] for t in ['grind','sorry','admit','native_decide','axiom '])
r7=json.loads((p/'run007/result.json').read_text());assert r7['status']=='PASS' and r7['source_sha256']==sha(p/'RMDag.final.lean');assert sha(p/'run007/compiler.log')==r7['log_sha256']
r6=json.loads((p/'run006/result.json').read_text());assert r6['status']=='PASS';assert "depends on axioms: [propext]" in (p/'run006/compiler.log').read_text()
record={'status':'PASS_SOURCE_AND_SAVED_EVIDENCE_PEER','reviewer':'opening_encoder','authorship':'Independent source review; no authorship of this RMDag refactor and no compiler invocation.','original_sha256':sha(p/'RMDag.before.lean'),'final_sha256':sha(p/'RMDag.final.lean'),'all_other_source_code_unchanged':True,'run_det_statement_unchanged':True,'ordinary_checks':['Atomic instruction inversions are unchanged, including decPos/decZero exclusion and equal predecessor values.','All four non-normal car cases use the car induction hypothesis; normal-car competitors contradict its exit, while equal car exits align registers and determine the node exit.','The four non-restarting cdr cases first align intermediate registers using the normal-car induction hypothesis, then compare cdr exits/registers. A cdrCont1 competitor contradicts normal/brk/cont(k+2)/halt.','The restarting cdrCont1 case aligns both intermediate states before invoking the strictly smaller restarted-run induction hypothesis. Other car/cdr shapes are excluded by the corresponding exit equality.','Break and continue counters retain their original one-level consumption rules; no termination assumption or infinite-run claim is introduced.','first/rename_i select proof branches only; all branches are ordinary equality elimination, constructor disjointness and induction hypotheses.'], 'run006_axiom_report':'[propext]','run006_record_sha256':sha(p/'run006/result.json'),'run007_record_sha256':sha(p/'run007/result.json'),'run007_final_source_pass':True,'findings':[]};(o/'review.json').write_text(json.dumps(record,indent=2)+'\n');print(sha(o/'review.json'))
