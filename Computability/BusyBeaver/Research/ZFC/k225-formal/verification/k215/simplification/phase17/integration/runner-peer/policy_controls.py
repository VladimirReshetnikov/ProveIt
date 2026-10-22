"""Exercise extracted pure owned policy gates only; no reviewed top-level code executes."""
from pathlib import Path
import ast,json,hashlib,re,tempfile
D=Path(__file__).resolve().parent; helper=Path('/tmp/k215-phase17-plan/build.py');data=helper.read_bytes();tree=ast.parse(data)
functions={n.name:n for n in ast.walk(tree) if isinstance(n,ast.FunctionDef)}
needed=[functions['profiles'],functions['policy']]
mod=ast.fix_missing_locations(ast.Module(body=needed,type_ignores=[]))
space={'Path':Path,'re':re,'STD':{'propext','Classical.choice','Quot.sound'},'PATTERN':r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)"}
exec(compile(mod,str(helper)+' [only profiles and policy]','exec'),space)
with tempfile.TemporaryDirectory(prefix='phase17-owned-policy-') as td:
 p=Path(td)/'log';exact={'expected_reports':[['A',['Classical.choice','Quot.sound','propext']]],'warnings_forbidden':True}
 new={'expected_report_names':['A'],'allowed_report_axioms':['Classical.choice','Quot.sound','propext'],'warnings_forbidden':True}
 log="'A' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
 baseline={'status':'PASS','exit_code':0,'timed_out':False,'log':str(p)}
 cases=[('exact_positive',exact,baseline,log,True),('exact_smaller_rejected',exact,baseline,"'A' depends on axioms: [propext]\n",False),('added_axiom_rejected',exact,baseline,"'A' depends on axioms: [propext, Classical.choice, Quot.sound, cheat]\n",False),('sorry_rejected',exact,baseline,log+'sorryAx\n',False),('error_rejected',exact,baseline,log+'error: bad\n',False),('failure_rejected',exact,{**baseline,'status':'FAIL'},log,False),('exit_rejected',exact,{**baseline,'exit_code':1},log,False),('timeout_rejected',exact,{**baseline,'timed_out':True},log,False),('warning_rejected',exact,baseline,log+'warning: x\n',False),('missing_report_rejected',exact,baseline,'',False),('duplicate_report_rejected',exact,baseline,log+log,False),('unexpected_report_rejected',exact,baseline,log+"'B' does not depend on any axioms\n",False),('new_profile_positive',new,baseline,"'A' depends on axioms: [propext]\n",True),('new_wrong_name_rejected',new,baseline,"'B' depends on axioms: [propext]\n",False),('new_missing_name_rejected',new,baseline,'',False),('new_added_axiom_rejected',new,baseline,"'A' depends on axioms: [cheat]\n",False)]
 results=[]
 for name,row,rec,text,wanted in cases:
  p.write_text(text);got=space['policy'](row,rec);assert got is wanted,name
  results.append({'name':name,'expected_accept':wanted,'actual_accept':got})
 x={'status':'PASS_EXTRACTED_OWNED_POLICY_GATES_ONLY','helper_sha256':hashlib.sha256(data).hexdigest(),'positive_count':sum(x['expected_accept'] for x in results),'negative_count':sum(not x['expected_accept'] for x in results),'cases':results,'compiler_or_top_level_runner_invoked':False,'extraction':'ast.parse; execute only existing profiles and policy function definitions from the owned helper.'}
 (D/'policy-controls.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x,indent=2))
