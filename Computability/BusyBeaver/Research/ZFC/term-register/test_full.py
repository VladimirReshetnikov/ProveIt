from pathlib import Path
import sys,argparse,json,time,hashlib,itertools,copy
from term_register import load_backend,word_code,code_word,seq
from full_program import FullProgram,execute_fast

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--frontend',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--max-length',type=int,default=10);a=ap.parse_args()
 if not __debug__:ap.error('assertions must remain enabled')
 sys.setrecursionlimit(15000)
 sys.path[:0]=[str(a.frontend),str(a.frontend/'source50/code')]
 import term_patterns as V,pattern_codec as B,test_patterns as T,symbolic254 as S,check_term254 as CT,test_circuits as TC
 start=time.monotonic();backend=load_backend(a.repo,a.output.parent/'backend');P=FullProgram(backend,T.TABLES);syntax=P.b.add_sequence(P.syntax());default=P.b.add_sequence(P.verify());print('control built',len(P.b.sequences),flush=True)
 specimens=[S.Raw(0),S.Raw(1,(0,),(S.Raw(0),S.Raw(0))),S.Raw(2,(1,),(S.Raw(0),))]
 specimens += [S.Raw(tag,tuple(range(S.ARITY[tag]))) for tag in range(3,11)]+[S.Raw(11,(0,1,2))]
 controls=[]
 for raw in specimens:
  term,goal=CT.convert_control(raw);cert=T.strip(TC.from_term(term));bits=B.encode(cert,T.TABLES)
  root=P.b.add_sequence(P.verify(control_goal=goal));controls.append((root,cert,goal,bits))
 P.b.reduce_to_cons()
 names={n:i for i,n in enumerate(P.names)}
 def run(root,bits,fast=True,initial=0):
  values=[initial]*len(P.names);values[names['candidate']]=word_code(bits)
  result=execute_fast(P,root,values,contract_macros=fast)
  assert result['control']==('normal',),result
  assert values[names['candidate']]==word_code(bits)
  return values[names['valid']],result,values
 # Full scan agrees on all small words; verify agrees on fixedF and trusted
 # controls. Short literal runs independently check every contracted helper.
 short=literal=0;ops=0
 for length in range(a.max_length+1):
  for bits in map(''.join,itertools.product('01',repeat=length)):
   parsed=B.decode(bits,T.TABLES);expected=int(parsed is not None)
   actual,result,values=run(syntax,bits,initial=7)
   assert actual==expected,('syntax',bits,actual,expected)
   accepted,_,_=run(default,bits,initial=7)
   assert accepted==int(B.accepts(bits,T.TABLES)),('verify',bits,accepted)
   if length<=5:
    slow,stats,slowvalues=run(syntax,bits,False,7)
    assert values==slowvalues,('literal_contract',bits,dict(zip(P.names,values)),dict(zip(P.names,slowvalues)))
    literal+=1;ops+=stats['literal_register_operations']
   short+=1
 print('small words PASS',short,literal,flush=True)
 measurements=[]
 for tag,(root,cert,goal,bits) in enumerate(controls):
  valid,result,_=run(root,bits,initial=7)
  assert valid==1,('positive',tag,len(bits),result)
  invalid,_,_=run(default,bits,initial=7);assert invalid==0,('fixedF',tag)
  measurements.append({'rule':tag,'bits':len(bits),'goal':goal,**result})
  print('rule',tag,'PASS',len(bits),result['structured_calls'],flush=True)
 # Every template small assignment tests alias0 and both bundle gates.
 import test_paths as TP,term_paths as Paths
 assignment_count=0
 for tag,pat in T.TABLES.items():
  for vals in itertools.product(range(3),repeat=pat.arity):
   arena=TP.ProducerArena();literalids=[0,arena.b(1,0,0),arena.b(2,0,0)];args=[literalids[x] for x in vals]
   out=arena.apply('bundle' if tag==11 else 'rho'+str(tag-2),args)
   row={'tag':tag,'args':args,'children':[],'formula':out}
   if tag==11:row['gate_paths']=[Paths.find_path(arena.nodes,args[2],args[j]) or [] for j in (0,1)]
   cert={'format':V.FORMAT,'nodes':arena.nodes,'proof_rows':[row]};bits=B.encode(cert,T.TABLES)
   root=P.b.add_sequence(P.verify(control_goal=out));P.b.reduce_to_cons()
   actual,_,_=run(root,bits)
   expected=int(V.verify_certificate(cert,T.TABLES,goal=out));assert actual==expected,('assignment',tag,vals,out,actual,expected)
   assignment_count+=1
  print('assignments',tag,'PASS',assignment_count,flush=True)
 record={'status':'PASS','scope':'Complete primitive-register control; finite tests use explicitly contracted local arithmetic loops. No compiler verification, TM execution endpoint or state reduction claim.','register_count':len(P.names),'registers':P.names,'small_words':short,'literal_contract_comparisons':literal,'literal_operations':ops,'all12_controls':measurements,'template_assignments':assignment_count,'elapsed_seconds':time.monotonic()-start,'source_sha256':{n:hashlib.sha256((Path(__file__).parent/n).read_bytes()).hexdigest() for n in ('term_register.py','full_program.py','test_full.py')}}
 a.output.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))

if __name__=='__main__':main()
