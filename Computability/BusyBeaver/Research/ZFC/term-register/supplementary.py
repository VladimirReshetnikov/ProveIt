from pathlib import Path
import argparse,sys,json,time,hashlib,itertools,copy
from term_register import *
from full_program import *

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--frontend',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 if not __debug__:ap.error('assertions enabled required')
 sys.setrecursionlimit(15000);sys.path[:0]=[str(a.frontend),str(a.frontend/'source50/code')]
 import test_patterns as T,pattern_codec as B,term_patterns as V,test_circuits as TC,check_term254 as CT,symbolic254 as S
 start=time.monotonic();P=FullProgram(load_backend(a.repo,a.output.parent/'backend'),T.TABLES);syntax=P.b.add_sequence(P.syntax());default=P.b.add_sequence(P.verify())
 positive=P.b.add_sequence(P.search(control_goal=0));P.b.reduce_to_cons();names={n:i for i,n in enumerate(P.names)}
 helpercases=0
 # Complete register-vector comparison, including dirty scratch. Helpers are
 # contracted only in one interpreter; the other literally executes everyop.
 for label,root,initials in [
  ('clear',P.clear('active'),[{'active':k} for k in range(9)]),
  ('move',P.move('active','minor'),[{'active':k,'minor':m} for k in range(5) for m in range(5)]),
  ('copy',P.copy('active','minor'),[{'active':k,'minor':m} for k in range(5) for m in range(5)]),
  ('lt',P.lt('active','minor'),[{'active':k,'minor':m} for k in range(9) for m in range(9)]),
  ('eq',P.eq('active','minor'),[{'active':k,'minor':m} for k in range(9) for m in range(9)]),
  ('pop',P.pop(),[{'cursor':k,'ok':ok} for k in range(130) for ok in (0,1)]),
  ('unary',P.unary('active'),[{'cursor':k,'ok':ok} for k in range(130) for ok in (0,1)]),
  ('fixed2',P.fixed2('active'),[{'cursor':k,'ok':ok} for k in range(130) for ok in (0,1)])]:
  P.b.reduce_to_cons()
  for init in initials:
   x=[7]*len(P.names)
   for n,v in init.items():x[names[n]]=v
   y=x.copy();ra=execute_fast(P,root,x,contract_macros=True);rb=execute_fast(P,root,y,contract_macros=False)
   assert ra['control']==rb['control'] and x==y,(label,init,dict(zip(P.names,x)),dict(zip(P.names,y)))
   helpercases+=1
 print('all helper contracts PASS',helpercases,flush=True)
 checked=0
 for length in range(13):
  for bits in map(''.join,itertools.product('01',repeat=length)):
   values=[0]*len(P.names);values[names['candidate']]=word_code(bits);r=execute_fast(P,syntax,values)
   assert r['control']==('normal',) and bool(values[names['valid']])==(B.decode(bits,T.TABLES) is not None),('syntax',bits)
   checked+=1
 print('full syntax allwords PASS',checked,flush=True)
 # All malformed suffixes remain checked, even when no semantic row references
 # the malformed object. They cannot be hidden behind selected ReadNode input.
 nat=lambda n:'1'*n+'0';tag=lambda n,w:format(n,'0'+str(w)+'b')
 malformed={
 'empty':'','truncated_unary':'111111','node_count':nat(8)+'0000','row_count':nat(0)+nat(8)+'00000',
 'unused_zero_alias':nat(1)+tag(0,2)+nat(0)+nat(0)+nat(1)+tag(0,4)+nat(0),
 'unused_forward_node':nat(1)+tag(1,2)+nat(1)+nat(0)+nat(1)+tag(0,4)+nat(0),
 'unknown_unused_last_rule':nat(0)+nat(2)+tag(0,4)+nat(0)+tag(12,4)+nat(0),
 'proof_forward':nat(0)+nat(1)+tag(2,4)+nat(0)+nat(0)+nat(0),
 'argument_reference':nat(0)+nat(1)+tag(2,4)+nat(1)+nat(0)+nat(0),
 'formula_reference':nat(0)+nat(1)+tag(0,4)+nat(1)}
 truth,goal=CT.convert_control(S.Raw(0));cert=T.strip(TC.from_term(truth));truthbits=B.encode(cert,T.TABLES)
 malformed['leftover']=truthbits+'0'
 for name,bits in malformed.items():
  assert B.decode(bits,T.TABLES) is None,name
  values=[0]*len(P.names);values[names['candidate']]=word_code(bits);r=execute_fast(P,syntax,values)
  assert r['control']==('normal',) and not values[names['valid']],name
 # Full blank zero-register scheduler with a compile-time positive control goal
 #0. The default compiled machine still has hardwired falsity; no endpoint is
 # taken from candidate data. Independently enumerate reference first match.
 first=None
 for candidate in range(1000):
  cert=B.decode(code_word(candidate),T.TABLES)
  if cert is not None and V.verify_certificate(cert,T.TABLES,goal=0):first=candidate;break
 assert first is not None
 values=[7]*len(P.names);run=execute_fast(P,positive,values)
 assert run['control']==('halt',) and values[names['candidate']]==first,(run,first,values[names['candidate']])
 record={'status':'PASS','helper_literal_contracted_complete_vector_cases':helpercases,'fullsyntax_words_maxlength':12,'fullsyntax_words':checked,'malformed_unused_suffixes':list(malformed),
 'scheduler_positive_control':{'trusted_goal':0,'first_word_code':first,'word':code_word(first),'actual_candidate':values[names['candidate']],**run},
 'scope':'finite helper loop-contract QA and full control tests. Positive scheduler uses trusted truth endpoint, separately from fixedF compiled table; no compiler equivalence proof.',
 'elapsed_seconds':time.monotonic()-start,'source_sha256':{n:hashlib.sha256((Path(__file__).parent/n).read_bytes()).hexdigest() for n in ('term_register.py','full_program.py','supplementary.py')}}
 a.output.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))

if __name__=='__main__':main()
