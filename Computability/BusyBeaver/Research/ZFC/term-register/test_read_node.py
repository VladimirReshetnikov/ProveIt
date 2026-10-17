from pathlib import Path
import argparse,hashlib,itertools,json,time
from term_register import *

def main():
 p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--max-length',type=int,default=8);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 if not __debug__:p.error('Keep assertions enabled')
 start=time.monotonic();backend=load_backend(a.repo,a.output.parent/'backend');P=Program(backend);root=P.read_node();b=P.b
 # Binaryize once so execution uses exactly the backend's Sequence nodes.
 b.reduce_to_cons()
 pop=P.b.add_sequence(P.pop());P.b.reduce_to_cons();popcases=0
 for n in range(130):
  vals=[0]*len(REGISTERS);vals[REGISTERS.index('cursor')]=n;vals[REGISTERS.index('ok')]=1
  r=execute(b,pop,vals);assert r['control']==('normal',)
  assert vals[REGISTERS.index('ok')]==int(n>0)
  assert vals[REGISTERS.index('cursor')]==((n-1)//2 if n else 0)
  assert vals[REGISTERS.index('bit')]==((n-1)%2 if n else 0);popcases+=1
 total=valid=failed=ops=maximum=0;representatives=[]
 for length in range(a.max_length+1):
  for bits in map(''.join,itertools.product('01',repeat=length)):
   code=word_code(bits);assert code_word(code)==bits
   for idx in range(4):
    values=[7]*len(REGISTERS);values[0]=code;values[1]=idx
    result=execute(b,root,values);assert result['control']==('normal',)
    actual={n:values[REGISTERS.index(n)] for n in ('ok','is_zero','tag','left','right','cursor')}
    expected=reference(bits,idx);assert actual==expected,(bits,idx,actual,expected)
    assert values[0]==code and values[1]==idx
    assert all(values[REGISTERS.index(n)]==0 for n in ('count','node_number','todo','cmp_a','cmp_b','quotient','bit','unary_loop','copy_scratch','less'))
    total+=1;valid+=actual['ok'];failed+=not actual['ok'];ops+=result['register_operations'];maximum=max(maximum,result['register_operations'])
    if idx==1 and actual['ok'] and len(representatives)<8:representatives.append({'word':bits,'index':idx,'output':actual})
 record={'status':'PASS','scope':'Actual inc/decrement selected-prefix ReadNode in existing Wade Sequence semantics. Not full structural parser, complete checker, TM state count or formal simulation.','registers':list(REGISTERS),'register_count':len(REGISTERS),'pop_contract_cases':popcases,'all_word_max_length':a.max_length,'word_codes_tested':2**(a.max_length+1)-1,'index_cases_per_word':4,'read_node_cases':total,'successful_prefix_reads':valid,'failed_prefix_reads':failed,'register_operations':ops,'max_register_operations_per_case':maximum,'elapsed_seconds':time.monotonic()-start,'representatives':representatives,'source_sha256':hashlib.sha256(Path(__file__).with_name('term_register.py').read_bytes()).hexdigest(),'complete_machine_compiled':False}
 a.output.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))

if __name__=='__main__':main()
