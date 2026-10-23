"""New negative/edge controls for the proposed oracle cut. No repository code runs."""
import importlib.util
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError('Optimization is unsupported; run without -O.')

D=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('owned_cut',D/'check_oracle_cut.py')
A=importlib.util.module_from_spec(spec)
spec.loader.exec_module(A)

def main():
    table=A.load_table();r=1
    cut=(0,False,(A.B(1),),(A.X('mark',r),))
    cases={}
    cases['exact_cut_accepts']=A.oracle_cut(cut,'CD',r)
    variants={
      'wrong_register':(0,False,cut[2],(A.X('mark',r+1),)),
      'wrong_state':(64,False,cut[2],cut[3]),
      'wrong_orientation':(0,True,cut[2],cut[3]),
      'unmarked_box':(0,False,cut[2],(A.X(),)),
      'extra_right_cell':(0,False,cut[2],cut[3]+(A.B(0),)),
    }
    for name,s in variants.items():cases[name+'_rejected']=not A.oracle_cut(s,'CD',r)
    stop=lambda s:A.oracle_cut(s,'CD',r)
    cases['false_progress_cannot_accept_empty_prefix']=A.execute(table,None,cut,stop,A.step,moved=False) is None
    cases['true_progress_accepts_reflexive_tail']=A.execute(table,None,cut,stop,A.step,moved=True)==(cut,[])
    altered=dict(table);altered[0,0]=(0,0,94)
    cases['neutral_failure_has_valid_fallback']=A.step(altered,None,cut) is not None
    cases['explicit_cut_precedes_fallback']=A.execute(altered,None,cut,stop,A.step,moved=True)==(cut,[])
    cases['wrong_branch_register_rejected']=A.step(table,(r+1,True),cut) is None
    require=lambda ok,msg:A.require(ok,msg)
    for name,ok in cases.items():require(ok,'Negative control failed: '+name)
    result={'status':'PASS','tests':cases,'scope':'Finite rejection and progress controls only; not a formal proof.'}
    (D/'ORACLE_CUT_CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
