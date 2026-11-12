"""Raw exact-sequent proof translation and strict-input regression checks."""
import copy
import json
import pathlib
import subprocess
import sys
import raw_control
import matched_raw_control
import raw_two_case
import raw_examples
import raw_translate

ROOT=pathlib.Path(__file__).resolve().parent


def rejection_cases():
    r=lambda a:['r',a]
    ev=lambda p,q:['v',p,q]
    cases={
      'boolean_scalar':{'goal':[False,False],'proof':r(False)},
      'boolean_successor_tag':{'goal':[[False,0],[False,0]],'proof':r([False,0])},
      'float_scalar':{'goal':[0.0,0.0],'proof':r(0.0)},
      'free_parameter':{'goal':[-1,-1],'proof':r(-1)},
      'loose_bound_index':{'goal':[1,1],'proof':r(1)},
      'wrong_successor_tag':{'goal':[[1,0],[1,0]],'proof':r([1,0])},
      'nonexistent_clause':{'goal':[0,0],'proof':['u',0,0,r(0)]},
      'negative_clause_index':{'goal':[0,0],'proof':['u',-1,0,r(0)]},
      'boolean_clause_index':{'goal':[0,0],'proof':['u',False,0,r(0)]},
      'extra_argument':{'goal':[0,0],'proof':['r',0,0]},
      'unknown_rule':{'goal':[0,0],'proof':['unknown']},
      'wrong_goal':{'goal':[0,[0,0]],'proof':r(0)},
      'eval_wrong_zero_source':{'goal':[0,0],'proof':ev(r([0,0]),r([0,0,1]))},
      'eval_successor_as_iterator':{'goal':[0,0],'proof':ev(r(0),r([0,0]))},
      'di_witness_escape':{'goal':[[0,0]],'proof':['i',[[0,0]],-1,r(0)]},
      'counter_variable_is_not_successor':{'goal':[[0,0]],'proof':['i',[[0,0]],0,ev(r(0),r([-1,0,1]))]},
    }
    c=[0,0,1];s=[0,0,[0,1]];b=[c,0,[0,1]]
    cases['iterator_counter_is_not_successor']={'goal':[b,[0,s]],'proof':ev(r(s),r(b))}
    for value in (None,[],False,{}, {'goal':[0,0]}, {'proof':r(0)}, {'goal':[0,0],'proof':r(0),'extra':0}):
        cases['malformed_'+str(len(cases))]=value
    return cases


def run():
    originals=raw_examples.examples()
    # Ensure a direct root branch is present even if the inherited generator changes.
    originals['direct_root']={'goal':[0,0],'proof':['v',['r',0],['r',0]]}
    translated={}
    node_data=[]
    for name,c in originals.items():
        raw_control.verify(c);matched_raw_control.verify(c)
        t=raw_translate.compile_certificate(c)
        raw_control.verify(t);matched_raw_control.verify(t)
        if t['goal']!=c['goal']:raise RuntimeError('end-sequent change')
        before=raw_translate.count_nodes(c['proof'])
        roots=raw_translate.count_roots(c['proof'])
        after=raw_translate.count_nodes(t['proof'])
        if after!=before+2*roots:raise RuntimeError('node count mismatch')
        translated[name]=t
        node_data.append({'case':name,'before':before,'root_nodes':roots,'after':after})
    negatives=rejection_cases()
    # Invalid in the reduced interface, but valid in the old one.
    negatives['removed_root_opcode_shape']=originals['direct_root']
    d=copy.deepcopy(translated['used_induction_hypothesis'])
    d['proof'][2]=[0,0]
    negatives['progress_cannot_be_retagged_as_cases']=d
    d=copy.deepcopy(translated['used_induction_hypothesis'])
    d['goal']=[0,0];d['proof']=['e',[0,0],d['proof'],['r',-1]]
    negatives['de_eigenvariable_escape']=d
    for name,c in negatives.items():
        try:raw_two_case.verify(c)
        except Exception:pass
        else:raise RuntimeError('unexpected accept '+name)
    process_count=0
    for name,c in list(translated.items())+list(negatives.items()):
        expected=name in translated
        for flag in ([],['-O']):
            p=subprocess.run([sys.executable,*flag,str(ROOT/'raw_two_case.py')],input=json.dumps(c),capture_output=True,text=True)
            accepted=p.returncode==0 and p.stdout.strip()=='ACCEPT'
            if accepted!=expected:raise RuntimeError((name,p.returncode,p.stdout,p.stderr))
            process_count+=1
    folder=ROOT/'raw_certificates';folder.mkdir(exist_ok=True)
    for name,c in translated.items():(folder/(name+'.json')).write_text(json.dumps(c,indent=2)+'\n')
    report={'positive_certificates':len(translated),'negative_certificates':len(negatives),'exact_sequent_translations':len(translated),'reverse_inclusions':len(translated),'process_checks':process_count,'node_overhead_checks':len(node_data),'unexpected_outcomes':0,'node_data':node_data}
    (ROOT/'raw_validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='node_data'},indent=2))


if __name__=='__main__':run()
