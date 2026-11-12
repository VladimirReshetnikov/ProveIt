"""Targeted validation for the exact-zero-base companion."""
import copy
import json
import subprocess
import sys
import validate as shared
import zero_base as new
from zero_base_translate import translate

ROOT=shared.ROOT


def run():
    pos=shared.positives()
    # The induction hypothesis is genuinely used at a nonzero witness.
    p=copy.deepcopy(pos['used_equation_induction'])
    p['proof'][2]=shared.S(0)
    pos['nonzero_witness_used_progress']=p
    # A zero witness with nonzero reflexive base must select cases, and the
    # branch genuinely needs the exact base equation 1=1.
    one=shared.S(0)
    b=shared.I(shared.S(-1),one,one)
    predecessor=shared.I(-1,one,one)
    computation=shared.EV(shared.R(predecessor),shared.R(b))
    base_hyp=['u',0,0,shared.R(0)]
    actual_base=shared.identity_root(base_hyp,shared.R(one),one)
    step=shared.transitivity(computation,actual_base,b,one)
    goal=[[shared.I(1,one,one),one]]
    pos['zero_witness_nonzero_base_case']={'goal':goal,'proof':['i',goal,0,step]}
    negatives=shared.negatives(shared.positives())
    # Reusing an equation-progress proof for this nonzero-base matrix fails.
    matrix=[shared.I(1,one,1),one]
    progress_step=shared.EV(['u',0,0,shared.R(0)],shared.R(shared.I(shared.S(-1),one,1)))
    negatives['nonzero_base_cannot_use_progress']={'goal':[matrix],'proof':['i',[matrix],0,progress_step]}
    folder=ROOT/'zero_base_certificates';folder.mkdir(exist_ok=True)
    for name,c in pos.items():
        new.verify(c)
        dest=translate(c)
        (folder/(name+'.json')).write_text(json.dumps(c,indent=2)+'\n')
        (folder/(name+'.native_seven.json')).write_text(json.dumps(dest,indent=2)+'\n')
    count=0
    for name,c in list(pos.items())+list(negatives.items()):
        expected=name in pos
        for flag in ([],['-O']):
            run=subprocess.run([sys.executable,*flag,str(ROOT/'zero_base.py')],input=json.dumps(c),capture_output=True,text=True)
            accepted=run.returncode==0 and run.stdout.strip()=='ACCEPT'
            if accepted!=expected:raise RuntimeError((name,flag,run.returncode,run.stdout,run.stderr))
            count+=1
    out={'positive_certificates':len(pos),'negative_certificates':len(negatives),'native_seven_translations':len(pos),'process_checks':count,'unexpected_outcomes':0}
    (ROOT/'zero_base_validation.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__=='__main__':run()
