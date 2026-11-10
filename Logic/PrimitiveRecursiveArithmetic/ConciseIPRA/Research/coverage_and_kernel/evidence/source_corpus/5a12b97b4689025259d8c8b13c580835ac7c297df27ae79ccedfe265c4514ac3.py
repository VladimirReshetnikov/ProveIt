"""Public-interface verification of the boxed scalar kernel, outside trust."""
import json
from pathlib import Path
import sys
from validate_counter import metrics,negative_cases,run
from produce_scalar import ScalarEmitter,fixtures
import produce_counter

HERE=Path(__file__).resolve().parent

class UnboxedEmitter(ScalarEmitter):
    go=produce_counter.Emitter.go

def main():
    kernel=HERE/'kernel_scalar_boxed.py'
    positives=json.loads((HERE.parent/'fixtures/scalar_focused.json').read_text())['cases']
    negatives=negative_cases(positives)
    negatives.extend([
        dict(name='true_step_unboxed_zero_restricted',accept=False,packet=[[0,0,0,0],[[[0],0,[]],[]]]),
        dict(name='false_scalar_constant_update',accept=False,packet=[[0,0,0,0],[[[[]],[],[]],[[]]]]),
        dict(name='true_step_unboxed_variable_restricted',accept=False,packet=UnboxedEmitter().run(fixtures()['DI_progress_uses_hypothesis']))
    ])
    (HERE.parent/'fixtures/scalar_negative.json').write_text(json.dumps(dict(cases=negatives),indent=2)+'\n')
    results=[]
    for optimized in (False,True):
        for case in positives+negatives:
            result=run(kernel,case['packet'],optimized)
            passed=result['accept']==case['accept'] and not result['timeout']
            results.append(dict(name=case['name'],optimized=optimized,expected=case['accept'],passed=passed,**result))
    summary=dict(python=sys.version,check_count=len(results),passed=sum(x['passed'] for x in results),failures=[x for x in results if not x['passed']],metrics=metrics(kernel),checks=results,scope='Finite executable checks. The boxed-counter translation and scalar arithmetic completeness require the mathematical proofs in the report.')
    (HERE.parent/'evidence/implementation_scalar_validation.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k!='checks'},indent=2))
    if summary['failures']:raise SystemExit(1)

if __name__=='__main__':main()
