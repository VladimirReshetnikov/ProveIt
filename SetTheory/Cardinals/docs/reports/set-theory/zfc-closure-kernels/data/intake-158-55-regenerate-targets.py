from pathlib import Path
import json, sys, time
root=Path('/tmp/zfc-intake-158/run-55-countdown')
sys.path.insert(0,str(root/'loop_experiments'))
import affine_reference_loops as loops
reference=json.loads((root/'binary_loop_experiments/remaining_cases/matrix_reference_targets.json').read_text())
start=time.monotonic()
fresh=loops.raw_targets([int(i) for i in reference['cases']])
normalized=json.loads(json.dumps(fresh))
assert normalized['cases']==reference['cases']
receipt={'status':'PASS','selected_cases':len(reference['cases']),'target_count':sum(len(v['targets']) for v in reference['cases'].values()),'comparison':'all selected cases and every regenerated raw matrix frontier field equal retained cases reference','seconds':time.monotonic()-start,'scope':'source matrix targets only; no binary search or proof assistant'}
Path('/tmp/zfc-intake-158/replay-55-countdown/target-regeneration.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
