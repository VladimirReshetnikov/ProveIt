"""Independent hand-constructed controls for the successor-R byte kernel."""
import json
import subprocess
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
KERNEL = ROOT / 'successor_variant/code/kernel_bytes.py'
COMP = [0, 0, 0, 0]
rows = []
def check(name, packet, expected):
    p = subprocess.run([sys.executable, '-I', '-S', str(KERNEL)],
                       input=json.dumps(packet), text=True, capture_output=True, timeout=10)
    accepted = p.returncode == 0 and p.stdout == 'ACCEPT\n'
    rejected = p.returncode != 0 and p.stdout == 'REJECT\n'
    if not (accepted if expected else rejected):
        raise RuntimeError((name, expected, p.stdout, p.stderr))
    rows.append({'name':name, 'expected_accept':expected, 'accepted':accepted, 'packet':packet})
def axiom(name, n, seed, body, output, accepted=True):
    check(name, [COMP, [[n, seed, body], output]], accepted)
nums = [0, [0], [[0]]]
for j, seed in enumerate(nums):
    for n in (0, 0.0, False, []):
        axiom('zero_alias_seed_'+str(j)+'_'+repr(n),n,seed,3,[seed])
    for jn, n in enumerate(nums):
        axiom('counter_'+str(j)+'_'+str(jn),[n],seed,3,n)
        axiom('counter_alias_'+str(j)+'_'+str(jn),[n],seed,4,n)
        for body in (1, 2):
            axiom('state_'+str(j)+'_'+str(jn)+'_'+str(body),[n],seed,body,[n,seed,body])
        axiom('nested_counter_'+str(j)+'_'+str(jn),[n],seed,[5],[n])
        axiom('nested_state_'+str(j)+'_'+str(jn),[n],seed,[3],[[n,seed,[3]]])
        axiom('recursor_protects_counter_'+str(j)+'_'+str(jn),[n],seed,[7,0,1],[n,0,1])
        axiom('recursor_protects_state_'+str(j)+'_'+str(jn),[n],seed,[5,0,1],[[n,seed,[5,0,1]],0,1])
for n in ([0,0], [0,0,0], 1, True, 0.5, {}, '', {'':0}, None, [None], [''], [[0,0,0,0]], float('nan'),float('inf')):
    for body in (0,1,3):
        axiom('malformed_counter_'+repr(n)+'_'+str(body), n, [0], body, 0, False)
for t in nums+[[[0],0,3]]:
    r=[[t],0,3]
    major=[r,t]
    packet=[COMP,COMP,[major,r,t,[1,t]],[t,t]]
    check('R_reflexivity_'+repr(t),packet,True)
    wrong=[COMP,COMP,[major,r,t,[1,t]],[t,[t]]]
    check('R_reflexivity_wrong_target_'+repr(t),wrong,False)
# Introduce D_xy(y=y), then prove its successor equation using R-based reflexivity.
t=[-1]; r=[[t],0,3]; major=[r,t]
check('R_reflexivity_inside_DI', [COMP,COMP,[major,r,t,[1,t]],[[],0,0,[0]],[0,0,[1,1]]],True)
# Non-vacuous zero-valued witness R(S0,0;u,v.u) used in D_xy(x=x).
wbox=[[0],0,3]; r=[[wbox],0,3]; major=[r,wbox]
check('R_zero_box_nonvacuous_DI', [COMP,COMP,[major,r,wbox,[1,wbox]],[[],0,0,wbox],[0,0,[3,3]]],True)
(ROOT/'audits/r_focused_independent_results.json').write_text(json.dumps({'status':'PASS','count':len(rows),'cases':rows},indent=2)+'\n')
print('PASS',len(rows),'independent R controls')
