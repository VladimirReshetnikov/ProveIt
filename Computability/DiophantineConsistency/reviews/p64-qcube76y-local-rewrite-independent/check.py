#!/usr/bin/env python3
"""Reproduce and independently validate bounded 76Y local-screen metadata."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent; research=here.parents[1]/'research'
packet=research/'p64-qcube76y-local-rewrite-search'; graph=research/'p64-qcube76-independent-y-candidate/graph.json'
pins={packet/'search.py':'3f6982c59a0148053ffa2b0e3f97b8267feff1e4eaeb0b2e645a439e91d32fea',
      packet/'result.json':'820e962b32d6759765b43122d2f91e94471a9d29a8c205079dfcc51882892b1b',
      graph:'196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in pins.items():
    if sha(p)!=h: raise RuntimeError('input hash drift: '+str(p))
proc=subprocess.run(['/usr/bin/ionice','-c','3',sys.executable,'-I','-S','-B',str(packet/'search.py')],
    stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60,preexec_fn=lambda:os.nice(19))
if proc.returncode!=0 or proc.stderr or proc.stdout!=(packet/'result.json').read_bytes():
    raise RuntimeError('screen rerun did not byte-match')
x=json.loads(proc.stdout);g=json.loads(graph.read_bytes());nvars=len(g['witnesses'])+len(g['fixed_numerals'])
if nvars!=18 or len(g['source'])!=76: raise RuntimeError('unexpected graph structure')
counts=x['exact_target']['counts']; expected_first=sum(2*n*n+n for n in range(nvars+5,nvars+5+76))
expected_second=sum(4*n-1 for n in range(nvars+5,nvars+5+76))
if counts['targets']!=76 or counts['first_gates']!=expected_first or counts['second_queries']!=expected_second:
    raise RuntimeError('derived counter mismatch')
if counts['square_root_queries']!=216 or counts['targets_with_sample_zero'] or counts['sample_zero_nonconstant']:
    raise RuntimeError('signature or square-root counter mismatch')
if x['exact_target']['one_gate_candidates'] or x['exact_target']['two_gate_candidates'] or x['extras']['aliases'] or x['extras']['square_only_negations']:
    raise RuntimeError('unexpected candidate in result')
if not any(v['target']=='__neg_two__' and v['live']==76 for v in x['positive_control']['one_gate_candidates']):
    raise RuntimeError('double-negation positive control missing')
if not any(v['target']=='b' and v['live']==3 and v['replacement']==['-',0,'x'] for v in x['square_sign_control']['square_only_negations']):
    raise RuntimeError('square-sign positive control missing')
result={'status':'PASS_BOUNDED_SCREEN_REVIEW','script_sha256':sha(Path(__file__)),
        'screen_sha256':pins[packet/'search.py'],'screen_result_sha256':pins[packet/'result.json'],'graph_sha256':pins[graph],
        'derived_first_gates':expected_first,'derived_second_queries':expected_second,'square_root_queries':216,
        'positive_controls':['double_negation','square_only_negation'],
        'scope':'Independent rerun and source/counter review of finite modular screen; no Lean or global lower bound.'}
out=here/'result.json'; payload=json.dumps(result,indent=2,sort_keys=True)+'\n'
if sys.argv[1:]==['--write']:
    with out.open('x') as f:f.write(payload)
elif sys.argv[1:]:raise SystemExit('usage: python3 -I -S -B check.py [--write]')
elif out.read_text()!=payload:raise SystemExit('result differs')
print(json.dumps(result,sort_keys=True))
