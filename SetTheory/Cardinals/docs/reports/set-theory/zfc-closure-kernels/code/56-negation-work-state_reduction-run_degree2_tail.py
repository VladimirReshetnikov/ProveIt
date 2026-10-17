#!/usr/bin/env python3
"""Run previously untouched degree-two domains with full incoming actions."""
import json
from pathlib import Path
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
# Source50's archived run touched none of these domains. State143 was completed
# separately in this session. Each domain contains 1008^2 concrete recipes.
STATES=[252,250,245,243,240,235,215,212,193,192,188,180,179,177,176,
        167,166,161,154,153,152,151,149,127,125,122,98,92,89,82,81,79,78,72]

def main():
    started=time.monotonic();done=[]
    for q in STATES:
        path=HERE/f'two_action_{q}_gap.json'
        if path.exists() and json.loads(path.read_text())['status']=='completed':
            result=json.loads(path.read_text())
        else:
            completed=subprocess.run([sys.executable,'-B',str(HERE/'two_action_search.py'),
                                      '--dead',str(q),'--gap-flexible','--seconds','900'],check=True)
            result=json.loads(path.read_text())
        done.append(result)
        aggregate=dict(scope='Previously untouched source50 two-incoming full-action domains, now using an output-gap-flexible sufficient contract.',
                       completed=[r['dead'] for r in done if r['status']=='completed'],
                       partial=[r['dead'] for r in done if r['status']!='completed'],
                       planned=sum(r['planned'] for r in done),pruned=sum(r['pruned'] for r in done),
                       remaining=sum(r['remaining'] for r in done),survivors=[x for r in done for x in r['survivors']],
                       evaluated_nodes=sum(r['evaluated_nodes'] for r in done),
                       checks=sum(r['checks'] for r in done),elapsed_seconds=time.monotonic()-started,
                       not_started=[s for s in STATES if s not in {r['dead'] for r in done}])
        (HERE/'degree2_tail_summary.json').write_text(json.dumps(aggregate,indent=2)+'\n')
        print('TAIL SUMMARY',json.dumps(aggregate),flush=True)
        if result['survivors']:break

if __name__=='__main__':main()
