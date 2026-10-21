#!/usr/bin/env python3
"""Reproduce two failed restricted allocation models; no candidate is accepted.

Requires NumPy and SciPy. The engine filter is deliberately conditional:
state50 is removed and34/0 becomes0L75 without a new engine runtime proof.
The failed MILPs are not lower bounds for arbitrary machines or allocators.
"""
import argparse,json,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=False)
    lines=[]
    for line in (HERE/'allocation/k215.native.tm').read_text().splitlines():
        if line.startswith('50 '):continue
        lines.append('34 0 0 L 75'if line=='34 0 0 L 50'else line)
    table=a.output/'conditional_template.tm';table.write_text('\n'.join(lines)+'\n')
    e=json.loads((HERE/'allocation/engine-baseline.json').read_text());e['rows']=[k for k in e['rows']if k[0]!=50]
    e['status']='CONDITIONAL_SYNTHESIS_FILTER';e['scope']='Inherited engine rows minus50; modified34/0 and scanner sufficiency are unproved runtime obligations.'
    engine=a.output/'conditional_filter.json';engine.write_text(json.dumps(e,indent=2)+'\n')
    for name,extra in [('retained',[]),('global',['--global-pure'])]:
        command=[sys.executable,str(HERE/'allocation/code/allocate.py'),str(HERE/'sites_zero5_206.json'),str(a.output/name),'--drop','50','--table',str(table),'--engine',str(engine),'--limit','20',*extra]
        subprocess.run(command,check=True)
        result=json.loads((a.output/name/'allocation.json').read_text())
        assert result['status']==('EMPTY_DOMAIN'if name=='retained'else 'NO_ALLOCATION')
    print('Two restricted allocation failures reproduced; no binary state reduction established.')
if __name__=='__main__':main()
