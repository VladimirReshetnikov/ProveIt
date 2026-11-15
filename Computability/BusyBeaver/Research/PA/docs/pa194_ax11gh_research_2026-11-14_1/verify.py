#!/usr/bin/env python3
"""Replay the new protocol, source binding, and stored physical closure audit.

Default mode rechecks algebra, every source instruction, recorded certificate
closure, and novelty.  --full first reconstructs the tables with every source
contract and independently replays every literal tape case (this is slow).
Assertions must be enabled.  Only the Python standard library is required.
"""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys

ROOT=Path(__file__).resolve().parent
FAMILIES=('PA194AX11GH','PA194AX11GHS')
HASHES=(
 '513e9c8b28e0dd41e6003bb8d82c80ff3dac5fb3c5274cd2f709a3bba8c3e9e1',
 '7a4738a9eedd3f53674d67568b3197d38237d11d0fc08fa3d41251a8faf8052c')

def run(label,args):
    path=ROOT/'verification'/'logs'/f'{label}.log'
    path.parent.mkdir(parents=True,exist_ok=True)
    print(f'Running {label} ...',flush=True)
    with path.open('w') as out:
        p=subprocess.run([sys.executable,'-B',*map(str,args)],cwd=ROOT,
                         stdout=out,stderr=subprocess.STDOUT)
    if p.returncode:
        print(path.read_text(),flush=True)
        raise SystemExit(f'{label} failed; see {path}')
    print(f'PASS {label}',flush=True)

def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Run without -O: assertions are required.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full',action='store_true')
    a=ap.parse_args()
    if a.full:run('construction',['build.py','--full'])
    for family,h in zip(FAMILIES,HASHES):
        m=ROOT/'machines'/family
        assert hashlib.sha256((m/'machine.tm').read_bytes()).hexdigest()==h
        receipt=json.loads((m/'receipt.json').read_text())
        assert receipt['status']=='PASS' and receipt['full_construction_replay']
        run('commands_'+family,['verification/check_commands.py',
            '--machine',m,'--output',ROOT/'verification'/f'commands_{family}.json'])
        run('source_'+family,['verification/check_source_commands.py',
            '--machine',m,'--output',ROOT/'verification'/'source_commands'/family])
    if a.full:
        run('literal',['verification/check_literal.py',
            *(ROOT/'machines'/f for f in FAMILIES),
            '--output',ROOT/'verification'/'results'])
    run('physical_closure',['verification/physical_ipra_audit.py','--bundle',ROOT,
        '--output',ROOT/'verification'/'physical_ipra_receipt.json'])
    run('novelty',['verification/novelty_pair.py',
        *(ROOT/'machines'/f/'machine.tm' for f in FAMILIES),
        '--output',ROOT/'verification'/'novelty_pair_receipt.json'])
    result={'status':'PASS','mode':'full replay' if a.full else 'stored certificate audit',
      'machines':[{'family':f,'sha256':h} for f,h in zip(FAMILIES,HASHES)],
      'kernel_checked':False,
      'scope':'Finite machine checks and explicit symbolic/source obligations; written uniform proofs and inherited PA calibration are separate mathematical inputs.'}
    (ROOT/'verification'/'verification_summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()

