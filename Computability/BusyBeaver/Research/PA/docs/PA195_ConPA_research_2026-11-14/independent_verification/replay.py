#!/usr/bin/env python3
"""Replay bounded reduction searches; --full rederives symbolic source coverage.

Default: reproduce one-helper, two-keeper-row, and bypass searches from the
recorded context certificates. --extended also replays two arbitrary helpers.
--full recomputes the context certificates from every source contract first.
"""
from pathlib import Path
import argparse,subprocess,hashlib,json,shutil,sys
HERE=Path(__file__).resolve().parent

def run(args):
    p=subprocess.run([str(x)for x in args],check=True,text=True,capture_output=True)
    return p.stdout.strip()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full',action='store_true')
    ap.add_argument('--extended',action='store_true')
    a=ap.parse_args()
    manifest=json.loads((HERE/'MANIFEST.json').read_text())
    for rel,expected in manifest['sha256'].items():
        assert hashlib.sha256((HERE/rel).read_bytes()).hexdigest()==expected,('Manifest mismatch',rel)
    for name in ['scan_helper','scan_two_rows','scan_two_helper','scan_bypass','scan_pair_bypass','scan_stutter_bypass']:
        run(['g++','-O3','-std=c++17','-Wall','-Wextra','-Werror',HERE/(name+'.cpp'),'-o',HERE/name])
    run([sys.executable,HERE/'check_bypass.py'])
    run([sys.executable,HERE/'check_composite_commands.py'])
    run([sys.executable,HERE/'check_composite_binding.py'])
    reports=[]
    for family in ['diagonal196','separate196']:
        reference=HERE/'recorded'/family
        old=json.loads((reference/'receipt.json').read_text())
        assert hashlib.sha256((HERE/'inputs'/family/'machine.native.tm').read_bytes()).hexdigest()==old['native_sha256']
        assert hashlib.sha256((reference/'contexts.txt').read_bytes()).hexdigest()==old['context_sha256']
        work=HERE/'results'/family;work.mkdir(parents=True,exist_ok=True)
        if a.full:
            subprocess.run([sys.executable,HERE/'source_contexts.py',family],check=True)
            now=json.loads((work/'receipt.json').read_text())
            assert now==old,'Recomputed source-context receipt differs'
        else:
            for n in ['table.txt','contexts.txt']:shutil.copy2(reference/n,work/n)
        counters={}
        for tool in ['scan_helper','scan_two_rows']+(['scan_two_helper'] if a.extended or a.full else []):
            counters[tool]=run([HERE/tool,work/'table.txt',work/'contexts.txt',work/(tool+'.txt'),'196'])
            assert 'survivors 0' in counters[tool] or 'passes 0' in counters[tool]
            if tool=='scan_helper':
                words=counters[tool].split();actual=dict(zip(words[::2],map(int,words[1::2])))
                assert actual==old['screen']
            if tool=='scan_two_helper':assert not(work/(tool+'.txt')).read_text()
        run([sys.executable,HERE/'wide_contexts.py',work])
        counters['bypass9']=run([HERE/'scan_bypass',work/'table.txt',work/'contexts9.txt',work/'bypass9.txt','196','4'])
        counters['pair_bypass9']=run([HERE/'scan_pair_bypass',work/'table.txt',work/'contexts9.txt',work/'pair_bypass9.txt','196','4'])
        counters['stutter_bypass9']=run([HERE/'scan_stutter_bypass',work/'table.txt',work/'contexts9.txt',work/'stutter_bypass9.txt','196','4'])
        assert all('survivors 0' in counters[k] for k in ['bypass9','pair_bypass9','stutter_bypass9'])
        report=dict(family=family,recomputed_source_contexts=a.full,counters=counters)
        reports.append(report);print(json.dumps(report,indent=2),flush=True)
    (HERE/'results/replay.json').write_text(json.dumps(reports,indent=2)+'\n')

if __name__=='__main__':main()
