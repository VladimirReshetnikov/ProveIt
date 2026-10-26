#!/usr/bin/env python3
"""Validate captured #print axioms messages against an explicit endpoint list.

Usage: python check_axiom_log.py lean.stdout --expected expected_endpoints.txt
The expected file has one fully qualified theorem name per line (# comments
allowed). Every expected theorem must be seen; unknown axiom names fail closed.
Only checks supplied logs: a zero exit code does NOT establish that Lean was
run successfully, that logs are authentic, or that all intended targets exist.
Keep the Lean process exit code, command, versions, commit, and source hashes.
"""
import argparse, json, re
from pathlib import Path
ALLOWED={'propext','Classical.choice','Quot.sound'}
PAT=re.compile(r"'([^\n]+?)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",re.M)

def check(log, expected):
    observed={}; errors=[]; spans=[]
    for m in PAT.finditer(log):
        spans.append(m.span())
        name=m.group(1); body=m.group(2)
        if body is None or not body.strip():
            ax=set()
        else:
            pieces=[x.strip() for x in body.split(',')]
            if any(not x or re.search(r'\s',x) for x in pieces):
                errors.append(f'{name}: malformed axiom list')
            ax=set(pieces)
        observed.setdefault(name,set()).update(ax)
        bad=sorted(ax-ALLOWED)
        if bad: errors.append(f'{name}: forbidden axiom(s): '+', '.join(bad))
    for marker in re.finditer(r'\bdepends on axioms\b|\bdoes not depend on any axioms\b',log):
        if not any(a <= marker.start() < b for a,b in spans):
            errors.append('Malformed or incomplete axiom report near byte '+str(marker.start()))
    if not expected: errors.append('Expected endpoint set is empty; refusing vacuous success.')
    for name in sorted(expected-observed.keys()): errors.append(f'Missing axiom output: {name}')
    # Preserve full compiler logs; this textual aid is intentionally conservative.
    if re.search(r'(?m)\berror:',log,re.I) or re.search(r'(?m)\bwarning:.*\bsorry',log,re.I):
        errors.append('Compiler diagnostic requires review; see raw log.')
    return {'allowed_axioms':sorted(ALLOWED),'observed':{k:sorted(v) for k,v in observed.items()},'errors':errors,'status':'PASS_LOG_ONLY' if not errors else 'FAIL'}

def main():
    ap=argparse.ArgumentParser(description=__doc__); ap.add_argument('log',type=Path); ap.add_argument('--expected',type=Path,required=True)
    a=ap.parse_args(); expected={l.split('#',1)[0].strip() for l in a.expected.read_text().splitlines()}; expected.discard('')
    r=check(a.log.read_text(),expected); print(json.dumps(r,indent=2)); raise SystemExit(bool(r['errors']))
if __name__=='__main__': main()
