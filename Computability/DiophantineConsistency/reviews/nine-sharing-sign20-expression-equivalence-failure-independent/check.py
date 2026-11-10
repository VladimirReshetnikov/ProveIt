#!/usr/bin/env python3
"""Audit recorded pre-Lean family-key setup failure; do not execute runner."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign20-expression-equivalence-check';attempt=packet/'attempt01';out=Path('/tmp/nine-sharing-sign20-expression-equivalence-check-20261109');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
o=json.loads((attempt/'outer-result.json').read_text());assert o['author_observed_outer_session']==66119 and o['author_observed_numeric_outer_exit']==1
runner=packet/'run.py';assert sha(runner)==o['runner_sha256']=='1e3acf2d0b30f075cbc18177eb5d23ad3c95b61daa574da0c65f0e22f9409cf2'
log=(attempt/'outer-output.txt').read_text();assert sha(attempt/'outer-output.txt')==o['outer_output_sha256'] and log==o['author_observed_stdout'] and "KeyError: '24'" in log
s=runner.read_text();assert s.count("for family in ('24','25'):")==2 and "('Sign20CurrentExpressionEval','Sign25CurrentExpressionEval')" in s and "family='24' if local=='Sign20CurrentExpressionEval' else '25'" in s
u=json.loads((packet/'union.json').read_text());assert set(u)=={'20','21'} and out.is_dir() and not (out/'state.json').exists()
assert not list(out.glob('*-deps.txt')) and not list(out.glob('*-compile.txt')) and not (out/'lib/DiophantineConsistency/Sign20ExpressionEquivalence.olean').exists()
survey=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'evaluator-union-survey.py')],capture_output=True,text=True,check=True,timeout=120);assert set(json.loads(survey.stdout)['evaluators'])=={'20','21'}
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_session':66119,'outer_exit':1,'scope':'setup failure before state and Lean; original preflight failed to inspect injection and direct-routing loops'},sort_keys=True,indent=2))
