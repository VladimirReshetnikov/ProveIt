#!/usr/bin/env python3
"""Inspect pinned nine-variable sources and build claims; does not run Lean."""
from hashlib import sha256
from pathlib import Path
import json
import re
import subprocess
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is rejected')
DC=Path(__file__).resolve().parents[2]
REPO=DC.parents[1]
SRC=DC/'Lean/DiophantineConsistency'
commit='d9947ea4ea9c0b5957bb833bac677741d7c9a341'
pins={
 'IPRAExplicitZFCFinal.lean':'ce51ce23ef4c04ff6415a92905f819e8cb21d326d50413eaa28e4cfd53c0c70a',
 'IPRANineCurrent.lean':'15dfdd6d6f2304c33773ac9b1d32f268518ab4f10181ac4440b8b147c74e2d54',
 'IPRAExplicitZFCReduction.lean':'38af4f63ce1d800a5d9a51e7b8df77dd2a40cf863e1974b836371e5445ecd419',
 'ModelJonesNine.lean':'52fd7d935965d554eb6dd667ae86a97ffa6518b6ec6e053faab3efa8a9bf5143',
 'ModelProgramLink.lean':'ab27fb8d076369febca716581bd0159cb80aef0bb63e51015e31d217c863824b',
 'ModelRepFinal.lean':'73350c8264b0593a5fb68b97cc7de5cdcde85a60119ba291c5b8af2dacd96da7',
 'ExplicitZFCSyntax.lean':'86c1c0edb6b6943ba1f7165da1d0175b246e02d697f231da3afdbf46983dc98b',
 'ExplicitZFC.lean':'081619bb76d08848f742e6a07a2d38e5f98f20fe9c3a7ec8d1d33d69e16f9fd7',
 'ModelCarrierCurrent.lean':'f0a4898f545a932b135783799ae0d44179fbcbcb08e5d97eaced4515740e990f',
 'IPRANineChecks.lean':'860903cd7bd24457f4f2800f7e6f77c1e2a0e8906ac7e572ac99d7ddd9ffdcaf',
}
def need(ok,msg):
    if not ok: raise ValueError(msg)
def digest(data): return sha256(data).hexdigest()
def check_files():
    for name,pin in pins.items():
        need(digest((SRC/name).read_bytes())==pin,'source changed: '+name)
    need(digest((DC/'EXPLICIT_EQUATION.md').read_bytes())==
         '95b3755e77e1833befe528eb5524d99830e8350c1a65ee576d2836b9cb08f069','equation document')
    need(digest((DC/'research/nine-variable-ipra/PLAN.md').read_bytes())==
         '418669661245804eb0f250cbffa05749c136729d5ccf968f3baee01040d14e6f','author plan')
def git(*args):
    p=subprocess.run(['git','-C',str(REPO),*args],capture_output=True,check=False)
    need(p.returncode==0,'git failed: '+str(args))
    return p.stdout
check_files()
message=git('show','-s','--format=%B',commit).decode()
need('Every module built serially' in message and '#print axioms lists only' in message,
     'author build/axiom statement not found')
for name,pin in pins.items():
    if name=='ModelCarrierCurrent.lean':
        continue  # inherited input; not changed by the endpoint commit
    path='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+name
    need(digest(git('show',commit+':'+path))==pin,'source differs from endpoint commit: '+name)

explicit=(SRC/'IPRAExplicitZFCFinal.lean').read_text()
current=(SRC/'IPRANineCurrent.lean').read_text()
reduction=(SRC/'IPRAExplicitZFCReduction.lean').read_text()
binding=(SRC/'ExplicitZFC.lean').read_text()
for s in ('ModelJonesNine.jonesModel sourceModel',
          'ModelProgramLink.sourceModel ModelRepFinal.precCase',
          'IPRAExpressionNative.nativeNoZero ExplicitZFCSyntax.expression'):
    need(s in explicit,'missing explicit endpoint link: '+s)
for name in ('native_equivalence','standard_equivalence','reference_equivalence'):
    need(re.search(r'\btheorem\s+'+name+r'\s*:',explicit) is not None,
         'missing/no-premise explicit declaration: '+name)
    need(re.search(r'\btheorem\s+'+name+r'\s*:',current) is not None,
         'missing/no-premise current declaration: '+name)
need('def JonesModel : Prop' in reduction and 'def SourceModel : Prop' in reduction,
     'reduction model obligations')
need('theorem expression_eq_syntax : expression = ExplicitZFCSyntax.expression' in binding,
     'separate formal syntax equality')
need('def expression : Expr (Fin 9) := ExecutableJones.expression seed 0' in current,
     'distinct maintained-equation construction')

changed=git('diff','--name-only','-z',commit+'^',commit,'--',
            'Computability/DiophantineConsistency/Lean/DiophantineConsistency/*.lean').decode().split('\0')
changed=[p for p in changed if p]
need(changed,'empty endpoint source list')
markers=[]
for path in changed:
    data=git('show',commit+':'+path).decode()
    if re.search(r'\b(sorry|admit)\b|^\s*axiom\b',data,re.M): markers.append(path)
need(not markers,'lexical sorry/admit/axiom markers: '+str(markers))
local={name:(REPO/'.lake/build/lib/lean/DiophantineConsistency'/name).is_file() for name in
       ('IPRAExplicitZFCFinal.olean','IPRANineCurrent.olean')}
plan_dir=DC/'research/nine-variable-ipra'
evidence_files=sorted(p.name for p in plan_dir.iterdir() if p.is_file())
check_files()
print(json.dumps({'status':'PASS_PINNED_SOURCE_INSPECTION_NOT_A_BUILD',
                  'endpoint_commit':commit,'changed_lean_files_scanned':len(changed),
                  'local_endpoint_objects_present':local,'plan_directory_files':evidence_files,
                  'scope':'source and author-claim inspection; no Lean run or proof-closure audit'},sort_keys=True))
