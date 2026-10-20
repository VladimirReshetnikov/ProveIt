#!/usr/bin/env python3
"""Deterministically preserve the base projector except relational collection."""
from pathlib import Path
import residue_projection_parts as parts
ROOT=Path(__file__).resolve().parents[1]
p=(ROOT/'machine218/project_windows219.py').read_text()
p=p.replace('import sys,json,time,argparse,hashlib','import sys,json,time,argparse,hashlib,struct')
p=p.replace('a=ap.parse_args();R=a.radius;CAP=2*R+3',"ap.add_argument('--residue',type=Path,default=ROOT/'root218/joint_residue.bin')\nap.add_argument('--residue-audit',type=Path,default=ROOT/'root218/joint_residue_audit.json')\na=ap.parse_args();R=a.radius;CAP=2*R+3")
p=p.replace('bootcert=json.loads(a.startup.read_text());boot=bootcert[\'startup\']',parts.SETUP+'\nbootcert=json.loads(a.startup.read_text());boot=bootcert[\'startup\']')
i=p.index('def values(');j=p.index('@lru_cache(150000)',i);p=p[:i]+parts.VALUES+'\n'+p[j:]
i=p.index('def collect(');j=p.index('def loop_positions(',i);p=p[:i]+parts.COLLECT+'\n'+p[j:]
p=p.replace("receipt=dict(status=", "receipt=dict(residue_certificate_sha256=sha(a.residue),residue_audit_sha256=sha(a.residue_audit),status=")
p=p.replace('Requires the checked source invariant, symbolic runtime induction, and proved source semantics.', 'Requires independently checked product and joint-residue source invariants, symbolic runtime induction, and proved source semantics.')
(ROOT/'root218/project_residue_windows219.py').write_text(p)
print('GENERATED root218/project_residue_windows219.py')
