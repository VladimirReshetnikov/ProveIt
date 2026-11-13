#!/usr/bin/env python3
"""Derive the exact recipe and scopedness definitions without importing endpoint semantics."""
import hashlib,json,sys
from pathlib import Path
P=Path(__file__).resolve().parent;src=P.parent/'nine-seed33-jones-compact-lean-specialized-draft/Sign33MacroRecipe.lean'
h=lambda b:hashlib.sha256(b).hexdigest()
b=src.read_bytes()
if h(b)!='c19d0ba99c7594611088744f7c293ac1a7647f4aeb3facd3169e9619d0152ad1':raise RuntimeError('source pin')
s=b.decode();start=s.index('/-- Open proposition: compact graph evaluation equals the checked endpoint. -/');end=s.index('end DiophantineConsistency.Sign33MacroRecipe',start);s=s[:start]+s[end:];out=P/'Sign33MacroRecipeLight.lean'
if sys.argv[1:]==['--write']:out.write_text(s)
elif sys.argv[1:]==['--check']:
 if out.read_text()!=s:raise RuntimeError('light recipe mismatch')
 print(json.dumps({'status':'PASS_SPLIT_REGENERATION_ONLY','source_sha256':h(b),'output_sha256':h(out.read_bytes()),'scope':'Source transformation only; no Lean semantics or parser proof.'},sort_keys=True))
else:raise SystemExit('expected --write or --check')
