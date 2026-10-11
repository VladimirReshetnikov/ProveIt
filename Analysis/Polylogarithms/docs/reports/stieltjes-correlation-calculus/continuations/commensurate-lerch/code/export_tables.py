#!/usr/bin/env python3
"""Export exact pole data as readable, versioned mathematical artifacts."""
import json
from pathlib import Path
from commensurate import pole_table
ROOT=Path(__file__).resolve().parents[1]
families=[(1,1),(1,2),(1,3),(1,4),(2,3),(1,1,2),(1,2,3),(1,1,2,2)]
out=[]
for qs in families:
    t=pole_table(qs)
    out.append({'rates':[str(q) for q in t.rates], 'period':str(t.period), 'sign':t.sign,
                'coefficients':[{'pole':str(rho),'order':k,'coefficient_sympy':str(a)} for (rho,k),a in sorted(t.coefficients.items())]})
(ROOT/'verification'/'exact-pole-tables.json').write_text(json.dumps(out,indent=2)+'\n')
