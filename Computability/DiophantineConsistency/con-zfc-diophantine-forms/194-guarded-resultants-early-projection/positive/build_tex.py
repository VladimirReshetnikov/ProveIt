#!/usr/bin/env python3
"""Render the exact complete proof into portable ASCII-source LaTeX."""
from pathlib import Path
import subprocess,tempfile
ROOT=Path(__file__).resolve().parent
s=(ROOT/'PROOF.md').read_text()
replace={'−':'-','–':'--','—':'---','²':'^2','³':'^3','⁴':'^4','⁶':'^6','⁷':'^7','⁸':'^8','₀':'0','±':'+/-','≡':' congruent ','≤':'<=','≥':'>=','∈':' in ','≠':'!=','≔':':=','Δ':'Delta','Ω':'Omega','λ':'lambda','β':'beta','σ':'sigma','κ':'kappa','ρ':'rho','τ':'tau','η':'eta','ζ':'zeta','α':'alpha','ε':'epsilon','π':'pi','ψ':'psi','χ':'chi','θ':'theta','·':'*','→':' -> ','↔':' iff ','’':"'",'“':'"','”':'"'}
for a,b in replace.items():s=s.replace(a,b)
s='\n'.join(line if line.startswith('    ') else line.replace('**','').replace('*',r'\*').replace('^',r'\^') for line in s.splitlines())+'\n'
if not s.isascii():raise ValueError(sorted(set(c for c in s if ord(c)>127)))
with tempfile.TemporaryDirectory() as d:
 p=Path(d)/'proof.md';p.write_text(s)
 subprocess.run(['pandoc',str(p),'-f','markdown','-t','latex','--top-level-division=section','-o',str(ROOT/'section.tex')],check=True)
