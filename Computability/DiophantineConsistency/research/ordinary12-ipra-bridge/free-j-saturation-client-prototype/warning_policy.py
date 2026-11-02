#!/usr/bin/env python3
"""Exact historical ArithmeticBinaryCarry warning inventory and controls."""
import os
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
def accepted(name,src,text):
    if name=='DiophantineConsistency.ArithmeticBinaryCarry':
        expected=(f"{src}:153:12: warning: try 'simp' instead of 'simpa'\n\n"
            "Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`\n"
            f"{src}:159:16: warning: try 'simp' instead of 'simpa'\n\n"
            "Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`\n"
            f"{src}:153:54: warning: 'simp' tactic does nothing\n\n"
            "Note: This linter can be disabled with `set_option linter.unusedTactic false`\n"
            f"{src}:153:54: warning: this tactic is never executed\n\n"
            "Note: This linter can be disabled with `set_option linter.unreachableTactic false`\n")
        return text==expected
    return 'warning:' not in text

def main():
    name='DiophantineConsistency.ArithmeticBinaryCarry'
    src=Path('/tmp/ipra-freej-saturation-explore/src/DiophantineConsistency/ArithmeticBinaryCarry.lean')
    text=(Path(__file__).resolve().parent/'observations/author-explore/ArithmeticBinaryCarry.log').read_text()
    if not accepted(name,src,text):raise ValueError('observed inventory rejected')
    for other_name,other_text in ((name,text.replace(':153:12:',':153:13:',1)),(name,text+'extra warning: injected\n'),('DiophantineConsistency.ArithmeticSaturation',text),(name,''),(name,text.replace("Note: This linter can be disabled with `set_option linter.unusedTactic false`\n",'',1))):
        if accepted(other_name,src,other_text):raise ValueError(('changed warning accepted',other_name,other_text))
    if not accepted('DiophantineConsistency.ArithmeticSaturation',src,''):raise ValueError('warning-free module rejected')
    print('PASS_EXACT_SATURATION_WARNING_CONTROLS')
if __name__=='__main__':main()
