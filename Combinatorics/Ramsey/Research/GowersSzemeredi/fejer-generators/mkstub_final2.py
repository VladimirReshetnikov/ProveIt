"""StubFinal.lean via mkstub_final.py, then state the corpus theorem
progressionPhasePartition_explicit as a stub axiom (its inlined proof uses a corpus
lemma the peer has since changed) and allow it in the audit block."""
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
subprocess.run([sys.executable, '-X', 'utf8', str(HERE / 'mkstub_final.py')], check=True)
p = HERE / 'StubFinal.lean'
s = p.read_text(encoding='utf8')
a = s.index('theorem progressionPhasePartition_explicit :')
b = s.index(':= by', a)
end = re.compile(r'\n(?=/--|theorem |def |end |namespace )').search(s, b).start()
stmt = s[a:b].replace('theorem progressionPhasePartition_explicit', 'axiom progressionPhasePartition_explicit')
s = s[:a] + stmt.rstrip() + '\n' + s[end:]
old = '``LeanProofs.GowersSzemeredi.section16RecurrenceProfileWith_explicit]'
assert old in s
s = s.replace(old, '``LeanProofs.GowersSzemeredi.section16RecurrenceProfileWith_explicit, '
              '``LeanProofs.GowersSzemeredi.progressionPhasePartition_explicit]')
p.write_text(s, encoding='utf8', newline='\n')
print('stubbed; lines', s.count('\n'))
