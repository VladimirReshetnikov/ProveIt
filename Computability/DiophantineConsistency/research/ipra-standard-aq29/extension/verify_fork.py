#!/usr/bin/env python3
"""Check the task fork against pinned reviewed reference-extension sources."""
import hashlib
from pathlib import Path
import freeze

HERE = Path(__file__).resolve().parent
STANDARD = HERE.parent
REFERENCE = STANDARD.parent/'reference-coherent-replay'
PINS = {
    'plan.py': '007828b8f92298dd8b47413d54d0298198f40d4396417631251f97d06cb7c996',
    'extension/prepare.py': '4720f7a2989e4fcf883dd50fd81711a82c5dacfbf526665763cd7c06e7892964',
    'extension/freeze.py': '49ecd7b286a6fd3351ab215c60093205765e4506d96f84cdbeec0dd12c3e09e9',
    'extension/rebuild.py': '069aa3f87638e5ea571e30ab8ae12af0ab9d23d38e00b0c6c3935a9228bdf35f',
    'extension/compare.py': '7e355f2ecfe464b6828aab85ea324cea519bc0e989f3b6dba81bd50c4abe7a34',
    'extension/run_pair.py': 'ab51a8b295adc0419610671e5e39775a538d45858151bf8b575bdfa6dfc6a8f7',
}
def H(data): return hashlib.sha256(data).hexdigest()

for rel, expected in PINS.items():
    raw = (REFERENCE/rel).read_bytes()
    if H(raw) != expected:
        raise ValueError(('reviewed reference source changed', rel))
    source = raw.decode()
    if rel == 'plan.py':
        source = source.replace(
            "DRAFT = ROOT/'Computability/DiophantineConsistency/research/ipra-equality-reference/draft'",
            "DRAFT = ROOT/'Computability/DiophantineConsistency/research/ipra-standard-aq29/draft'")
        a = source.index('DRAFT_NAMES = {'); b = source.index('\nTARGETS =', a)
        source = source[:a]+"DRAFT_NAMES = {'IPRAStandardAQ29', 'IPRAStandardAQ29Checks'}"+source[b:]
        source = source.replace("TARGETS = ('DiophantineConsistency.IPRAReferenceReplayChecks',)",
                                "TARGETS = ('DiophantineConsistency.IPRAStandardAQ29Checks',)")
    elif rel == 'extension/prepare.py':
        source = source.replace('research/reference-coherent-replay/extension/task-policy.json',
                                'research/ipra-standard-aq29/extension/task-policy.json')
    elif rel == 'extension/freeze.py':
        a = source.index('EXPECTED=('); b = source.index('\nH=prepare.digest', a)
        source = source[:a]+'EXPECTED=(\n'+''.join('    '+repr(x)+',\n' for x in freeze.EXPECTED)+')'+source[b:]
    if (STANDARD/rel).read_text() != source:
        raise ValueError(('unexpected fork delta', rel))
print('PASS: six production tools match pinned reviewed sources plus task-specific substitutions')
