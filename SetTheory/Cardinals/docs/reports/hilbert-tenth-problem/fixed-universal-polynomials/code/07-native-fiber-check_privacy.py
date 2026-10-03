"""Check delivered human-readable text for environment-private path artifacts."""
import sys
sys.dont_write_bytecode = True
import re
from pathlib import Path
from verify_release import ROOT, inventory, require


def main():
    files, unused = inventory(ROOT)
    # Construct tokens so the scanner itself has no prohibited literal.
    forbidden = ['/'+'workspace/', '/'+'root/', '/'+'home/agent/', 'dream'+'_notes', 'collaboration'+'.send_message', '<'+'transcript_evidence>']
    scanned = 0
    for name, path in sorted(files.items()):
        if path.suffix not in ('.md','.json','.tex','.txt','.sha256'):
            continue
        text = path.read_text(encoding='utf-8')
        require(not any(token in text for token in forbidden),'private artifact in '+name)
        require(not re.search(r'\b(?:agent_id|thread_id|turn_id)\b',text),'internal identifier in '+name)
        scanned += 1
    print('PASS: public-clean text scan on '+str(scanned)+' text files; PDF visual/text QA is recorded separately')


if __name__ == '__main__':
    main()
