#!/usr/bin/env python3
"""Source-level consistency checks for the uncompiled replay target policy."""
import json
from pathlib import Path
import re
import unittest
import freeze

HERE=Path(__file__).resolve().parent
RESEARCH=HERE.parents[1]
DRAFT=RESEARCH/'ipra-equality-reference/draft'

class PolicyTests(unittest.TestCase):
    def test_policy_freezer_and_wrapper_match_exactly(self):
        policy=json.loads((HERE/'task-policy.json').read_text())
        self.assertEqual(policy['target'],'DiophantineConsistency.IPRAReferenceReplayChecks')
        self.assertEqual(policy['expected_axiom_names'],list(freeze.EXPECTED))
        wrapper=(DRAFT/'IPRAReferenceReplayChecks.lean').read_text()
        names=re.findall(r'^#print axioms (\S+)\s*$',wrapper,re.M)
        self.assertEqual(names,policy['expected_axiom_names'])
        self.assertIn('import DiophantineConsistency.IPRAReferenceAQ29Source',wrapper)
        self.assertIn('import DiophantineConsistency.IPRAReferenceRoundtrip',wrapper)
    def test_selected_coding_drafts_resolve_in_planner(self):
        planner=freeze.load_planner()
        self.assertEqual(planner.TARGETS,('DiophantineConsistency.IPRAReferenceReplayChecks',))
        for module in ('IPRAReferenceSourceConsistency','IPRAReferenceAQ29Source','IPRAReferenceReplayChecks'):
            self.assertIn(module,planner.DRAFT_NAMES)
            self.assertTrue((DRAFT/(module+'.lean')).is_file())
        source=(DRAFT/'IPRAReferenceAQ29Source.lean').read_bytes()
        self.assertIn('DiophantineConsistency.IPRAReferenceSourceConsistency',planner.imports(source))
        self.assertIn('DiophantineConsistency.IPRAReferenceAQ29Direct',planner.imports(source))

if __name__=='__main__':unittest.main()
