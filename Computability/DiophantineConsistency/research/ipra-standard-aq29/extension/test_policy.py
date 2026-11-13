#!/usr/bin/env python3
"""Check the dedicated target, axiom reports and source import bindings."""
import json
from pathlib import Path
import re
import unittest
import freeze

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

class PolicyTests(unittest.TestCase):
    def test_policy_matches_target_and_diagnostic_source(self):
        policy = json.loads((HERE/'task-policy.json').read_text())
        self.assertEqual(policy['target'], 'DiophantineConsistency.IPRAStandardAQ29Checks')
        self.assertEqual(policy['expected_axiom_names'], list(freeze.EXPECTED))
        checks = (ROOT/'draft/IPRAStandardAQ29Checks.lean').read_text()
        self.assertEqual(re.findall(r'^#print axioms\s+([^\s]+)', checks, re.M),
                         policy['expected_axiom_names'])
        self.assertIn('import DiophantineConsistency.IPRAStandardAQ29', checks)
        client = (ROOT/'draft/IPRAStandardAQ29.lean').read_text()
        for dep in ('IPRAStandardTheory', 'IPRAAQ29Native', 'IPRABoundedRhoZFC'):
            self.assertIn('import DiophantineConsistency.'+dep, client)
        self.assertIn('IPRAAQ29Native.literal_equivalence', client)
        self.assertIn('IPRABoundedRhoZFC.zfcEquiv', client)
        self.assertIn('Entailment.E!_trans literal_equivalence', client)

if __name__ == '__main__':
    unittest.main()
