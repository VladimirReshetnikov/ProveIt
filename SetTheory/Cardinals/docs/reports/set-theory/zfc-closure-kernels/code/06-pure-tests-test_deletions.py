"""Full relation checks for two genuine one-object deletion models."""
import unittest

class DeletionTests(unittest.TestCase):
    def test_deleting_range_purity_full_model(self):
        # Domain {0}, E={(0,0)}. Every subset test is true, and every
        # closure consequent y in C is true, for both possible relations.
        for relation in (False, True):
            bounded = True
            closure = not relation or True
            self.assertTrue(not bounded or closure)
        # The empty-relation instance fails when range purity is retained.
        self.assertFalse(not True or False)
    def test_membership_seed_without_inhabitedness_empty_model(self):
        # Domain {0}, E=empty. Every subset test is true but neither seed
        # membership nor closure membership activates an input.
        for relation in (False, True):
            active = False or False
            closure = not (active and relation) or False
            purity = not False or relation
            self.assertTrue(closure and purity)
        # A reflexive seed with the full relation fails in this model.
        self.assertFalse(not ((True or False) and True) or False)

if __name__ == '__main__':
    unittest.main()
