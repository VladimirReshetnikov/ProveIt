"""Research implementation. No unchecked input is promoted to a knot verdict."""
from .slp import Presentation, Arena, LimitExceeded, from_words, export_word_arena
from .dihedral import solve as solve_two_meridians
__version__ = '0.1.0'
