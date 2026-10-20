# Independent decoder audit of the provisional218 table

The literal candidate SHA-256 is
`cd2e25ad8bd58112b74d671ff78334eacc0eb237201b32c871a73424e134073f`.
It has218 working states and436 rows, but **this first table is not accepted
from blank start**. Its source decoder is correct; its initialization fails.

`../candidate218_decoder_audit.py` independently parses both tables, checks the
exact three changed retained rows and deletion of301, simulates all4,743
source prefixes, proves the two local predecessor-bit decoder paths by literal
steps, and reproduces the first blank-start discrepancy. It also checks the
relevant contexts in the completed published219 R7 projection.

The machine-readable result is `decoder_audit.json`. The manuscript-ready
explanation is `decoder_lemma.tex`. Neither file treats a correct primitive
decoder as a substitute for a complete blank initialization proof.

The reduction's mechanism is useful independently of the initializer issue:
state88 shares two source roles using the immediately preceding address bit;
state51's new exit helps distinguish those roles while preserving its old
post-initialization scan behavior whenever the following cell is1.
