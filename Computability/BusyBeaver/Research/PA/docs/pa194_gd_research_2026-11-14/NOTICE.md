# Attribution and provenance

This packet builds on the ProveIt PA Busy Beaver research corpus at revision
`8d31445d858761a8f6150c2e5012adae8895e932` and James Chang's PA196 construction.
It retains the original James Chang MIT license and ProveIt Contributors MIT No
Attribution license in `licenses/`.

Unmodified source inputs and their exact origins are listed in
`PROVENANCE.json`. `construction/compiler.py` and `symbolic_runtime.py` are
verbatim from the primary PA194 packet. `construction/support.py` consists of
its table, simultaneous-quotient, and startup utilities as vendored in the
pending AX11GH research packet. `check_commands.py` is adapted from the PA194GH
free-term emitter and command checker; its algebraic framework is inherited,
while the diagonal parameter, normal distribution order, dual detector checks,
and associated derived-word tests were changed for this work.
`check_source.py` is adapted from the incoming AX11GH arithmetic-template
checker, in turn adapted from the updated AX11H packet; it has been changed
for these ten-entry AX outputs, three operands, ordinary distribution, and
three Shift implementations.

The new files and modifications in this packet are the GD/GDH/GDHS composition,
its reproducible builder and documentation, and its exact construction
certificates. The common design, constituent reductions, and proof strategy
are attributed to the source corpus. No authorship claim is made for inherited
machinery or for separately known optimizations.
