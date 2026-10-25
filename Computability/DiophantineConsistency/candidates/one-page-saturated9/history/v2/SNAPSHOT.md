# Historical v2 tight-nine-point checkpoint and actual fit-guard failure

This inert snapshot preserves the complete ten active candidate files and
external renderer from the second reviewed/released checkpoint, plus its
full failure transcript. All original dependencies and the previous
history/v1 remain in the live provenance tree; they are not recursively
copied. The archived runtime paths/pins are provenance data, not a claim
that this folder is a standalone executable checkout.

The actual v2 TeX was c359081b6e1e610730a941185bf86bb12ca13a47ab94b98183a1a07141a314af;
TOOL_PINS was739914e92fd8edd735f789bd857e19d325c2fe10bc4b88c7a34c41ca804cbb02.
Both full static delta reviews approved it, then root released five commands.
The first scratch renderer produced onepage/163624bytes with no vertical
overflow, but rejected a10.7589-point kernel hbox at line81. It did not
materialize a PDF, resultJSON or other generated artifact. No actual
mathematical auditor or pure rebuild ran. FAILURE.stderr.txt retains the
entire outside failure transcript. The current next proposed change is a
single additional D2 line break; its fit is untested.
