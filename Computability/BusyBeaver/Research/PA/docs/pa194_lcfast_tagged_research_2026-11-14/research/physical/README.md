# Bounded physical reductions: no accepted shortcut or shared fold

These two fresh C++ programs screen restricted physical transformations. They are discovery tools; no smaller table was produced or accepted. Compile with C++17. Their input tables use native start 74 and halt 254.

## Single-transition contraction

`shortcuts.cpp` computes all finite abstract windows reachable from a blank window, allowing either bit whenever a cell is newly exposed at a window boundary. It then tests whether one altered transition can reproduce a positive bounded prefix of the old path, with exact control, displacement and tape-window agreement.

```sh
c++ -O3 -std=c++17 shortcuts.cpp -o /tmp/pa-shortcuts
/tmp/pa-shortcuts PA194AX11GHF.tm 7 161 74
/tmp/pa-shortcuts PA194AX11GHF.tm 6 200 74 GH_contexts6.txt
```

The first run reached 912,456 windows and found zero alterable rows. The source-narrowed run started with 271,639 radius-six windows, restricted 171 controls using 30,818 inherited source/startup contexts, and again found zero alterable rows. Arithmetic-box controls retain the broader abstraction. The narrowed envelope is a screen, not a replacement for universal verification of an accepted machine.

## A shared selector for two history pairs

`shared_selector.cpp` tries to replace two homogeneous-history pairs by two merged controls and one shared selector. The current bit stores the pair tag, the previous cell stores the history bit, and an existing provider must restore the tag and reproduce the intended original transition. It tries both pair tags and existing providers on bounded windows.

```sh
c++ -O3 -std=c++17 shared_selector.cpp -o /tmp/pa-shared-selector
/tmp/pa-shared-selector PA194AX11GHF.tm 6 120
/tmp/pa-shared-selector primary.tm 7 200
/tmp/pa-shared-selector PA194AX11GHF.tm 6 200 GH_contexts6.txt
```

Each input has sixteen eligible history pairs. All three runs reported zero nominations. The primary radius-seven run reached 898,177 windows. Standard-output candidates and standard-error statistics are retained as the named `.txt` and `.log` files.

## Scope and provenance

The inputs are from ProveIt snapshot `8d31445d858761a8f6150c2e5012adae8895e932`. `PA194AX11GHF.tm` and its GHS companion are the incoming accelerated native tables. `primary.tm` is the original primary table expressed in native labels. `GH_contexts6.txt` is the unchanged complete source/startup radius-six context file from the supplied GH reduction work. The manifest records their exact bytes. The C++ implementations are new in this investigation; the inherited tables and context data retain the upstream attribution and licenses in the packet root.

These failures concern the stated templates and finite search bounds. They neither exclude other 193-state constructions nor prove a global lower bound.
