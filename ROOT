chapter "DBLog"

session DBLog_Virtual_Cuts = "HOL-Library" +
  description "
    Machine-checked formal development accompanying the theoretical
    study 'A Theoretical Study of DBLog'.

    DBLog is studied as a snapshot-equivalent replay protocol for live
    databases: it reconstructs a logical, replay-equivalent snapshot of a
    live database scope without taking a physical database snapshot. The
    development is layered. Layer 0 fixes the source-history and replay
    substrate; Layer 1 the abstract DBLog run and its wellformedness;
    Layer 2 proves that a wellformed run replays to the source state at
    its frontier on its scope. Layer 3 introduces the certified virtual
    cut and, inside the layer3_checker_substrate locale, proves that
    verifier acceptance and faithful source observation --- together with
    the locale's checker-substrate obligations --- imply that the
    certificate replays to the same source state. Layer 4 specialises that
    locale result to whole-table claims. The post-core continuation
    extension adds two primary source-side facts on top of the core
    ladder --- continuation across frontiers extends a virtual cut at a
    frontier to one at any later frontier by appending the faithful
    in-scope CDC segment for the half-open interval, and sub-scope
    restriction restricts a virtual cut on a key scope to any sub-scope ---
    together with whole-table and accepted-certificate corollaries.

    Every theorem is conditional on the premises stated in its statement;
    the machine check does not discharge the deployment obligations or the
    external-observation assumption that a real deployment must establish.

    All theories build sorry-free. The wellformedness predicate's WF7
    clean-prefix CDC-coherence conjunct is provably redundant --- the lemma
    wf7_clean_prefix_cdc_coherence_redundant (in Layer01_Fixtures)
    establishes it for every run --- and is retained in the predicate body
    for documentation.
  "
  theories
    Source_History
    Replay
    Scope
    DBLog_Run
    Virtual_Cut
    Layer01_Witnesses
    Layer01_Virtual_Cut_Example
    Layer01_Witness_Topics
    Layer01_Fixtures
    Layer2_Fixtures
    Layer3_Witnesses
    Layer3_Fixtures
    Layer4_Whole_Table
    Layer4_Witnesses
    Layer4_Fixtures
    Continuation
    Continuation_Fixtures
