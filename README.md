# DBLog_Virtual_Cuts — Isabelle/HOL formal development

This is the machine-checked formal development that accompanies the paper

> **A Theoretical Study of DBLog**  
> *Certified Virtual Cuts for a Snapshot-Equivalent Replay of Live Databases*  
> Andreas Andreakis

The paper studies DBLog as a *snapshot-equivalent replay protocol for live
databases*: it produces a logical, replay-equivalent snapshot of a live
database scope without taking a physical database snapshot. The central
formal object is the **certified virtual cut** — a finite, asynchronously
gathered mix of change-data-capture events and chunk reads whose certified
replay reaches the same state as the source at a chosen frontier (a position
in the source-event order, analogous to a CDC watermark or log sequence
number) on a chosen key scope (the subset of keys the certificate claims to
reconstruct, for example a single table's primary keys).

The paper's formal definitions and its named theorem ladder are formalized
and machine-checked here, each under the conditional premises stated in its
theorem (see the *Main results* section below). The Isabelle/HOL kernel
checks the proofs under the assumptions stated in the paper; it does not,
and cannot, discharge the *Deployment obligations* (conditions the operator
or implementation must establish in a deployment — for example, faithful
CDC delivery and watermark placement) or the *External observation
assumption* (that the source-side observation is faithful, which the model
cannot prove from the certificate alone). The role of the machine check
is to guard against drift between the paper and the formalization.

## Building

The development is built and checked with **Isabelle2025-2**
(https://isabelle.in.tum.de/). It depends only on `HOL-Library` from the
Isabelle distribution; no Archive of Formal Proofs entries are required.

From this directory:

    isabelle build -d . DBLog_Virtual_Cuts

The session checks all seventeen theories `sorry`-free in a few seconds.

## Contents

The development is layered: each layer builds on the ones before it. Six
theories carry the core definitions and the main theorems, and one further
theory adds the post-core continuation extension on top of the core
ladder.

| Layer | Theory | Content |
|-------|--------|---------|
| 0 | `Source_History` | the source database and its history of states |
| 0 | `Replay` | the replay / apply substrate for change events |
| 0 | `Scope` | key scopes |
| 1 | `DBLog_Run` | the abstract DBLog run — chunk plan, clean prefix, and the `wellformed_dblog_run` predicate |
| 2–3 | `Virtual_Cut` | the virtual cut and the Layer 2 result; the certificate, its verifier, and Layer 3 certificate soundness |
| 4 | `Layer4_Whole_Table` | the whole-table specialization |
| post-core extension | `Continuation` | source-side continuation across frontiers and sub-scope restriction of virtual cuts |

The remaining ten theories support the core development and the
continuation extension. They are not required to state or prove the main
theorems; they exercise the definitions and guard against vacuity:

- `Layer01_Virtual_Cut_Example` — a fully worked positive virtual-cut
  example.
- `Layer01_Witnesses`, `Layer01_Witness_Topics`, `Layer3_Witnesses`,
  `Layer4_Witnesses` — positive witnesses that the predicates are
  inhabited. The Layer 3/4 witnesses additionally pin the abstract
  certificate / evidence / raw-observation interface with fixture axioms;
  see *Witness and fixture methodology* below.
- `Layer01_Fixtures`, `Layer2_Fixtures`, `Layer3_Fixtures`,
  `Layer4_Fixtures` — counterexample and boundary fixtures showing that the
  wellformedness clauses and certificate checks are not trivially satisfied.
- `Continuation_Fixtures` — the positive continuation witness and the
  load-bearing and boundary fixtures for the continuation extension.

### Witness and fixture methodology

The witness and fixture theories introduce fresh constants for the abstract
run, chunk, certificate, and evidence vocabulary with `axiomatization` and pin
their accessor values. They also introduce fresh source-coordinate constants
with explicit strict-order axioms (for example coordinates `c1_w` and `c2_w`
fixed above the base coordinate `c0`); these coordinate axioms are model-shape
assumptions about the source-coordinate order, not accessor pinning. The
theories are fixture instances that exercise the definitions and theorem
surfaces — model-shape witnesses for the abstract interface — rather than
executable constructions from closed-form data. Their non-vacuity and rejection
claims hold relative to both the accessor-pinning fixture axioms and the
source-coordinate order axioms.

These fixture and witness axiomatizations are confined to the witness and
fixture theories. The four core-ladder theorems and the five continuation-
extension theorems do not depend on them: their statements and proofs use
only the abstract `consts` / `typedecl` interface plus two modeling-level
axiomatizations declared with the abstract model itself — the source-
coordinate linear order with least element `c0` in `Source_History`, and
the distinct chunk enumeration `chunks_list` in `DBLog_Run`.

## Main results

### Core ladder (Layers 2–4)

Four core theorems carry the development.

- **`wellformed_run_implies_virtual_cut`** — the clean prefix of a wellformed
  DBLog run is a virtual cut: replaying it reproduces the source state,
  restricted to the run's scope, at the run's frontier.

- **`accepted_certificate_implies_wellformed_run`** — a certificate accepted
  by the verifier, paired with a faithful observation of the source, is
  witnessed by a wellformed run that is coherent with the certificate.

- **`accepted_virtual_cut_sound`** — a certificate accepted by the verifier,
  under faithful source observation, is a virtual cut: its certified replay
  reaches the source state at the certified frontier on the certified scope.

- **`accepted_whole_table_anchor_domain_specialization`** — when the
  certificate's claim scope is the whole table, applying its clean prefix
  reproduces the entire source state at the frontier.

Each core result is conditional. The Layer 2 result,
`wellformed_run_implies_virtual_cut`, is conditional on the hypotheses named
in its statement — chiefly the `wellformed_dblog_run` premise. The Layer 3
and Layer 4 results are established *inside* the `layer3_checker_substrate`
locale, which abstracts the verifier as a set of soundness obligations: an
accepted certificate has a wellformed materializing run whose accessors
agree with the certificate, under faithful source observation. Their
conditions are the hypotheses named in each statement — verifier
acceptance, faithful source observation, and, for the whole-table result, a
whole-table claim scope — *together with* these checker-substrate
obligations. All of these correspond to the Deployment obligations and the
External observation assumption discussed in the paper: the formalization
makes them explicit hypotheses; it does not discharge them.

### Continuation extension

The continuation extension is the promoted source-side fragment of the
"certificate algebra" future-work catalog (see the paper's "Source-Side
Continuation and Restriction of Virtual Cuts" section). It is built source-side
over the core ladder: each result is an `Apply`-against-`Src` equality, and
the proofs compose with Layer 2 and Layer 3 without re-opening the abstract
DBLog run model.

- **`virtual_cut_state_continuation`** — primary continuation theorem. On a
  wellformed source history, a virtual cut at frontier `f` on scope `K`
  extends to a virtual cut at any later frontier `f'` on `K` by appending the
  faithful CDC continuation segment for the half-open interval `(f, f']` on
  `K`. The premise that the appended segment is exactly the
  `cdc_segment_between` for `(f, f']` on `K` is the source-side faithfulness
  obligation; the wellformedness of the source history is the second
  conditional premise.

- **`virtual_cut_state_restrict_scope`** — sub-scope restriction lemma. A
  virtual cut on key scope `K` restricts to a virtual cut on any `K' ⊆ K`.
  The converse — scope widening — is not stated and would assert agreement on
  keys never certified.

- **`whole_table_state_continuation`** — whole-table instance of continuation.
  When `Apply σ = Src b0 H f` holds unrestricted — the all-keys equality the
  Layer 4 specialisation yields — appending the full CDC segment for
  `(f, f']` on `UNIV` reaches the source state at `f'` on every key. A scoped
  continuation does not become whole-table for free.

- **`virtual_cut_restrict_to_subscope`** — certificate-accessor sub-scope
  restriction. An accepted certificate's virtual cut, read through its
  accessors, restricts to any sub-scope `K' ⊆ scope C` as a source-side
  `virtual_cut_state` equality on `clean_prefix C` at `frontier C`. This is
  *not* a claim that a restricted certificate is accepted by the verifier;
  verifier acceptance of any concrete restricted certificate is an evidence
  obligation, not a consequence of the source-side algebra.

- **`accepted_certificate_continuation_sound`** — accessor-level accepted-
  certificate continuation. Inside the `layer3_checker_substrate` locale, an
  accepted certificate under faithful source observation extends, by a
  faithful CDC continuation segment for `(frontier C, f']` on `scope C`, to
  a virtual-cut-state equality on `clean_prefix C @ δ` at the later frontier
  `f'`. The conditional premises are verifier acceptance, faithful source
  observation, wellformedness of the source history, the locale's
  checker-substrate obligations, *and* the continuation-segment faithfulness
  premise on `δ`.

Each continuation-extension result is conditional on the hypotheses named
in its statement, with the same Deployment-obligation and
External-observation-assumption interpretation as the core ladder. The
extension is source-side throughout: no result here is a destination-state,
delivery, sink, or extended-certificate-acceptance claim.

## Release metadata

For the artifact deposited under the paper's DOI, the verification
environment is pinned as follows.

- **Session.** `DBLog_Virtual_Cuts`, 17 theories (see *Contents* above),
  checked `sorry`-free.
- **Prover.** Isabelle2025-2 (`ISABELLE_IDENTIFIER=Isabelle2025-2`),
  using `HOL-Library` only — no Archive of Formal Proofs entry.
- **Release identification.** Before depositing or citing the artifact as
  a release, create the signed release tag for the exact checked commit
  and record the commit hash, tag name, release date, and Zenodo DOI with
  the tag and in the Zenodo deposit.

A representative clean-build transcript — `isabelle build -c -d .
DBLog_Virtual_Cuts`, run from this directory; elapsed times are
machine-dependent:

    Cleaned DBLog_Virtual_Cuts
    Running DBLog_Virtual_Cuts ...
    Finished DBLog_Virtual_Cuts (0:00:13 elapsed time, 0:00:35 cpu time, factor 2.65)
    0:00:18 elapsed time, 0:00:35 cpu time, factor 1.93

The build exits with status 0, and no theory uses `sorry` or `oops`.

## License

Released under the BSD 3-Clause License. See [`LICENSE`](LICENSE).

## Author

Andreas Andreakis.
