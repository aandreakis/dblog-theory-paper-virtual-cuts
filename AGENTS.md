# AGENTS.md

Orientation file for AI assistants and automated readers working with this
repository. Human readers should start at [`README.md`](README.md), which is
deliberately short: it points at the sources and their identifiers. This file is
the fullest orientation surface in the repository.

This repository is **not a software project**. It is a research paper plus its
machine-checked formal development. There is no application to run, no test
suite to extend, and no feature work. Your likely task is to *read, explain,
cite, or check* — so this file gives you the source hierarchy, the exact
vocabulary, the theorem index, and the claims this work does **not** make.

**Links.** Paper: [arXiv:2605.31475](https://arxiv.org/abs/2605.31475)
([v4 abs](https://arxiv.org/abs/2605.31475v4) ·
[v4 PDF](https://arxiv.org/pdf/2605.31475v4) ·
[in-repo PDF](paper/dblog_virtual_cuts_v4.pdf) ·
[sources](paper/)). Formal development:
[`formal/`](formal/) · archived at Zenodo
[10.5281/zenodo.21732790](https://doi.org/10.5281/zenodo.21732790) (version 2.1)
· [10.5281/zenodo.20389696](https://doi.org/10.5281/zenodo.20389696) (concept
DOI). Derived reading: [`docs/THEOREMS.md`](docs/THEOREMS.md) ·
[`docs/PROVENANCE.md`](docs/PROVENANCE.md) ·
[`formal/README.md`](formal/README.md). Prior work:
[2020 DBLog paper](https://arxiv.org/abs/2010.12597) ·
[2019 Netflix Tech Blog post](https://netflixtechblog.com/dblog-a-generic-change-data-capture-framework-69351fb9099b).
Author: Andreas Andreakis,
[ORCID 0009-0003-9025-9402](https://orcid.org/0009-0003-9025-9402).

---

## 1. What this is, in one paragraph

The paper **“A Theoretical Study of DBLog: Certified Virtual Cuts for a
Snapshot-Equivalent Replay of Live Databases”** (Andreas Andreakis, 2026,
[arXiv:2605.31475](https://arxiv.org/abs/2605.31475)) formalizes the correctness
object of the DBLog change-data-capture backfill mechanism: a **certified
virtual cut**, a finite bundle of CDC events and chunk reads whose replay
reaches the same per-key state as the source at a chosen frontier on a chosen
key scope. Nine headline theorems are machine-checked in Isabelle/HOL under the
premises stated in their own statements. (The development's other theorems are
closed witnesses and fixtures; they exercise the definitions and guard against
vacuity.)

## 2. Source precedence

When sources disagree, the higher entry wins. Say so explicitly if you find a
disagreement — it is a defect worth reporting.

1. **`formal/`** — the Isabelle/HOL sources. Kernel-checked; the last word on
   what is actually proved and under which hypotheses.
2. **`paper/main.tex`** and the arXiv PDF — the paper of record, including its
   scope statements, non-claims, and deployment obligations.
3. **`formal/README.md`** — the artifact's own description of its contents.
4. **`README.md`, `docs/`, this file** — derived explanation for readers. Useful,
   but never authoritative over 1–3.

Never infer a theorem's content from prose in this repository. Read the
statement in `formal/`.

## 3. Repository map

| Path | Contents | Authoritative? | Editable? |
|---|---|---|---|
| `formal/*.thy`, `formal/ROOT`, `formal/document/` | Isabelle/HOL session `DBLog_Virtual_Cuts`, 38 theories | yes, for proofs | **no — byte-frozen** |
| `formal/README.md` | artifact README (theory-by-theory) | yes, for artifact description | no |
| `paper/main.tex`, `paper/refs.bib`, `paper/figures/` | arXiv v4 sources | yes, for the paper | only by the author |
| `paper/*.pdf` | built paper | yes | no |
| `docs/THEOREMS.md` | verbatim theorem statements, premises, non-claims | no (derived) | yes, by the author |
| `docs/PROVENANCE.md` | paper/artifact version history and DOIs | no (derived) | yes, by the author |
| `README.md`, `AGENTS.md`, `CITATION.cff` | hub surface | no (derived) | yes, by the author |

## 4. Hard rules

1. **Do not edit anything under `formal/`.** Those bytes are identical to the
   archived Zenodo deposit (version 2.1, DOI `10.5281/zenodo.21732790`). An edit
   silently breaks the correspondence between this repository and the archival
   record. If you believe you have found a defect, report it as an issue with a
   reproduction; artifact defects are fixed by publishing a new version, not by
   patching this tree.
2. **Never state a theorem without its premises.** Every one of the nine
   headline results is premise-bearing. “DBLog is correct” is not a claim this
   work makes; “under the wellformed-run premises, the clean prefix of a DBLog
   run replays to the source state at its frontier on its scope” is. Use the
   paper's status label **Machine-checked**, not the retired label
   `Conditional`.
3. **Never claim the work verifies an implementation.** It models a mechanism.
   Debezium, Apache Flink CDC, and Netflix's DBLog implement that mechanism;
   none of them is verified here.
4. **Preserve the deployment/observation split.** The verifier's `Accept` does
   not establish faithful source observation, and no theorem discharges the
   deployment obligations. See §7.
5. **Do not run `isabelle build` speculatively.** A full check takes minutes and
   needs Isabelle2025-2 plus a LaTeX toolchain. Read the sources instead unless
   the user asked for a build.
6. **Cite exact identifiers.** Version DOI when bytes matter, concept DOI when
   you mean “the artifact”. See §9.

## 5. Vocabulary (use these words precisely)

| Term | Meaning here |
|---|---|
| **source history** | The append-only sequence of source events; positions are *source coordinates*. |
| **frontier** | A position in the source event order at which a claim is made. The real-world analogue is an LSN or CDC watermark. |
| **scope** (`K`) | The set of keys a claim covers, e.g. one table's primary keys. Claims never extend past it. |
| **chunk** | A primary-key range read from the table. Its rows enter the stream as *refresh events*. |
| **CDC event** | A change event from the source log. A later CDC event dominates a stale refresh event for the same key. |
| **clean prefix** | The canonical replayable prefix constructed from a run: refresh and CDC events merged in source-coordinate order. |
| **virtual cut** | The property that replaying a bundle reaches the source state at a frontier on a scope. It is *extensional* — an equality of outcomes, not a physical snapshot read, and it asserts no single source timestamp across chunk rows. |
| **certificate** | The evidence object carrying scope, frontier and clean prefix. |
| **evidence** | The carrier recording the run backing a certificate. |
| **verify** | The three-way checker: `Accept`, `Reject`, `Unsupported`. |
| **wellformed run** (`WF`) | The run-model obligations: log retention, frontier discipline, watermark consistency, chunk-read honesty. |
| **faithful source observation** (`FSO`) | The assumption that the observation the checker consumes reflects the real source. External; not checkable from the certificate. |
| **deployment obligations** | The conditions a real deployment must establish (faithful CDC delivery, watermark placement, retention). Hypotheses here, not results. |
| **anchor domain / whole-table scope** | The Layer 4 machinery specializing a claim to an entire table. |

Avoid: “snapshot” unqualified (the point is that there is no physical
snapshot), “guarantees”, “ensures exactly-once”, “proves DBLog correct”.

## 6. Theorem index

Nine headline theorems. Locations are `formal/<file>:<line>` in the frozen tree.
Several also exist in locale form; the locale copy is the abstract statement,
the listed location is the public one.

### Core ladder

| # | Theorem | Location | Says |
|---|---|---|---|
| 1 | `wellformed_run_implies_virtual_cut` | `Virtual_Cut.thy:193` (locale: `DBLog_Run_Substrate_Layer2.thy:1780`) | A wellformed run's clean prefix replays to the source state at the run's frontier, restricted to the run's scope. |
| 2 | `accepted_certificate_implies_wellformed_run` | `Virtual_Cut.thy:595` (locale: `DBLog_Cert_Substrate.thy:230`) | An accepted certificate + faithful source observation is witnessed by a wellformed run coherent with the certificate. |
| 3 | `accepted_virtual_cut_sound` | `Virtual_Cut.thy:619` (locale: `DBLog_Cert_Substrate.thy:251`) | Hence an accepted certificate under faithful observation is a virtual cut on its certified scope and frontier. |
| 4 | `accepted_whole_table_anchor_domain_specialization` | `Layer4_Whole_Table.thy:91` (locale: `DBLog_Cert_Substrate.thy:274`) | With a whole-table claim scope, applying the clean prefix reproduces the entire source state at the frontier. |

Results 2–4 are proved inside the `layer3_checker_substrate` locale, which
abstracts the verifier as soundness obligations S1–S4. Those obligations are
discharged for the concrete verifier in `Virtual_Cut.thy`; quoting 2–4 without
noting they carry checker-substrate obligations is an under-statement of their
premises.

### Source-side continuation and restriction

| # | Theorem | Location | Says |
|---|---|---|---|
| 5 | `virtual_cut_state_continuation` | `Continuation.thy:440` | On a wellformed source history, a cut at `f` on `K` extends to any later `f'` by appending exactly the faithful CDC segment for `(f, f']` on `K`. |
| 6 | `virtual_cut_state_restrict_scope` | `Continuation.thy:564` | A cut on `K` restricts to any `K' ⊆ K`. Widening is not stated and would assert agreement on keys never certified. |
| 7 | `whole_table_state_continuation` | `Continuation.thy:604` | The whole-table instance of continuation. A scoped cut does not become whole-table for free. |
| 8 | `virtual_cut_restrict_to_subscope` | `Continuation.thy:640` (also `DBLog_Cert_Substrate_Inst.thy:61`) | An accepted certificate's cut restricts to a sub-scope **as a source-side state equality** — not as verifier acceptance of a restricted certificate. |
| 9 | `accepted_certificate_continuation_sound` | `Continuation.thy:685` (also `DBLog_Cert_Substrate_Inst.thy:83`) | Accessor-level continuation for an accepted certificate, inside the checker-substrate locale, with the continuation-segment faithfulness premise. |

**Non-vacuity.** `Public_Checker_Witness.thy` exhibits a concrete accepted
certificate/evidence pair, a deployment environment where faithful observation
genuinely holds, and fires all nine theorems at those witnesses. Two closing
exhibits — an accepted pair whose observation is unfaithful, and faithful
evidence the verifier rejects — show the two headline premises are independent.

**Modelling constraint.** The run- and certificate-layer results carry a
`linorder` hypothesis on the key type `'k`, from the deterministic enumeration
in the canonical clean-prefix construction. Theorems 5–8's state-level forms are
constraint-free.

## 7. Claims this work does not make

Correct these if you see them, including in your own drafts.

| Misreading | Correction |
|---|---|
| “Proves DBLog is correct.” | Proves properties of a *model* of the mechanism under stated premises. |
| “Proves exactly-once delivery.” | Delivery is out of scope. No theorem is a delivery claim. |
| “Guarantees the sink converges.” | Destination-side convergence needs a separate sink model; the paper marks it future work and a non-claim. |
| “Verifies Debezium / Flink CDC / Netflix's implementation.” | No implementation is verified. Those systems implement the same mechanism. |
| “The checker accepting means the data is right.” | `Accept` yields a virtual cut **only together with** faithful source observation and the checker-substrate obligations. |
| “The proofs discharge the operational assumptions.” | They are hypotheses. Deployment obligations and the external observation assumption are exactly what the kernel cannot check. |
| “A cut on a table's keys gives whole-table correctness.” | Only if the claim scope *is* the whole table (theorem 4). Scope widening is never claimed. |
| “It takes a consistent snapshot at a point in time.” | A virtual cut asserts an equality of outcomes at a frontier. No single source timestamp is claimed across chunk rows. |
| “38 theorems.” | 38 *theory files*; nine headline theorems. Twenty-four theory files are witnesses and fixtures. |

## 8. Verifying things yourself

```bash
# Find a theorem statement (frozen tree, stable line numbers)
grep -n "theorem accepted_virtual_cut_sound" formal/*.thy

# List every theorem in the development
grep -rn "^theorem " formal/*.thy

# Confirm nothing is admitted — empty output means clean. (The word
# "axiomatization" does appear in two documentation passages of
# Source_History.thy, which is why this grep anchors to command position.)
grep -rEn "^\s*(sorry|oops|axiomatization|typedecl|consts)\b" formal/*.thy

# Confirm this tree matches the archived artifact byte for byte
curl -sL https://zenodo.org/records/21732790/files/DBLog_Virtual_Cuts-2.1.tar.gz | tar xz
diff -r DBLog_Virtual_Cuts-2.1 formal        # no output = identical

# Full machine check (Isabelle2025-2, several minutes, LaTeX required)
isabelle build -d formal DBLog_Virtual_Cuts
```

The only `typedef` is the source coordinate type in `Source_History.thy`, a
conservative extension over a provably non-empty set with `linorder` and
`order_bot` instances proved rather than assumed.

## 9. Identifiers, versions, citation

| Object | Identifier |
|---|---|
| Paper | arXiv:2605.31475 — v1 29 May, v2 12 Jun, v3 8 Aug, **v4 13 Aug 2026** (current). 29 pages, cs.DB + cs.LO, CC BY 4.0. |
| Artifact, latest | Zenodo `10.5281/zenodo.21732790` (version 2.1, 1 Aug 2026), repo tag `v2.1` |
| Artifact, concept DOI | `10.5281/zenodo.20389696` — always resolves to the newest version |
| Artifact, earlier | `10.5281/zenodo.20652511` (2.0) · `10.5281/zenodo.20389697` (1.0) |
| Prior work | 2020 DBLog paper arXiv:2010.12597; Netflix Tech Blog, Dec 2019 |

ArXiv v2 cites artifact 2.0 (`10.5281/zenodo.20652511`). ArXiv v3 and v4 cite
artifact 2.1 (`10.5281/zenodo.21732790`) and carry the same 2.1 corpus as an
ancillary directory. The repository's `formal/` tree is byte-identical to that
v4 ancillary and the Zenodo deposit. Version 2.1 repairs a Layer 3 negative
control that failed to materialize its run (a vacuous control found by external
review) and adds a regression theory pinning the repair. **The nine headline
theorem statements are unchanged**; the repaired control's own statement is
strictly strengthened. Do not describe v2 as citing 2.1, or v3/v4 as citing
2.0.

BibTeX entries for both objects are in [`README.md`](README.md#citing) and
machine-readable metadata is in [`CITATION.cff`](CITATION.cff). Prefer those
over composing your own.

## 10. Answering common questions

| Question | Read |
|---|---|
| What is a virtual cut? | §5 above; paper §“Virtual Cuts” |
| What exactly is proved? | `docs/THEOREMS.md` — verbatim statements, premises, non-claims |
| Does this prove my pipeline is correct? | §7 above — no |
| How does DBLog work? | Paper §“The DBLog Mechanism”; the 2020 paper (arXiv:2010.12597) |
| What are the assumptions? | Paper's *Deployment obligations* and *External observation assumption*; `formal/README.md` → *Main results* |
| Why 38 theories for 9 theorems? | Fourteen carry definitions and results; twenty-four are constructed witnesses and fixtures guarding against vacuity. `formal/README.md` → *Contents* |
| What changed between artifact versions? | §9 above; `docs/PROVENANCE.md` |
