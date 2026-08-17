# Theorem index

The nine headline theorems, each with its **verbatim Isabelle statement**, a
reading in words, its premises, and what it does *not* say. Locations are
`formal/<file>:<line>` in the frozen tree; several theorems also exist in
locale form over abstract carriers, and those copies are noted.

Statements are transcribed from the sources. If this file and `formal/`
disagree, `formal/` is right and this file is a bug — please
[open an issue](../../../issues).

**Notation.** `b0` is the base state (a partial map from keys to values), `H`
the source history, `f` a frontier, `K` a key scope, `σ` a replay-event list,
`C` a certificate, `E` its evidence, `Raw` the raw source observation.
`Apply σ` replays `σ`; `Src b0 H f` is the source state at frontier `f`;
`x ↾ K` restricts to scope `K`.

---

## Core ladder (Layers 2–4)

### 1. `wellformed_run_implies_virtual_cut`

`formal/Virtual_Cut.thy:193` — locale form: `formal/DBLog_Run_Substrate_Layer2.thy:1780`

```isabelle
theorem wellformed_run_implies_virtual_cut:
  assumes "wellformed_dblog_run b0 R H"
  shows
    "virtual_cut_state b0 (clean_prefix_of R) (scope_of R)
                       (frontier_of R) H"
```

**In words.** The canonical clean prefix of a wellformed DBLog run is a virtual
cut: replaying it reaches the source state at the run's own frontier,
restricted to the run's own scope.

**Premises.** `wellformed_dblog_run b0 R H` — the run-model obligations:
source-log retention, frontier discipline, watermark consistency, chunk-read
honesty. This is the load-bearing hypothesis of the whole development; the
paper's *Deployment obligations* are what a real system must do to satisfy it.

**Does not say.** Nothing about a *certificate* — this is the run-level result.
Nothing about keys outside `scope_of R`, and nothing at frontiers other than
`frontier_of R`.

### 2. `accepted_certificate_implies_wellformed_run`

`formal/Virtual_Cut.thy:595` — locale form: `formal/DBLog_Cert_Substrate.thy:230`

```isabelle
theorem accepted_certificate_implies_wellformed_run:
  fixes b0 :: "'k ⇀ 'v"
    and H :: "('k, 'v) src_history"
    and Raw :: raw_observation
  assumes accept: "verify C E = Accept"
      and faithful: "faithful_source_observation E b0 H Raw"
  shows   "∃R. wellformed_dblog_run b0 R H ∧ cert_run_coherent C E R"
```

**In words.** A certificate the verifier accepts, together with a faithful
observation of the source, is witnessed by *some* wellformed run that is
coherent with the certificate.

**Premises.** Verifier acceptance; faithful source observation (`FSO`) — the
*External observation assumption*, which no certificate can establish on its
own. In the locale form, additionally the checker-substrate obligations S1–S4.

**Does not say.** That acceptance alone implies a wellformed run. `FSO` is not
a consequence of `Accept`; `formal/Public_Checker_Witness.thy` exhibits an
accepted pair whose observation is unfaithful, precisely to show the two
premises are independent.

### 3. `accepted_virtual_cut_sound`

`formal/Virtual_Cut.thy:619` — locale form: `formal/DBLog_Cert_Substrate.thy:251`

```isabelle
theorem accepted_virtual_cut_sound:
  fixes b0 :: "'k ⇀ 'v"
    and H :: "('k, 'v) src_history"
    and Raw :: raw_observation
  assumes accept: "verify C E = Accept"
      and faithful: "faithful_source_observation E b0 H Raw"
  shows   "virtual_cut b0 C H"
```

**In words.** The headline soundness result. An accepted certificate, under
faithful source observation, *is* a virtual cut: its certified replay reaches
the source state at the certified frontier, on the certified scope.

**Premises.** As for theorem 2.

**Does not say.** Anything about delivery, about the destination, or about keys
outside `scope C`. It does not say the data reached a sink, only that replaying
the certified prefix reaches the same per-key state the source had at
`frontier C` on `scope C`.

### 4. `accepted_whole_table_anchor_domain_specialization`

`formal/Layer4_Whole_Table.thy:91` — locale form: `formal/DBLog_Cert_Substrate.thy:274`

```isabelle
theorem accepted_whole_table_anchor_domain_specialization:
  fixes b0 :: "'k ⇀ 'v"
    and H :: "('k, 'v) src_history"
    and Raw :: raw_observation
    and b :: frontier
  assumes accept: "verify C E = Accept"
      and faithful: "faithful_source_observation E b0 H Raw"
      and whole: "whole_table_claim_scope b0 C H b"
  shows "Apply (clean_prefix C) = Src b0 H (frontier C)"
```

**In words.** When the certificate's claim scope *is* the whole table, the
equality holds unrestricted: applying the clean prefix reproduces the entire
source state at the frontier.

**Premises.** Acceptance, faithful observation, **and** the whole-table claim
scope condition `whole_table_claim_scope b0 C H b`.

**Does not say.** That a scoped cut can be widened. The whole-table condition is
a hypothesis, not something the verifier's `Accept` establishes.

> Theorems 2–4 are proved inside the `layer3_checker_substrate` locale, which
> abstracts the verifier as soundness obligations S1–S4. Those obligations are
> discharged for the concrete verifier in `formal/Virtual_Cut.thy`. Quoting
> these results without noting the checker-substrate obligations understates
> their premises.

---

## Source-side continuation and restriction

These are the promoted source-side fragment of the paper's certificate-algebra
catalog. Each is an `Apply`-against-`Src` equality proved over the core ladder,
without re-opening the run model.

### 5. `virtual_cut_state_continuation`

`formal/Continuation.thy:440`

```isabelle
theorem virtual_cut_state_continuation:
  fixes b0 :: "'k ⇀ 'v"
    and H :: "('k, 'v) src_history"
  assumes wfH: "wellformed_src_history H"
      and cut: "virtual_cut_state b0 σ K f H"
      and seg: "cdc_segment_between H K f f' δ"
  shows "virtual_cut_state b0 (σ @ δ) K f' H"
```

**In words.** A cut at frontier `f` on scope `K` advances to any later frontier
`f'` on the same scope by appending the CDC segment committed in the half-open
interval `(f, f']`, filtered to `K`.

**Premises.** A wellformed source history; the existing cut; and `seg` — the
appended segment must be *exactly* the faithful `cdc_segment_between` for
`(f, f']` on `K`. That last premise is the source-side faithfulness obligation:
in a deployment, it is a condition on the CDC stream, not a result.

**Does not say.** That any segment you happen to have is that segment. Missing
or duplicated events break `seg`, and with it the conclusion.

### 6. `virtual_cut_state_restrict_scope`

`formal/Continuation.thy:564`

```isabelle
theorem virtual_cut_state_restrict_scope:
  fixes b0 :: "'k ⇀ 'v"
  assumes cut: "virtual_cut_state b0 σ K f H"
      and sub: "K' ⊆ K"
  shows "virtual_cut_state b0 σ K' f H"
```

**In words.** A cut on scope `K` restricts to any sub-scope `K' ⊆ K`.

**Does not say.** The converse. Scope *widening* is not stated and would assert
agreement on keys the cut never certified.

### 7. `whole_table_state_continuation`

`formal/Continuation.thy:604`

```isabelle
theorem whole_table_state_continuation:
  fixes b0 :: "'k ⇀ 'v"
    and H :: "('k, 'v) src_history"
  assumes wfH: "wellformed_src_history H"
      and tab: "Apply σ = Src b0 H f"
      and seg: "cdc_segment_between H UNIV f f' δ"
  shows "Apply (σ @ δ) = Src b0 H f'"
```

**In words.** The whole-table instance of continuation: when the equality holds
unrestricted at `f` — the form theorem 4 yields — appending the full CDC segment
for `(f, f']` on all keys reaches the source state at `f'` on every key.

**Does not say.** That a scoped cut becomes whole-table for free. The unrestricted
equality is a hypothesis here, and the segment is over `UNIV`, not over a scope.

### 8. `virtual_cut_restrict_to_subscope`

`formal/Continuation.thy:640` — also `formal/DBLog_Cert_Substrate_Inst.thy:61`

```isabelle
theorem virtual_cut_restrict_to_subscope:
  fixes b0 :: "'k ⇀ 'v"
  assumes vc:  "virtual_cut b0 C H"
      and sub: "K' ⊆ scope C"
  shows "virtual_cut_state b0 (clean_prefix C) K' (frontier C) H"
```

**In words.** Read through its accessors, an accepted certificate's cut restricts
to any sub-scope as a source-side state equality.

**Does not say.** That a *restricted certificate* is accepted by the verifier.
Acceptance of any concrete restricted certificate is an evidence obligation, not
a consequence of the source-side algebra.

### 9. `accepted_certificate_continuation_sound`

`formal/Continuation.thy:685` — also `formal/DBLog_Cert_Substrate_Inst.thy:83`

```isabelle
theorem accepted_certificate_continuation_sound:
  fixes b0 :: "'k ⇀ 'v"
    and H :: "('k, 'v) src_history"
    and Raw :: raw_observation
  assumes accept:   "verify C E = Accept"
      and faithful: "faithful_source_observation E b0 H Raw"
      and wfH:      "wellformed_src_history H"
      and seg:      "cdc_segment_between H (scope C) (frontier C) f' δ"
  shows "virtual_cut_state b0 (clean_prefix C @ δ) (scope C) f' H"
```

**In words.** Accessor-level continuation for an accepted certificate: acceptance
plus faithful observation plus a faithful continuation segment extends the
certified cut to a later frontier on the same scope.

**Premises.** All four listed above, plus — in the locale form — the
checker-substrate obligations. This theorem carries the most premises in the
development; quote it with them.

**Does not say.** That the extended object is itself an accepted certificate.
The conclusion is a state equality, not a verifier verdict.

---

## Two properties of the whole set

**Non-vacuity.** `formal/Public_Checker_Witness.thy` exhibits a concrete
certificate/evidence pair that `verify` genuinely accepts, a deployment
environment in which `faithful_source_observation` genuinely holds, and fires
all nine theorems at those concrete witnesses. Two closing exhibits — an
accepted pair whose observation is unfaithful, and faithful evidence the
verifier rejects — show the two headline premises are independent and neither is
vacuous.

**The `linorder` constraint.** The run- and certificate-layer results carry a
`linorder` hypothesis on the key type `'k`. It enters through the canonical
clean-prefix construction in `formal/DBLog_Run_Core.thy`, which enumerates each
chunk-read domain with `sorted_list_of_set` and interleaves emitted events by
source coordinate with a stable `sort_key`, making "for each key in the chunk
domain" a deterministic enumeration; `clean_prefix_of` propagates it upward.
The four state-level continuation and restriction results (theorems 5–8) are
constraint-free. Database primary keys are totally ordered in practice, so the
hypothesis does not narrow the intended interpretation.

---

## Finding things yourself

```bash
# every theorem in the development
grep -rn "^theorem " formal/*.thy

# nothing admitted - empty output means clean
grep -rEn "^\s*(sorry|oops|axiomatization|typedecl|consts)\b" formal/*.thy

# full check (Isabelle2025-2)
isabelle build -d formal DBLog_Virtual_Cuts
```

The second grep anchors to command position on purpose. The word
`axiomatization` occurs in two documentation passages of
`formal/Source_History.thy` — both saying that none is used — so an unanchored
search reports those prose lines and appears to contradict the claim it is
meant to check.
