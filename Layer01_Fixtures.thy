theory Layer01_Fixtures
  imports DBLog_Run
begin

text \<open>
  Layer 0 and Layer 1 negative fixtures, with one boundary fixture.

  Each negative fixture proves @{const wellformed_src_history} or
  @{const wellformed_dblog_run} \<^emph>\<open>rejects\<close> a constructed
  instance, and the fixture proof extracts a designated violated
  wellformedness clause, showing that clause rejects the displayed
  shape. The fixtures are clause-targeting rejection proofs, not
  minimal one-clause countermodels, and are not intended to prove
  clause independence or minimality unless a section says so
  explicitly: an instance may violate more than its designated
  clause (@{text fix_row_abs} also fails WF6 main), and a fixture
  leaves unrelated accessors unconstrained rather than satisfying
  every other WF clause.

  Negative fixtures:

    \<^item> @{text "fix_h_c0"}     -- WF-H2 c0-event-exclusion (Layer 0);
    \<^item> @{text "fix_overlap"}  -- WF1 (b) chunk-domains pairwise
        disjoint;
    \<^item> @{text "fix_miss_cov"} -- WF1 (c) canonical-chunk-ownership
        domain equals scope;
    \<^item> @{text "fix_inf_dom"}  -- WF1 (f) chunk-domain finiteness;
    \<^item> @{text "fix_after_f"}  -- WF5 chunk-read coordinate at-or-
        before frontier;
    \<^item> @{text "fix_wrong_r"}  -- WF6 refresh correctness against
        @{const Src};
    \<^item> @{text "fix_same_c"}   -- WF6 specialized: same-coord
        read/event ambiguity;
    \<^item> @{text "fix_extra_cdc"} -- WF2 faithfulness (observed CDC
        not in source history);
    \<^item> @{text "fix_miss_dom"} -- WF2 coverage (post-chunk-read
        source event not in observed CDC -- the ``missing
        dominator'' shape);
    \<^item> @{text "fix_dup_mset"} -- WF2 post-read same-key/same-
        coordinate multiplicity (the @{text "[A, B, A]"} vs
        @{text "[A, B]"} missing-duplicate shape);
    \<^item> @{text "fix_dup_order"} -- WF2 order-preserving sublist
        (same multiset but wrong same-coordinate order);
    \<^item> @{text "fix_resp_dom"}  -- WF1 (d) responsible-chunk vs
        chunk-domain-membership disagreement;
    \<^item> @{text "fix_row_abs"}   -- WF6 row-absence (absence-Refresh
        in the clean prefix without the matching source state being
        empty for that key).

  Boundary fixture:

    \<^item> @{text "boundary_empty_scope"} -- wellformed run with
        @{text "scope_of R = {}"}; the WF body holds vacuously.
        Documents that empty scope is permitted by the predicate,
        with a non-empty-scope positive witness carried elsewhere.

  Construction approach. Each fixture is an independent section
  introducing a fresh family of constants via
  @{command axiomatization}, fixing every Layer 1 accessor value the
  WF body's relevant clause references. The fixture's main theorem
  unfolds @{const wellformed_dblog_run} (or
  @{const wellformed_src_history}), extracts the violated clause,
  and derives @{term False} from the axiomatized accessor values.
  Each fixture's constants are local to its section in narrative;
  they coexist in the theory's @{command consts} space without
  interaction because the WF predicate is invoked once per fixture
  on the fixture's own run / history.

  No WF7 clean-prefix CDC-coherence negative fixture appears in run
  form. Because @{const clean_prefix_of} is run-derived, the WF7
  clause holds for every run with no wellformedness premise (proved
  in the "WF7 clean-prefix CDC coherence holds for every run"
  section below), so a WF7-violating run is unconstructible. The
  building-block shapes a WF7 fixture would gesture at are exercised
  directly against @{const canonical_clean_prefix} in theory
  @{text Layer2_Fixtures}.
\<close>


section \<open>Layer 0 negative fixture: source event at c0\<close>

text \<open>
  Fixture: a source history with a single event at coordinate
  @{text c0} (the paper's banned coordinate per WF-H2). The history
  is rejected by @{const wellformed_src_history} because WF-H2's
  @{text "hist_coord (H ! i) \<noteq> c0"} clause fails on index
  @{text 0}.

  Why WF-H2 is load-bearing. Without WF-H2, an event at @{text c0}
  would mean @{text "Src(b0, H, c0) k = Some v"} for the event's key,
  contradicting the convention that @{text "Src(b0, H, c0) = b0"}
  unconditionally on wellformed histories. Layer 1's chunk-read
  reasoning uses the latter convention to discharge the boundary
  case where a chunk reads at @{text c0} (paper Lemma 1.1's chunk-
  read-at-base discharge). This fixture exhibits the rejection that
  makes the convention sound.
\<close>

definition H_c0 :: "(nat, nat) src_history" where
  "H_c0 = [(c0, Update 1 7)]"

lemma length_H_c0: "length H_c0 = 1"
  by (simp add: H_c0_def)

lemma H_c0_nth_0: "H_c0 ! 0 = (c0, Update 1 7)"
  by (simp add: H_c0_def)

theorem fix_h_c0_rejected:
  "\<not> wellformed_src_history H_c0"
proof
  assume H: "wellformed_src_history H_c0"
  hence wfh2: "\<forall>i. i < length H_c0 \<longrightarrow> hist_coord (H_c0 ! i) \<noteq> c0"
    unfolding wellformed_src_history_def by blast
  have "(0::nat) < length H_c0" using length_H_c0 by simp
  with wfh2 have "hist_coord (H_c0 ! 0) \<noteq> c0" by blast
  thus False using H_c0_nth_0 by simp
qed


section \<open>Layer 1 negative fixture: overlapping chunk domains (WF1 (b))\<close>

text \<open>
  Fixture: two chunks @{text "ov_chA / ov_chB"} with intersecting
  @{const chunk_domain}s. WF1 (b) requires pairwise disjointness;
  the fixture's domains share key @{text 2}, so WF1 (b) rejects.

  Why WF1 (b) is load-bearing. Without disjointness, two chunks
  could each claim a Refresh for the same key with conflicting
  observations; @{text Apply} on the resulting clean prefix would
  deterministically use whichever Refresh appears last (per
  @{const apply_step}), but Lemma 1.1's source-side equality would
  not be established because the pairing of source events to
  chunk-read coordinates becomes ambiguous (which chunk's
  @{text chunk_read_coordinate} gates the dominating-CDC
  computation for the contended key?). The canonical chunk
  partition pre-empts this by forbidding overlap; the fixture
  exhibits the rejection.
\<close>

axiomatization
  R_ov   :: "(nat, nat) run" and
  ov_chA :: "(nat, nat) chunk" and
  ov_chB :: "(nat, nat) chunk"
where
      ov_chunks_distinct: "ov_chA \<noteq> ov_chB"
  and ov_chunks_set:      "chunks R_ov = {ov_chA, ov_chB}"
  and ov_dom_A:           "chunk_domain R_ov ov_chA = {1, 2}"
  and ov_dom_B:           "chunk_domain R_ov ov_chB = {2, 3}"

definition b0_ov :: "nat \<rightharpoonup> nat" where
  "b0_ov = (\<lambda>k. None)"

definition H_ov :: "(nat, nat) src_history" where
  "H_ov = []"

theorem fix_overlap_rejected:
  "\<not> wellformed_dblog_run b0_ov R_ov H_ov"
proof
  assume H: "wellformed_dblog_run b0_ov R_ov H_ov"
  hence wf1b:
    "\<forall>ch1 \<in> chunks R_ov. \<forall>ch2 \<in> chunks R_ov.
        ch1 \<noteq> ch2 \<longrightarrow> chunk_domain R_ov ch1 \<inter> chunk_domain R_ov ch2 = {}"
    unfolding wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have inA: "ov_chA \<in> chunks R_ov" using ov_chunks_set by simp
  have inB: "ov_chB \<in> chunks R_ov" using ov_chunks_set by simp
  from wf1b inA inB ov_chunks_distinct
  have "chunk_domain R_ov ov_chA \<inter> chunk_domain R_ov ov_chB = {}"
    by blast
  with ov_dom_A ov_dom_B have "(2::nat) \<notin> ({1, 2} \<inter> {2, 3})" by simp
  thus False by simp
qed


section \<open>Layer 1 negative fixture: chunk owns out-of-scope key (WF1 (c))\<close>

text \<open>
  Fixture: a single chunk @{text mc_ch} with
  @{text "chunk_domain R_mc mc_ch = {1, 2}"}, but
  @{text "scope_of R_mc = {1}"}. The canonical chunk-ownership
  domain (union of all chunk domains) is @{text "{1, 2}"}; WF1 (c)
  requires it to equal @{text "scope_of R_mc"}; the fixture violates
  this because @{text mc_ch} owns the out-of-scope key @{text 2}.

  Why WF1 (c) is load-bearing, distinctly from WF1 (a). WF1 (a)
  (each in-scope key has a unique owning chunk) already forces
  @{text "scope_of R \<subseteq> canonical_chunk_ownership_domain R"};
  WF1 (c) strengthens that containment to an equality and so is the
  only clause ruling out the reverse direction --- a chunk owning a
  key outside the claimed scope. This fixture targets exactly that
  direction: WF1 (a) is satisfiable here (the sole in-scope key
  @{text 1} is owned by @{text mc_ch}), so the rejection isolates
  WF1 (c)'s exact-domain-equality role rather than a coverage gap
  WF1 (a) would itself catch. Without the equality, a chunk could
  emit Refresh events for keys outside @{const scope_of}, placing
  out-of-scope replay events into the canonical clean prefix and
  leaving the Layer 2 scope-restricted equality no longer
  characterizing it.
\<close>

axiomatization
  R_mc  :: "(nat, nat) run" and
  mc_ch :: "(nat, nat) chunk"
where
      mc_chunks_set: "chunks R_mc = {mc_ch}"
  and mc_dom:        "chunk_domain R_mc mc_ch = {1, 2}"
  and mc_scope:      "scope_of R_mc = {1}"

definition b0_mc :: "nat \<rightharpoonup> nat" where
  "b0_mc = (\<lambda>k. None)"

definition H_mc :: "(nat, nat) src_history" where
  "H_mc = []"

theorem fix_miss_cov_rejected:
  "\<not> wellformed_dblog_run b0_mc R_mc H_mc"
proof
  assume H: "wellformed_dblog_run b0_mc R_mc H_mc"
  hence wf1c: "canonical_chunk_ownership_domain R_mc = scope_of R_mc"
    unfolding wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have "canonical_chunk_ownership_domain R_mc = {1, 2}"
    unfolding canonical_chunk_ownership_domain_def
    using mc_chunks_set mc_dom by simp
  with wf1c mc_scope have "({1, 2::nat}) = {1}" by simp
  thus False by auto
qed


section \<open>Layer 1 negative fixture: infinite chunk domain (WF1 (f))\<close>

text \<open>
  Fixture: a single chunk @{text inf_ch} with
  @{text "chunk_domain R_inf inf_ch = (UNIV :: nat set)"}. WF1 (f)
  requires every chunk's domain to be finite; the fixture's domain
  is the infinite set of natural numbers.

  Why WF1 (f) is load-bearing. The Layer 1 chunk-plan model is
  intended to be executable -- chunk plans materialize as finite
  records -- and the WF1 (a)..(e) bookkeeping (unique responsible
  chunk per in-scope key, etc.) is over a bounded key set per chunk.
  Without finiteness, WF4's "for every k in chunk_domain" obligation
  becomes infeasible to satisfy via finite chunk-read records.
\<close>

axiomatization
  R_inf  :: "(nat, nat) run" and
  inf_ch :: "(nat, nat) chunk"
where
      inf_chunks_set: "chunks R_inf = {inf_ch}"
  and inf_dom:        "chunk_domain R_inf inf_ch = (UNIV :: nat set)"

definition b0_inf :: "nat \<rightharpoonup> nat" where
  "b0_inf = (\<lambda>k. None)"

definition H_inf :: "(nat, nat) src_history" where
  "H_inf = []"

theorem fix_inf_dom_rejected:
  "\<not> wellformed_dblog_run b0_inf R_inf H_inf"
proof
  assume H: "wellformed_dblog_run b0_inf R_inf H_inf"
  hence wf1f2: "\<forall>ch \<in> chunks R_inf. finite (chunk_domain R_inf ch)"
    unfolding wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have "inf_ch \<in> chunks R_inf" using inf_chunks_set by simp
  with wf1f2 have "finite (chunk_domain R_inf inf_ch)" by blast
  with inf_dom have "finite (UNIV :: nat set)" by simp
  thus False by simp
qed


section \<open>Layer 1 negative fixture: chunk read after frontier (WF5)\<close>

text \<open>
  Fixture: a single chunk @{text caf_ch} with
  @{text "chunk_read_coordinate R_caf caf_ch = caf_c1"} and
  @{text "frontier_of R_caf = c0"}, where @{text "src_lt c0 caf_c1"}
  -- the chunk read happened strictly past the certified frontier.
  WF5 requires @{text "chunk_read_coordinate R ch \<le>\<^sub>src frontier_of R"};
  the fixture violates this.

  Why WF5 is load-bearing. Without WF5, a chunk could read at a
  coordinate ahead of the frontier; the Refresh's observation would
  describe a state past what the certificate claims to certify, and
  Lemma 1.1's @{text "Apply (clean_prefix_of R) \<restriction> scope =
  Src(b0, H, frontier_of R) \<restriction> scope"} equality would fail because
  the chunk-read state is not the source state at the frontier.
\<close>

axiomatization caf_c1 :: src_coord
  where caf_c0_lt_c1: "src_lt c0 caf_c1"

lemma caf_not_src_le_c1_c0: "\<not> src_le caf_c1 c0"
  using caf_c0_lt_c1 src_le_antisym
  unfolding src_lt_def by blast

axiomatization
  R_caf  :: "(nat, nat) run" and
  caf_ch :: "(nat, nat) chunk"
where
      caf_chunks_set:    "chunks R_caf = {caf_ch}"
  and caf_frontier:      "frontier_of R_caf = c0"
  and caf_read_coord:    "chunk_read_coordinate R_caf caf_ch = caf_c1"

definition b0_caf :: "nat \<rightharpoonup> nat" where
  "b0_caf = (\<lambda>k. None)"

definition H_caf :: "(nat, nat) src_history" where
  "H_caf = []"

theorem fix_after_f_rejected:
  "\<not> wellformed_dblog_run b0_caf R_caf H_caf"
proof
  assume H: "wellformed_dblog_run b0_caf R_caf H_caf"
  hence wf5: "\<forall>ch \<in> chunks R_caf.
                src_le (chunk_read_coordinate R_caf ch) (frontier_of R_caf)"
    unfolding wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have "caf_ch \<in> chunks R_caf" using caf_chunks_set by simp
  with wf5 have "src_le (chunk_read_coordinate R_caf caf_ch) (frontier_of R_caf)"
    by blast
  with caf_read_coord caf_frontier have "src_le caf_c1 c0" by simp
  with caf_not_src_le_c1_c0 show False by blast
qed


section \<open>Layer 1 negative fixture: wrong refresh value (WF6)\<close>

text \<open>
  Fixture: a single chunk @{text wr_ch} reading at @{text c0} on key
  @{text 1}, with
  @{text "chunk_read_result R_wr wr_ch 1 = Some (Some 99)"} but
  @{text "b0_wr 1 = Some 5"} and @{text "H_wr = []"}. WF6 requires
  @{text "m = Src b0 H (chunk_read_coordinate R ch) k"} on observed
  Refreshes; here @{text "Some 99 \<noteq> Some 5 = Src b0_wr H_wr c0 1"},
  so WF6 rejects.

  Why WF6 is load-bearing. Without WF6, a chunk-read could record
  any value, severing the link between observed Refreshes and the
  source state. Lemma 1.1's chunk-read-at-base discharge depends on
  the Refresh's recorded value matching @{const Src} at the read
  coordinate.
\<close>

axiomatization
  R_wr  :: "(nat, nat) run" and
  wr_ch :: "(nat, nat) chunk"
where
      wr_chunks_set:    "chunks R_wr = {wr_ch}"
  and wr_dom:           "chunk_domain R_wr wr_ch = {1}"
  and wr_read_coord:    "chunk_read_coordinate R_wr wr_ch = c0"
  and wr_chunk_read_result:
        "chunk_read_result R_wr wr_ch 1 = Some (Some 99)"

definition b0_wr :: "nat \<rightharpoonup> nat" where
  "b0_wr = (\<lambda>k. if k = 1 then Some 5 else None)"

definition H_wr :: "(nat, nat) src_history" where
  "H_wr = []"

lemma latest_src_event_H_wr_c0_1:
  "latest_src_event H_wr c0 (1::nat) = None"
  unfolding latest_src_event_def by (simp add: H_wr_def)

lemma Src_b0_wr_H_wr_c0_1: "Src b0_wr H_wr c0 (1::nat) = Some 5"
  unfolding Src_def using latest_src_event_H_wr_c0_1
  by (simp add: b0_wr_def)

theorem fix_wrong_r_rejected:
  "\<not> wellformed_dblog_run b0_wr R_wr H_wr"
proof
  assume H: "wellformed_dblog_run b0_wr R_wr H_wr"
  hence wf6:
    "\<forall>ch \<in> chunks R_wr. \<forall>k \<in> chunk_domain R_wr ch. \<forall>m.
        chunk_read_result R_wr ch k = Some m
          \<longrightarrow> m = Src b0_wr H_wr (chunk_read_coordinate R_wr ch) k"
    unfolding wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have inCh: "wr_ch \<in> chunks R_wr" using wr_chunks_set by simp
  have inK: "(1::nat) \<in> chunk_domain R_wr wr_ch" using wr_dom by simp
  from wf6 inCh inK wr_chunk_read_result
  have "Some 99 = Src b0_wr H_wr (chunk_read_coordinate R_wr wr_ch) (1::nat)"
    by blast
  with wr_read_coord Src_b0_wr_H_wr_c0_1 have "Some 99 = (Some (5::nat))" by simp
  thus False by simp
qed


section \<open>Layer 1 negative fixture: same-coord read/event ambiguity (WF6)\<close>

text \<open>
  Fixture: source event at coordinate @{text sc_c1} (an
  @{text "Update 1 7"}) AND chunk read at coordinate @{text sc_c1}
  with @{text "chunk_read_result = Some (Some 5)"} (the pre-event
  value). The convention is that chunk reads at @{text c} observe
  AFTER source events at @{text c}, so
  @{text "Src(b0, H, sc_c1)(1) = Some 7"} (the Update's value); the
  fixture's chunk read records @{text 5}, mismatching the convention.
  WF6 rejects on the @{text "Some 5 \<noteq> Some 7"} discrepancy.

  Why the same-coord convention is load-bearing. Without it, a chunk
  read at the same coordinate as a source event would have no
  determinate ``before-or-after-the-event'' interpretation; WF6's
  @{text "m = Src b0 H (chunk_read_coordinate R ch) k"} check would
  be ambiguous because @{const Src}'s @{const latest_src_event}
  filter is inclusive on @{text "src_le"} and would always pick up
  the same-coord event. The fixture exhibits the rejection in the
  ``before'' interpretation.
\<close>

axiomatization sc_c1 :: src_coord
  where sc_c0_lt_c1: "src_lt c0 sc_c1"

lemma sc_c1_le_c1: "src_le sc_c1 sc_c1"
  by (rule src_le_refl)

axiomatization
  R_sc  :: "(nat, nat) run" and
  sc_ch :: "(nat, nat) chunk"
where
      sc_chunks_set:    "chunks R_sc = {sc_ch}"
  and sc_dom:           "chunk_domain R_sc sc_ch = {1}"
  and sc_read_coord:    "chunk_read_coordinate R_sc sc_ch = sc_c1"
  and sc_chunk_read_result:
        "chunk_read_result R_sc sc_ch 1 = Some (Some 5)"

definition b0_sc :: "nat \<rightharpoonup> nat" where
  "b0_sc = (\<lambda>k. if k = 1 then Some 5 else None)"

definition H_sc :: "(nat, nat) src_history" where
  "H_sc = [(sc_c1, Update 1 7)]"

lemma length_H_sc: "length H_sc = 1" by (simp add: H_sc_def)

lemma H_sc_nth_0: "H_sc ! 0 = (sc_c1, Update 1 7)"
  by (simp add: H_sc_def)

lemma latest_src_event_H_sc_c1_1:
  "latest_src_event H_sc sc_c1 (1::nat) = Some 0"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_sc ! i)) sc_c1
                \<and> key_of (hist_event (H_sc ! i)) = (1::nat)"
  have "filter ?P [0] = [0]"
    using H_sc_nth_0 sc_c1_le_c1 by simp
  thus ?thesis
    unfolding latest_src_event_def
    using length_H_sc by simp
qed

lemma Src_b0_sc_H_sc_c1_1: "Src b0_sc H_sc sc_c1 (1::nat) = Some 7"
  unfolding Src_def
  using latest_src_event_H_sc_c1_1 H_sc_nth_0 by simp

theorem fix_same_c_rejected:
  "\<not> wellformed_dblog_run b0_sc R_sc H_sc"
proof
  assume H: "wellformed_dblog_run b0_sc R_sc H_sc"
  hence wf6:
    "\<forall>ch \<in> chunks R_sc. \<forall>k \<in> chunk_domain R_sc ch. \<forall>m.
        chunk_read_result R_sc ch k = Some m
          \<longrightarrow> m = Src b0_sc H_sc (chunk_read_coordinate R_sc ch) k"
    unfolding wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have inCh: "sc_ch \<in> chunks R_sc" using sc_chunks_set by simp
  have inK: "(1::nat) \<in> chunk_domain R_sc sc_ch" using sc_dom by simp
  from wf6 inCh inK sc_chunk_read_result
  have "Some 5 = Src b0_sc H_sc (chunk_read_coordinate R_sc sc_ch) (1::nat)"
    by blast
  with sc_read_coord Src_b0_sc_H_sc_c1_1 have "Some 5 = (Some (7::nat))" by simp
  thus False by simp
qed


section \<open>Layer 1 negative fixture: extra observed CDC (WF2 faithfulness)\<close>

text \<open>
  The ``observed CDC not in source history'' / ``faithfulness''
  shape. Fixture: @{text "src_history_of R_ec = []"} but
  @{text "cdc_events_of R_ec = [(ec_c1, Insert 1 5)]"} -- the run
  records an observed CDC event that has no corresponding source-
  history entry. WF2 faithfulness rejects: every observed CDC pair
  whose key is in scope and whose coordinate is at-or-before the
  frontier must appear in @{text src_history_of}.

  Why WF2 faithfulness is load-bearing. Without it, a run could
  fabricate observed CDC events; @{const Apply} on the clean prefix
  would produce per-key states unsupported by the source side, and
  Lemma 1.1's source-side equality would fail because
  @{const Src} ranges only over genuine source history.
\<close>

axiomatization ec_c1 :: src_coord
  where ec_c0_lt_c1: "src_lt c0 ec_c1"

lemma ec_c1_le_c1: "src_le ec_c1 ec_c1"
  by (rule src_le_refl)

axiomatization
  R_ec  :: "(nat, nat) run" and
  ec_ch :: "(nat, nat) chunk"
where
      ec_chunks_set:    "chunks R_ec = {ec_ch}"
  and ec_scope:         "scope_of R_ec = {1}"
  and ec_frontier:      "frontier_of R_ec = ec_c1"
  and ec_src_history:   "src_history_of R_ec = []"
  and ec_cdc_events:    "cdc_events_of R_ec = [(ec_c1, Insert 1 5)]"

definition b0_ec :: "nat \<rightharpoonup> nat" where
  "b0_ec = (\<lambda>k. None)"

theorem fix_extra_cdc_rejected:
  "\<not> wellformed_dblog_run b0_ec R_ec [] "
proof
  assume H: "wellformed_dblog_run b0_ec R_ec []"
  hence wf2f:
    "\<forall>p \<in> set (cdc_events_of R_ec).
        key_of (hist_event p) \<in> scope_of R_ec
        \<and> src_le (hist_coord p) (frontier_of R_ec)
        \<longrightarrow> p \<in> set (src_history_of R_ec)"
    unfolding wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have memSet: "(ec_c1, Insert 1 5) \<in> set (cdc_events_of R_ec)"
    using ec_cdc_events by simp
  have inScope: "key_of (hist_event ((ec_c1, Insert (1::nat) 5))) \<in> scope_of R_ec"
    using ec_scope by simp
  have leF: "src_le (hist_coord ((ec_c1, Insert (1::nat) 5))) (frontier_of R_ec)"
    using ec_frontier ec_c1_le_c1 by simp
  from wf2f memSet inScope leF
  have inSrc: "(ec_c1, Insert (1::nat) 5) \<in> set (src_history_of R_ec)" by blast
  with ec_src_history show False by simp
qed


section \<open>Layer 1 negative fixture: missing dominator (WF2 coverage)\<close>

text \<open>
  The ``omits suppression at the structural level'' shape: a
  sequence where the dominating CDC event is MISSING (not
  present-after-the-refresh). Fixture: a chunk reading at
  @{text c0}, an in-scope source event at @{text md_c1} above
  @{text c0} with key @{text 1}, but
  @{text "cdc_events_of R_md = []"} -- the run drops the dominating
  CDC event. WF2 coverage requires @{text "covers_ordinary_cdc R k
  (frontier_of R)"} for every in-scope key; that predicate insists
  the source event in @{text "(chunk_read_coordinate, frontier_of R]"}
  appears in @{const cdc_events_of}; the fixture's empty
  @{const cdc_events_of} fails the existential.

  Why WF2 coverage is load-bearing. Without it, ordinary CDC events
  could be dropped from observed CDC; @{const Apply} on the clean
  prefix would skip those keys, and Lemma 1.1's source-side equality
  would fail because @{const Src} sees the dropped events but
  @{const Apply} does not. This is the structural shape the
  ``missing dominator'' fixture exhibits.
\<close>

axiomatization md_c1 :: src_coord
  where md_c0_lt_c1: "src_lt c0 md_c1"

lemma md_c0_le_c1: "src_le c0 md_c1"
  using md_c0_lt_c1 unfolding src_lt_def by simp

lemma md_c1_le_c1: "src_le md_c1 md_c1"
  by (rule src_le_refl)

axiomatization
  R_md  :: "(nat, nat) run" and
  md_ch :: "(nat, nat) chunk"
where
      md_chunks_set:    "chunks R_md = {md_ch}"
  and md_scope:         "scope_of R_md = {1}"
  and md_frontier:      "frontier_of R_md = md_c1"
  and md_dom:           "chunk_domain R_md md_ch = {1}"
  \<comment> \<open>No explicit @{text "md_owns_1"} axiom is needed; it follows
       from @{text md_dom} via @{const owns} = set membership.
       The fixture's rejection proof unfolds WF2 coverage which
       indexes through @{text md_resp_1}, not @{text owns} directly.\<close>
  and md_resp_1:        "responsible_chunk R_md 1 = Some md_ch"
  and md_read_coord:    "chunk_read_coordinate R_md md_ch = c0"
  and md_src_history:   "src_history_of R_md = [(md_c1, Update 1 7)]"
  and md_cdc_events:    "cdc_events_of R_md = []"

definition b0_md :: "nat \<rightharpoonup> nat" where
  "b0_md = (\<lambda>k. None)"

definition H_md :: "(nat, nat) src_history" where
  "H_md = [(md_c1, Update 1 7)]"

lemma length_H_md: "length H_md = 1" by (simp add: H_md_def)

lemma H_md_nth_0: "H_md ! 0 = (md_c1, Update 1 7)"
  by (simp add: H_md_def)

theorem fix_miss_dom_rejected:
  "\<not> wellformed_dblog_run b0_md R_md H_md"
proof
  assume H: "wellformed_dblog_run b0_md R_md H_md"
  hence wf2c: "\<forall>k \<in> scope_of R_md. covers_ordinary_cdc R_md k (frontier_of R_md)"
    unfolding wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have k1: "(1::nat) \<in> scope_of R_md" using md_scope by simp
  with wf2c have cov: "covers_ordinary_cdc R_md (1::nat) (frontier_of R_md)" by blast
  from cov obtain ch where
    ch_resp: "responsible_chunk R_md 1 = Some ch" and
    ch_cov:  "\<forall>i. i < length (src_history_of R_md)
                  \<longrightarrow> src_lt (chunk_read_coordinate R_md ch)
                              (hist_coord (src_history_of R_md ! i))
                  \<longrightarrow> src_le (hist_coord (src_history_of R_md ! i)) (frontier_of R_md)
                  \<longrightarrow> key_of (hist_event (src_history_of R_md ! i)) = (1::nat)
                  \<longrightarrow> src_history_of R_md ! i \<in> set (cdc_events_of R_md)"
    unfolding covers_ordinary_cdc_def by blast
  from ch_resp md_resp_1 have ch_eq: "ch = md_ch" by simp
  have idx_lt: "(0::nat) < length (src_history_of R_md)"
    using md_src_history by simp
  have lt_premise: "src_lt (chunk_read_coordinate R_md md_ch)
                           (hist_coord (src_history_of R_md ! 0))"
    using md_read_coord md_src_history md_c0_lt_c1 by simp
  have le_premise: "src_le (hist_coord (src_history_of R_md ! 0))
                           (frontier_of R_md)"
    using md_src_history md_frontier md_c1_le_c1 by simp
  have key_premise: "key_of (hist_event (src_history_of R_md ! 0)) = (1::nat)"
    using md_src_history by simp
  from ch_cov ch_eq idx_lt lt_premise le_premise key_premise
  have "src_history_of R_md ! 0 \<in> set (cdc_events_of R_md)" by blast
  with md_src_history md_cdc_events show False by simp
qed


section \<open>Layer 1 negative fixture: duplicate multiplicity gap (WF2 mset)\<close>

text \<open>
  Duplicate same-key/same-coordinate regression fixture. Source has
  the same key and source coordinate slice @{text "[A, B, A]"}, but
  observed CDC has only @{text "[A, B]"}. Set membership and
  order-preserving sublist are insufficient for this shape; the WF2
  multiset clause rejects it by counting duplicate occurrences.
\<close>

axiomatization dm_c1 :: src_coord
  where dm_c0_lt_c1: "src_lt c0 dm_c1"

lemma dm_c1_le_c1: "src_le dm_c1 dm_c1"
  by (rule src_le_refl)

axiomatization
  R_dm  :: "(nat, nat) run" and
  dm_ch :: "(nat, nat) chunk"
where
      dm_scope:       "scope_of R_dm = {1}"
  and dm_frontier:    "frontier_of R_dm = dm_c1"
  and dm_resp_1:      "responsible_chunk R_dm 1 = Some dm_ch"
  and dm_read_coord:  "chunk_read_coordinate R_dm dm_ch = c0"
  and dm_src_history:
      "src_history_of R_dm =
         [(dm_c1, Update 1 5), (dm_c1, Update 1 6), (dm_c1, Update 1 5)]"
  and dm_cdc_events:
      "cdc_events_of R_dm =
         [(dm_c1, Update 1 5), (dm_c1, Update 1 6)]"

definition b0_dm :: "nat \<rightharpoonup> nat" where
  "b0_dm = (\<lambda>k. None)"

definition H_dm :: "(nat, nat) src_history" where
  "H_dm =
     [(dm_c1, Update 1 5), (dm_c1, Update 1 6), (dm_c1, Update 1 5)]"

theorem fix_dup_mset_rejected:
  "\<not> wellformed_dblog_run b0_dm R_dm H_dm"
proof
  assume H: "wellformed_dblog_run b0_dm R_dm H_dm"
  hence wf2_mset:
    "\<forall>k\<in>scope_of R_dm. \<forall>ch c.
        responsible_chunk R_dm k = Some ch
        \<and> src_lt (chunk_read_coordinate R_dm ch) c
        \<and> src_le c (frontier_of R_dm)
        \<longrightarrow>
          mset (source_key_coord_slice k c (cdc_events_of R_dm))
          = mset (source_key_coord_slice k c (src_history_of R_dm))"
    unfolding wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have ms:
    "mset (source_key_coord_slice (1::nat) dm_c1 (cdc_events_of R_dm))
     = mset (source_key_coord_slice (1::nat) dm_c1 (src_history_of R_dm))"
  proof -
    have k_scope: "(1::nat) \<in> scope_of R_dm"
      using dm_scope by simp
    from wf2_mset k_scope
    have inst:
      "\<forall>ch c.
        responsible_chunk R_dm (1::nat) = Some ch
        \<and> src_lt (chunk_read_coordinate R_dm ch) c
        \<and> src_le c (frontier_of R_dm)
        \<longrightarrow>
          mset (source_key_coord_slice (1::nat) c (cdc_events_of R_dm))
          = mset (source_key_coord_slice (1::nat) c (src_history_of R_dm))"
      by blast
    have prem:
      "responsible_chunk R_dm (1::nat) = Some dm_ch
       \<and> src_lt (chunk_read_coordinate R_dm dm_ch) dm_c1
       \<and> src_le dm_c1 (frontier_of R_dm)"
      using dm_resp_1 dm_read_coord dm_c0_lt_c1 dm_frontier dm_c1_le_c1
      by simp
    show ?thesis using inst prem by blast
  qed
  have bad_mset:
    "mset [(dm_c1, Update (1::nat) (5::nat)), (dm_c1, Update 1 (6::nat))]
     = mset [(dm_c1, Update (1::nat) (5::nat)), (dm_c1, Update 1 (6::nat)),
             (dm_c1, Update 1 (5::nat))]"
    using ms dm_cdc_events dm_src_history
    by (simp add: source_key_coord_slice_def)
  hence "length [(dm_c1, Update (1::nat) (5::nat)), (dm_c1, Update 1 (6::nat))]
       = length [(dm_c1, Update (1::nat) (5::nat)), (dm_c1, Update 1 (6::nat)),
                 (dm_c1, Update 1 (5::nat))]"
    by (rule mset_eq_length)
  thus False by simp
qed


section \<open>Layer 1 negative fixture: duplicate order gap (WF2 sublist)\<close>

text \<open>
  Companion duplicate-order regression fixture. Source has same-key /
  same-coordinate slice @{text "[A, B, A]"} and CDC has
  @{text "[A, A, B]"}. The multisets match, but there is no
  order-preserving embedding of the CDC slice into the source slice;
  this keeps the WF2 strict-mono / subsequence side load-bearing.
\<close>

axiomatization do_c1 :: src_coord
  where do_c0_lt_c1: "src_lt c0 do_c1"

lemma do_c1_le_c1: "src_le do_c1 do_c1"
  by (rule src_le_refl)

axiomatization
  R_do  :: "(nat, nat) run" and
  do_ch :: "(nat, nat) chunk"
where
      do_scope:       "scope_of R_do = {1}"
  and do_frontier:    "frontier_of R_do = do_c1"
  and do_src_history:
      "src_history_of R_do =
         [(do_c1, Update 1 5), (do_c1, Update 1 6), (do_c1, Update 1 5)]"
  and do_cdc_events:
      "cdc_events_of R_do =
         [(do_c1, Update 1 5), (do_c1, Update 1 5), (do_c1, Update 1 6)]"

definition b0_do :: "nat \<rightharpoonup> nat" where
  "b0_do = (\<lambda>k. None)"

definition H_do :: "(nat, nat) src_history" where
  "H_do =
     [(do_c1, Update 1 5), (do_c1, Update 1 6), (do_c1, Update 1 5)]"

theorem fix_dup_order_rejected:
  "\<not> wellformed_dblog_run b0_do R_do H_do"
proof
  assume H: "wellformed_dblog_run b0_do R_do H_do"
  hence wf2_order:
    "\<exists>\<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
        \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of R_do
                                 \<and> src_le (hist_coord p) (frontier_of R_do));
               cdc_in_slice  = filter in_slice (cdc_events_of R_do);
               hist_in_slice = filter in_slice (src_history_of R_do)
           in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                   \<iota> i < length hist_in_slice
                 \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
    unfolding wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  then obtain \<iota> :: "nat \<Rightarrow> nat" where
    iota_mono: "strict_mono \<iota>" and
    iota_hits:
      "(let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of R_do
                              \<and> src_le (hist_coord p) (frontier_of R_do));
            cdc_in_slice  = filter in_slice (cdc_events_of R_do);
            hist_in_slice = filter in_slice (src_history_of R_do)
        in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                \<iota> i < length hist_in_slice
              \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
    by blast
  let ?in_slice =
    "\<lambda>p. key_of (hist_event p) \<in> scope_of R_do
          \<and> src_le (hist_coord p) (frontier_of R_do)"
  have sub:
    "subseq (filter ?in_slice (cdc_events_of R_do))
            (filter ?in_slice (src_history_of R_do))"
  proof (rule subseq_from_strict_mono_nth[OF iota_mono])
    fix i
    assume i_lt: "i < length (filter ?in_slice (cdc_events_of R_do))"
    show "\<iota> i < length (filter ?in_slice (src_history_of R_do))
          \<and> filter ?in_slice (cdc_events_of R_do) ! i
             = filter ?in_slice (src_history_of R_do) ! \<iota> i"
      using iota_hits i_lt by (simp add: Let_def)
  qed
  have impossible:
    "subseq [(do_c1, Update (1::nat) (5::nat)), (do_c1, Update 1 (5::nat)),
             (do_c1, Update 1 (6::nat))]
            [(do_c1, Update (1::nat) (5::nat)), (do_c1, Update 1 (6::nat)),
             (do_c1, Update 1 (5::nat))]"
    using sub do_scope do_frontier do_cdc_events do_src_history do_c1_le_c1
    by simp
  thus False by simp
qed


section \<open>Layer 1 boundary fixture: empty scope (vacuous wellformedness)\<close>

text \<open>
  Fixture: a run with @{text "scope_of R_es = {}"} and no chunks.
  The WF body holds vacuously (every universally-quantified clause
  over scope or chunks is true on the empty domain).

  Documents the boundary: empty scope is permitted by the predicate;
  a separate positive witness carries the load-bearing non-empty
  scope case. This fixture itself is positive (the WF body holds)
  but is classed as a boundary case because it does not exhibit the
  substantive Layer 1 reasoning.
\<close>

axiomatization
  R_es :: "(nat, nat) run"
where
      es_scope:         "scope_of R_es = {}"
  and es_chunks_set:    "chunks R_es = {}"
  and es_frontier:      "frontier_of R_es = c0"
  and es_src_history:   "src_history_of R_es = []"
  and es_cdc_events:    "cdc_events_of R_es = []"
  and es_resp_all:      "responsible_chunk R_es k = None"

text \<open>
  @{const clean_prefix_of} is a run-derived @{command definition}
  (@{thm clean_prefix_of_def}); it is not axiomatized on the run but
  derived from the run's pinned accessors. @{text R_es} has no chunks
  and no observed CDC events, so the canonical construction yields the
  empty list.
\<close>

lemma es_chunks_list: "chunks_list R_es = []"
  using chunks_list_set[of R_es] es_chunks_set by simp

lemma es_clean_prefix: "clean_prefix_of R_es = []"
  unfolding clean_prefix_of_def canonical_clean_prefix_def cdc_event_replays_def
  using es_chunks_list es_cdc_events es_scope es_frontier
  by (simp add: List.map_filter_simps)

definition b0_es :: "nat \<rightharpoonup> nat" where
  "b0_es = (\<lambda>k. None)"

definition H_es :: "(nat, nat) src_history" where
  "H_es = []"

lemma wf_h_es: "wellformed_src_history H_es"
  unfolding wellformed_src_history_def by (simp add: H_es_def)

lemma es_canonical_partition:
  "canonical_chunk_ownership_domain R_es = {}"
  unfolding canonical_chunk_ownership_domain_def
  using es_chunks_set by simp

theorem boundary_empty_scope:
  "wellformed_dblog_run b0_es R_es H_es"
  unfolding wellformed_dblog_run_def
proof (intro conjI)
  \<comment> \<open>All clauses are vacuous on empty scope + empty src history
      + empty cdc_events. The WF2 order-preserving sublist clause
      requires an explicit witness for the strict_mono ι (the
      identity function suffices since the in-scope cdc_in_slice
      filter on the empty cdc_events_of produces an empty list,
      making the universal quantifier vacuously true).
      WF0 is split by `intro conjI` into source-history-binding +
      wellformed_src_history.\<close>
  show "src_history_of R_es = H_es"
    using es_src_history H_es_def by simp
next
  show "wellformed_src_history H_es" by (rule wf_h_es)
next
  show "\<forall>k\<in>scope_of R_es. \<exists>!ch. ch \<in> chunks R_es \<and> owns R_es ch k"
    using es_scope by simp
next
  show "\<forall>ch1\<in>chunks R_es. \<forall>ch2\<in>chunks R_es.
          ch1 \<noteq> ch2 \<longrightarrow> chunk_domain R_es ch1 \<inter> chunk_domain R_es ch2 = {}"
    using es_chunks_set by simp
next
  show "canonical_chunk_ownership_domain R_es = scope_of R_es"
    using es_canonical_partition es_scope by simp
next
  show "\<forall>k\<in>scope_of R_es. \<forall>ch.
          responsible_chunk R_es k = Some ch
            \<longleftrightarrow> ch \<in> chunks R_es \<and> owns R_es ch k"
    using es_scope by simp
next
  show "\<forall>k. k \<notin> scope_of R_es \<longrightarrow> responsible_chunk R_es k = None"
    using es_resp_all by simp
next
  show "finite (scope_of R_es)" using es_scope by simp
next
  show "\<forall>ch\<in>chunks R_es. finite (chunk_domain R_es ch)"
    using es_chunks_set by simp
next
  \<comment> \<open>WF1 (g): no dead chunks --- vacuous, R_es has no chunks.\<close>
  show "\<forall>ch\<in>chunks R_es. chunk_domain R_es ch \<noteq> {}"
    using es_chunks_set by simp
next
  show "\<forall>k\<in>scope_of R_es. covers_ordinary_cdc R_es k (frontier_of R_es)"
    using es_scope by simp
next
  \<comment> \<open>WF2 faithfulness: vacuous on empty cdc_events.\<close>
  show "\<forall>p\<in>set (cdc_events_of R_es).
          key_of (hist_event p) \<in> scope_of R_es
          \<and> src_le (hist_coord p) (frontier_of R_es)
          \<longrightarrow> p \<in> set (src_history_of R_es)"
    using es_cdc_events by simp
next
  \<comment> \<open>WF2 order-preserving sublist: cdc_events_of R_es = [], so
      cdc_in_slice is empty and the strict_mono ι obligation is
      discharged with the identity function (and the vacuous
      universal quantifier).\<close>
  show "\<exists>\<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
          \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of R_es
                                   \<and> src_le (hist_coord p) (frontier_of R_es));
                 cdc_in_slice  = filter in_slice (cdc_events_of R_es);
                 hist_in_slice = filter in_slice (src_history_of R_es)
             in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                    \<iota> i < length hist_in_slice
                  \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
  proof (intro exI[where x="\<lambda>n :: nat. n"] conjI)
    show "strict_mono (\<lambda>n :: nat. n)" by (simp add: strict_mono_def)
  next
    show "let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of R_es
                                \<and> src_le (hist_coord p) (frontier_of R_es));
              cdc_in_slice  = filter in_slice (cdc_events_of R_es);
              hist_in_slice = filter in_slice (src_history_of R_es)
          in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                 (\<lambda>n :: nat. n) i < length hist_in_slice
               \<and> cdc_in_slice ! i = hist_in_slice ! (\<lambda>n :: nat. n) i"
      using es_cdc_events by (simp add: Let_def)
  qed
next
  \<comment> \<open>WF2 post-read same-key/same-coordinate multiplicity: the
      empty-scope boundary witness has empty source history and
      empty observed CDC list, so every filtered slice is empty on
      both sides.\<close>
  show "\<forall>k\<in>scope_of R_es. \<forall>ch c.
          responsible_chunk R_es k = Some ch
          \<and> src_lt (chunk_read_coordinate R_es ch) c
          \<and> src_le c (frontier_of R_es)
          \<longrightarrow>
            mset (source_key_coord_slice k c (cdc_events_of R_es))
            = mset (source_key_coord_slice k c (src_history_of R_es))"
    using es_cdc_events es_src_history
    by (simp add: source_key_coord_slice_def)
next
  show "\<forall>ch\<in>chunks R_es.
          src_le (chunk_lower_watermark R_es ch) (chunk_read_coordinate R_es ch)
        \<and> src_le (chunk_read_coordinate R_es ch) (chunk_upper_watermark R_es ch)
        \<and> (\<forall>k\<in>chunk_domain R_es ch. \<exists>m. chunk_read_result R_es ch k = Some m)
        \<and> (\<forall>k\<in>chunk_domain R_es ch. \<forall>m.
             chunk_read_result R_es ch k = Some m
               \<longleftrightarrow> Refresh k m (chunk_read_coordinate R_es ch)
                    \<in> set (clean_prefix_of R_es))"
    using es_chunks_set by simp
next
  show "\<forall>ch\<in>chunks R_es.
          src_le (chunk_read_coordinate R_es ch) (frontier_of R_es)"
    using es_chunks_set by simp
next
  show "\<forall>ch\<in>chunks R_es. \<forall>k\<in>chunk_domain R_es ch. \<forall>m.
          chunk_read_result R_es ch k = Some m
            \<longrightarrow> m = Src b0_es H_es (chunk_read_coordinate R_es ch) k"
    using es_chunks_set by simp
next
  show "\<forall>ch\<in>chunks R_es. \<forall>k\<in>chunk_domain R_es ch.
          chunk_read_result R_es ch k = Some None
            \<longrightarrow> row_absence_meaningful b0_es H_es R_es ch k"
    using es_chunks_set by simp
next
  show "\<forall>p\<in>set (cdc_events_of R_es).
          key_of (hist_event p) \<in> scope_of R_es
          \<and> src_le (hist_coord p) (frontier_of R_es)
          \<longrightarrow> Cdc (hist_coord p) (hist_event p) \<in> set (clean_prefix_of R_es)"
    using es_cdc_events by simp
next
  show "\<forall>e c. Cdc c e \<in> set (clean_prefix_of R_es)
                \<and> key_of e \<in> scope_of R_es
                \<and> src_le c (frontier_of R_es)
                \<longrightarrow> (c, e) \<in> set (cdc_events_of R_es)"
    using es_clean_prefix by simp
qed


section \<open>Layer 1 negative fixture: responsible-chunk vs chunk_domain mismatch (WF1 (d))\<close>

text \<open>
  With @{const owns} an @{command abbreviation} over
  @{const chunk_domain}, a literal
  @{text "owns ch k \<noteq> (k \<in> chunk_domain ch)"} disagreement is
  structurally impossible at the Isabelle level (the two sides are
  definitionally equal). The load-bearing role for
  @{text responsible_chunk}/@{const chunk_domain} coherence is
  therefore carried by WF1 (d)'s iff between @{text responsible_chunk}
  and chunk-domain membership, which this fixture targets.

  Fixture: @{text "scope_of R_rd = {1}"}, a single chunk
  @{text rd_ch} with @{text "chunk_domain R_rd rd_ch = {1}"}, but
  @{text "responsible_chunk R_rd 1 = None"}. WF1 (d) requires
  @{text "responsible_chunk R k = Some ch \<longleftrightarrow>
  ch \<in> chunks R \<and> owns R ch k"} for every in-scope @{text k}.
  Instantiating @{text "k = 1"} and @{text "ch = rd_ch"}: the LHS
  is @{text "(None = Some rd_ch) = False"}; the RHS is
  @{text "(rd_ch \<in> chunks R_rd \<and> 1 \<in> chunk_domain R_rd rd_ch)
  = True"}. The iff fails.

  Why WF1 (d) is load-bearing. Without the iff, the
  @{text responsible_chunk} function and the per-chunk ownership
  predicate could disagree on which chunk is responsible for an
  in-scope key. Downstream WF2 coverage (which indexes through
  @{text responsible_chunk}) and Lemma 1.1's chunk-keyed reasoning
  would lose determinacy. This fixture exhibits the rejection.
\<close>

axiomatization
  R_rd  :: "(nat, nat) run" and
  rd_ch :: "(nat, nat) chunk"
where
      rd_chunks_set:    "chunks R_rd = {rd_ch}"
  and rd_dom:           "chunk_domain R_rd rd_ch = {1}"
  and rd_scope:         "scope_of R_rd = {1}"
  and rd_resp_none:     "responsible_chunk R_rd 1 = None"

definition b0_rd :: "nat \<rightharpoonup> nat" where
  "b0_rd = (\<lambda>k. None)"

definition H_rd :: "(nat, nat) src_history" where
  "H_rd = []"

theorem fix_resp_dom_rejected:
  "\<not> wellformed_dblog_run b0_rd R_rd H_rd"
proof
  assume H: "wellformed_dblog_run b0_rd R_rd H_rd"
  hence wf1d:
    "\<forall>k \<in> scope_of R_rd. \<forall>ch.
        responsible_chunk R_rd k = Some ch
          \<longleftrightarrow> ch \<in> chunks R_rd \<and> owns R_rd ch k"
    unfolding wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have inScope: "(1::nat) \<in> scope_of R_rd" using rd_scope by simp
  with wf1d
  have iff_for_rd_ch:
    "responsible_chunk R_rd 1 = Some rd_ch
       \<longleftrightarrow> rd_ch \<in> chunks R_rd \<and> owns R_rd rd_ch 1" by blast
  have rhs_holds: "rd_ch \<in> chunks R_rd \<and> owns R_rd rd_ch 1"
    using rd_chunks_set rd_dom by simp
  with iff_for_rd_ch have "responsible_chunk R_rd 1 = Some rd_ch" by simp
  with rd_resp_none show False by simp
qed


section \<open>Layer 1 negative fixture: row-absence meaningfulness violated (WF6 row-absence)\<close>

text \<open>
  Fixture: an absence-Refresh appears in the clean prefix at the
  chunk-read coordinate for an in-domain key, but the source state
  at that coordinate is NOT @{const None} for that key.

  Construction: @{text "chunks R_ra = {ra_ch}"},
  @{text "chunk_domain R_ra ra_ch = {1}"},
  @{text "chunk_read_coordinate R_ra ra_ch = c0"},
  @{text "chunk_read_result R_ra ra_ch 1 = Some None"} (absence
  observed), @{text "clean_prefix_of R_ra = [Refresh 1 None c0]"}
  (the absence-Refresh in the prefix), but
  @{text "b0_ra 1 = Some 99"} and @{text "H_ra = []"} so
  @{text "Src b0_ra H_ra c0 1 = Some 99 \<noteq> None"}. WF6 row-
  absence rejects: the implication
  @{text "row_absence_meaningful b0 H R ra_ch 1"} unfolds to a
  satisfied antecedent (1 in chunk_domain @{text ra_ch};
  @{text "Refresh 1 None c0"} in @{text "clean_prefix_of R_ra"})
  and a violated consequent (@{text "Src \<noteq> None"}).

  Why WF6 row-absence is load-bearing. Without the conjunct, an
  absence-Refresh could appear in @{const clean_prefix_of} for a
  key whose source state is not actually empty at the chunk-read
  coordinate -- the operational claim ``the chunk read observed
  no row for this key'' would be unsupported by the source side.
  Under WF4 + WF6 main the implication is auto-satisfied (WF4
  forces the absence-Refresh into scope when
  @{text "chunk_read_result = Some None"}; WF6 main forces
  @{text "Src(\<dots>)(k) = None"}). The conjunct brings the formal WF
  body into alignment with the paper's WF6 row-absence content;
  without WF4 + WF6 main (e.g., in a relaxed predicate), this
  clause would catch the constructed counterexample directly.

  This fixture targets the WF6 row-absence conjunct specifically.
  WF6 main is also violated on the same data (the same construction
  has @{text "Some None \<noteq> Src(b0_ra, H_ra, c0, 1) = Some 99"}, so
  WF6 main rejects too); on this constructed instance both conjuncts
  reject. The proof extracts the WF6 row-absence conjunct to show
  that it rejects this shape --- not that it is the only conjunct
  that does. Under WF4 + WF6 main the row-absence implication is
  redundant (see the paragraph above); it would be the sole
  catching conjunct only in a relaxed predicate lacking WF4 + WF6
  main.
\<close>

axiomatization
  R_ra  :: "(nat, nat) run" and
  ra_ch :: "(nat, nat) chunk"
where
      ra_chunks_set:    "chunks R_ra = {ra_ch}"
  and ra_dom:           "chunk_domain R_ra ra_ch = {1}"
  and ra_read_coord:    "chunk_read_coordinate R_ra ra_ch = c0"
  and ra_chunk_read_result:
        "chunk_read_result R_ra ra_ch 1 = Some None"
  and ra_cdc_events:    "cdc_events_of R_ra = []"

text \<open>
  @{const clean_prefix_of} is a run-derived @{command definition}
  (@{thm clean_prefix_of_def}); for @{text R_ra} it is derived from the
  pinned accessors above rather than axiomatized on the run. The
  @{text ra_cdc_events} axiom (no observed CDC events) is the input the
  earlier @{term "clean_prefix_of R_ra"} axiom left implicit; pinning
  it makes the derived clean prefix determinate.
\<close>

lemma ra_chunks_list: "chunks_list R_ra = [ra_ch]"
proof -
  have s: "set (chunks_list R_ra) = {ra_ch}"
    using chunks_list_set[of R_ra] ra_chunks_set by simp
  have "length (chunks_list R_ra) = 1"
    using distinct_card[OF chunks_list_distinct[of R_ra]] s by simp
  with s show ?thesis
    by (cases "chunks_list R_ra") auto
qed

lemma ra_clean_prefix:
  "clean_prefix_of R_ra = [Refresh (1::nat) (None::nat option) c0]"
proof -
  have d1: "sorted_list_of_set {Suc 0} = [Suc 0]" by eval
  show ?thesis
    unfolding clean_prefix_of_def canonical_clean_prefix_def
              cdc_event_replays_def chunk_read_refreshes_def
    by (simp add: ra_chunks_list ra_dom ra_read_coord
                  ra_chunk_read_result[unfolded One_nat_def]
                  ra_cdc_events d1 One_nat_def
                  List.map_filter_simps sort_key_def)
qed

definition b0_ra :: "nat \<rightharpoonup> nat" where
  "b0_ra = (\<lambda>k. if k = 1 then Some 99 else None)"

definition H_ra :: "(nat, nat) src_history" where
  "H_ra = []"

lemma latest_src_event_H_ra_c0_1:
  "latest_src_event H_ra c0 (1::nat) = None"
  unfolding latest_src_event_def by (simp add: H_ra_def)

lemma Src_b0_ra_H_ra_c0_1: "Src b0_ra H_ra c0 (1::nat) = Some 99"
  unfolding Src_def using latest_src_event_H_ra_c0_1
  by (simp add: b0_ra_def)

lemma refresh_in_ra_prefix:
  "Refresh (1::nat) (None::nat option) c0 \<in> set (clean_prefix_of R_ra)"
  using ra_clean_prefix by simp

theorem fix_row_abs_rejected:
  "\<not> wellformed_dblog_run b0_ra R_ra H_ra"
proof
  assume H: "wellformed_dblog_run b0_ra R_ra H_ra"
  hence wf6_ra:
    "\<forall>ch \<in> chunks R_ra. \<forall>k \<in> chunk_domain R_ra ch.
        chunk_read_result R_ra ch k = Some None
          \<longrightarrow> row_absence_meaningful b0_ra H_ra R_ra ch k"
    unfolding wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have inCh: "ra_ch \<in> chunks R_ra" using ra_chunks_set by simp
  have inK: "(1::nat) \<in> chunk_domain R_ra ra_ch" using ra_dom by simp
  from wf6_ra inCh inK ra_chunk_read_result
  have ram: "row_absence_meaningful b0_ra H_ra R_ra ra_ch 1" by blast
  hence implication:
    "(1 \<in> chunk_domain R_ra ra_ch
      \<and> Refresh 1 None (chunk_read_coordinate R_ra ra_ch)
            \<in> set (clean_prefix_of R_ra))
       \<longrightarrow> Src b0_ra H_ra (chunk_read_coordinate R_ra ra_ch) 1 = None"
    unfolding row_absence_meaningful_def by simp
  have antecedent:
    "1 \<in> chunk_domain R_ra ra_ch
     \<and> Refresh 1 None (chunk_read_coordinate R_ra ra_ch)
         \<in> set (clean_prefix_of R_ra)"
    using ra_dom ra_read_coord refresh_in_ra_prefix by simp
  from implication antecedent
  have "Src b0_ra H_ra (chunk_read_coordinate R_ra ra_ch) 1 = None" by blast
  with ra_read_coord Src_b0_ra_H_ra_c0_1 have "(Some (99::nat)) = None" by simp
  thus False by simp
qed


section \<open>WF7 clean-prefix CDC coherence holds for every run\<close>

text \<open>
  WF7 -- the clean-prefix CDC-coherence clause of
  @{const wellformed_dblog_run}, forward and reverse -- holds for
  \<^emph>\<open>every\<close> run, with no wellformedness premise. The theorems
  below establish this.

  There is therefore no WF7 negative fixture in run form. A negative
  fixture would have to pin @{term "clean_prefix_of R"} on a run
  whose other accessors are fixed, to a value that violates WF7. But
  @{const clean_prefix_of} is run-derived: it is a real
  @{command definition} (@{thm clean_prefix_of_def}), not an opaque
  accessor, so pinning it to a WF7-violating value contradicts the
  definition. A run that violates WF7 is unconstructible.

  The theorems below prove this. @{const clean_prefix_of} is
  @{const canonical_clean_prefix} applied to a run's chunk reads,
  observed CDC events, scope, and frontier. Its @{const Cdc} events
  are exactly the @{const cdc_event_replays} of the in-scope,
  at-or-before-frontier observed CDC events; the
  @{const chunk_read_refreshes} branch emits only @{const Refresh}
  events. Forward coherence (@{text wf7_forward_holds_for_all_runs})
  and reverse coherence (@{text wf7_reverse_holds_for_all_runs}) then
  follow directly, and @{text wf7_clean_prefix_cdc_coherence_redundant}
  states the exact WF7 conjunct of @{const wellformed_dblog_run} and
  proves it for an arbitrary run. WF7 is therefore a logically
  redundant conjunct of the predicate; it is kept in the body for
  documentation and audit continuity but constrains no run.

  The WF7-violating building-block shapes -- a
  misordered clean prefix, an extra refresh, a stray future
  @{const Cdc} -- are exercised directly against
  @{const canonical_clean_prefix} with hand-built inputs in theory
  @{text Layer2_Fixtures}, so the unconstructibility of WF7-violating
  runs leaves no structural coverage gap.
\<close>

lemma in_set_cdc_event_replaysI:
  fixes es :: "(src_coord \<times> ('k, 'v) source_event) list"
  assumes "(c, e) \<in> set es"
      and "key_of e \<in> scope"
      and "c \<le> frontier"
  shows "Cdc c e \<in> set (cdc_event_replays scope frontier es)"
  using assms(1)
proof (induction es)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "p = (c, e)")
    case True
    then show ?thesis
      using assms(2,3) by (simp add: cdc_event_replays_def)
  next
    case False
    with Cons.prems have "(c, e) \<in> set ps" by simp
    then have "Cdc c e \<in> set (cdc_event_replays scope frontier ps)"
      by (rule Cons.IH)
    then show ?thesis
      by (simp add: cdc_event_replays_def split: option.split)
  qed
qed

lemma wf7_forward_holds_for_all_runs:
  fixes R :: "('k :: linorder, 'v) run"
    and c :: src_coord
    and e :: "('k, 'v) source_event"
  assumes cdc_in:   "(c, e) \<in> set (cdc_events_of R)"
      and in_scope: "key_of e \<in> scope_of R"
      and le_front: "src_le c (frontier_of R)"
  shows "Cdc c e \<in> set (clean_prefix_of R)"
proof -
  have c_le: "c \<le> frontier_of R"
    using le_front by (simp add: less_eq_src_coord_def)
  have "Cdc c e \<in> set (cdc_event_replays (scope_of R) (frontier_of R)
                                          (cdc_events_of R))"
    using cdc_in in_scope c_le by (rule in_set_cdc_event_replaysI)
  thus ?thesis
    by (auto simp: clean_prefix_of_def canonical_clean_prefix_def)
qed

lemma wf7_reverse_holds_for_all_runs:
  fixes R :: "('k :: linorder, 'v) run"
    and c :: src_coord
    and e :: "('k, 'v) source_event"
  assumes e_in: "Cdc c e \<in> set (clean_prefix_of R)"
  shows "(c, e) \<in> set (cdc_events_of R)
       \<and> key_of e \<in> scope_of R
       \<and> src_le c (frontier_of R)"
proof -
  let ?mkRec = "\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                       crr_read_coord  = chunk_read_coordinate R ch,
                       crr_observation = chunk_read_result R ch \<rparr>"
  \<comment> \<open>Cdc events cannot come from the chunk_read_refreshes branch,
      which emits only Refresh events.\<close>
  have not_refresh_branch:
    "\<forall> ch. Cdc c e \<notin> set (chunk_read_refreshes (?mkRec ch))"
    unfolding chunk_read_refreshes_def List.map_filter_def
    by (auto split: option.splits)
  have split:
    "Cdc c e \<in> set (cdc_event_replays (scope_of R)
                                       (frontier_of R)
                                       (cdc_events_of R))
   \<or> (\<exists> ch \<in> set (chunks_list R).
        Cdc c e \<in> set (chunk_read_refreshes (?mkRec ch)))"
    using e_in
    by (auto simp: clean_prefix_of_def canonical_clean_prefix_def)
  from split not_refresh_branch have in_cdc_replays:
    "Cdc c e \<in> set (cdc_event_replays (scope_of R)
                                       (frontier_of R)
                                       (cdc_events_of R))"
    by blast
  from in_cdc_replays show ?thesis
    unfolding cdc_event_replays_def List.map_filter_def
    by (auto split: if_splits simp: less_eq_src_coord_def)
qed

theorem wf7_clean_prefix_cdc_coherence_redundant:
  fixes R :: "('k :: linorder, 'v) run"
  shows "(\<forall> p \<in> set (cdc_events_of R).
            key_of (hist_event p) \<in> scope_of R
            \<and> src_le (hist_coord p) (frontier_of R)
            \<longrightarrow> Cdc (hist_coord p) (hist_event p)
                  \<in> set (clean_prefix_of R))
       \<and> (\<forall> e c. Cdc c e \<in> set (clean_prefix_of R)
            \<and> key_of e \<in> scope_of R
            \<and> src_le c (frontier_of R)
            \<longrightarrow> (c, e) \<in> set (cdc_events_of R))"
proof
  show "\<forall> p \<in> set (cdc_events_of R).
          key_of (hist_event p) \<in> scope_of R
          \<and> src_le (hist_coord p) (frontier_of R)
          \<longrightarrow> Cdc (hist_coord p) (hist_event p)
                \<in> set (clean_prefix_of R)"
  proof (intro ballI impI)
    fix p
    assume p_in: "p \<in> set (cdc_events_of R)"
       and hyp: "key_of (hist_event p) \<in> scope_of R
                  \<and> src_le (hist_coord p) (frontier_of R)"
    have "(fst p, snd p) \<in> set (cdc_events_of R)" using p_in by simp
    moreover have "key_of (snd p) \<in> scope_of R" using hyp by simp
    moreover have "src_le (fst p) (frontier_of R)" using hyp by simp
    ultimately have "Cdc (fst p) (snd p) \<in> set (clean_prefix_of R)"
      by (rule wf7_forward_holds_for_all_runs)
    thus "Cdc (hist_coord p) (hist_event p) \<in> set (clean_prefix_of R)"
      by simp
  qed
next
  show "\<forall> e c. Cdc c e \<in> set (clean_prefix_of R)
                 \<and> key_of e \<in> scope_of R
                 \<and> src_le c (frontier_of R)
                 \<longrightarrow> (c, e) \<in> set (cdc_events_of R)"
  proof (intro allI impI)
    fix e c
    assume "Cdc c e \<in> set (clean_prefix_of R)
             \<and> key_of e \<in> scope_of R
             \<and> src_le c (frontier_of R)"
    from wf7_reverse_holds_for_all_runs[OF conjunct1[OF this]]
    show "(c, e) \<in> set (cdc_events_of R)" by simp
  qed
qed


section \<open>Existential bundles\<close>

text \<open>
  Three existence theorems re-state representative negative fixtures
  in reader-friendly @{text \<exists>} form. Each states ``there exists an
  instance the WF predicate rejects'', concluding with
  @{text "\<exists> ... \<not> wellformed_X ..."} and is discharged from one
  per-fixture theorem (Layer 0: @{text fix_h_c0_rejected}; Layer 1:
  @{text fix_overlap_rejected} and @{text fix_resp_dom_rejected}).
  They are existence witnesses, not an aggregate over the whole
  fixture set: the complete per-clause coverage is the individual
  @{text "fix_*_rejected"} theorems in the sections above.
\<close>

theorem layer0_negative_fixture_exists:
  "\<exists> (H :: (nat, nat) src_history). \<not> wellformed_src_history H"
proof (intro exI[where x = H_c0])
  show "\<not> wellformed_src_history H_c0" by (rule fix_h_c0_rejected)
qed

theorem layer1_negative_fixtures_exist:
  "(\<exists> (b0 :: nat \<rightharpoonup> nat) (R :: (nat, nat) run)
       (H :: (nat, nat) src_history).
        \<not> wellformed_dblog_run b0 R H)"
proof (intro exI[where x = b0_ov] exI[where x = R_ov] exI[where x = H_ov])
  show "\<not> wellformed_dblog_run b0_ov R_ov H_ov" by (rule fix_overlap_rejected)
qed

theorem boundary_empty_scope_exists:
  "\<exists> (b0 :: nat \<rightharpoonup> nat) (R :: (nat, nat) run)
      (H :: (nat, nat) src_history).
        wellformed_dblog_run b0 R H \<and> scope_of R = {}"
proof (intro exI[where x = b0_es] exI[where x = R_es] exI[where x = H_es]
             conjI)
  show "wellformed_dblog_run b0_es R_es H_es" by (rule boundary_empty_scope)
next
  show "scope_of R_es = {}" by (rule es_scope)
qed

theorem layer1_back_to_c_fixtures_exist:
  "(\<exists> (b0 :: nat \<rightharpoonup> nat) (R :: (nat, nat) run)
       (H :: (nat, nat) src_history).
        \<not> wellformed_dblog_run b0 R H)"
proof (intro exI[where x = b0_rd] exI[where x = R_rd] exI[where x = H_rd])
  show "\<not> wellformed_dblog_run b0_rd R_rd H_rd" by (rule fix_resp_dom_rejected)
qed

end
