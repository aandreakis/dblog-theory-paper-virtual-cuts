theory Layer01_Virtual_Cut_Example
  imports DBLog_Run
begin

text \<open>
  The paper's running example of a virtual cut, machine-checked.

  This theory is the checked counterpart of the paper's
  "Bootstrapping and Advancing a Virtual Cut: A Running Example" section. Where the
  minimum-viable witness theory exhibits a smallest non-vacuity
  witness for the wellformed-DBLog-run predicate, this theory
  exhibits a paper-quality concrete example: a realistic
  accounts-table backfill scenario carrying three in-scope keys,
  two chunks, four CDC events, two chunk reads at distinct
  source-log moments, and the full per-key replay-vs-source-state
  equality on the chosen frontier and scope (the conclusion of
  paper Lemma 1.1, @{text "wellformed_run_implies_virtual_cut"}, on
  the example instance).

  Construction approach. The Layer 1 run carrier
  @{typ "('k, 'v) run"} is a @{command typedecl} (no constructors),
  and the run accessors are @{command consts}. The example therefore
  uses an @{command axiomatization} block to introduce a single
  concrete run constant @{text ex_R} along with axiom equations
  fixing each accessor's value on @{text ex_R}, plus two concrete
  chunk constants @{text ex_ch_A} / @{text ex_ch_B} and four
  concrete source coordinates @{text "ec1, ec2, ec3, ec4"} above
  @{text c0}. The axioms are fixture axioms over fresh constants:
  they pin accessor values on these new constants only and assert no
  global property of the abstract Layer 1 vocabulary, which stays
  unconstrained on every other run / chunk / coordinate.

  The clean prefix is \<^emph>\<open>not\<close> axiomatized on the run.
  @{const clean_prefix_of} is a run-derived @{command definition}
  (@{thm clean_prefix_of_def}); for @{text ex_R} the lemma
  @{text ex_clean_prefix} below computes it, from the pinned
  accessors, to the concrete seven-event list the paper's running
  example walks through.

  Witness data summary (see the paper's running-example section for
  the full reader-facing narrative):

    \<^item> @{text b0_ex}:        key 100 \<mapsto> Some 5000 (Alice's $50.00),
                              key 200 \<mapsto> Some 10000 (Bob's $100.00),
                              all other keys \<mapsto> None
                              (Carol's account 300 has not yet
                              been opened);
    \<^item> @{text H_ex}:         four-event source history at
                              @{text "[ec1, ec2, ec3, ec4]"}
                              recording: c1 update Alice to $30;
                              c2 insert Carol at $25; c3 update
                              Bob to $120; c4 update Carol to $35;
    \<^item> @{term "scope_of ex_R"}:   @{text "{100, 200, 300}"};
    \<^item> @{term "frontier_of ex_R"}: @{text ec4} (after every event);
    \<^item> @{term "chunks ex_R"}:     @{text "{ex_ch_A, ex_ch_B}"};
    \<^item> @{term "chunk_domain ex_R ex_ch_A"}: @{text "{100, 200}"};
       @{term "chunk_domain ex_R ex_ch_B"}: @{text "{300}"};
    \<^item> chunk-read coordinates:  chunk A reads at @{text ec1};
                                  chunk B reads at @{text ec3};
    \<^item> @{term "cdc_events_of ex_R"}: equal to @{text H_ex}
                              (every CDC event observed);
    \<^item> @{term "clean_prefix_of ex_R"}: the seven-event list the
                              paper's running example walks through
                              (3 chunk-read refreshes plus 4 CDC
                              events, ordered by source coordinate;
                              chunk A's stale refresh of key 200 and
                              chunk B's stale refresh of key 300
                              both remain in the prefix in raw,
                              un-normalized @{const canonical_clean_prefix}
                              form, and are dominated at
                              @{const Apply} time by the c3 / c4 CDC
                              updates).

  Result: @{const Apply} on @{term "clean_prefix_of ex_R"}
  restricted to scope produces exactly @{text "(100 \<mapsto> 3000,
  200 \<mapsto> 12000, 300 \<mapsto> 3500)"}, which equals @{term "Src
  b0_ex H_ex ec4"} restricted to the same scope. The final theorem
  @{text ex_virtual_cut_holds} establishes the scope-restricted
  equality on the concrete instance, exhibiting the Layer 2
  source-side soundness conclusion (paper Lemma 1.1) on a
  non-trivial example. The example is also wellformed: @{text
  ex_wellformed_dblog_run} discharges
  @{const wellformed_dblog_run} on the
  @{text "(b0_ex, ex_R, H_ex)"} instance.
\<close>

subsection \<open>Witness source coordinates\<close>

text \<open>
  Four source coordinates above @{text c0}, with a strict @{text src_lt}
  chain @{text "c0 < ec1 < ec2 < ec3 < ec4"}. The chain ensures the
  example's source history events at @{text "ec1, ec2, ec3, ec4"}
  respect WF-H1 (non-decreasing source coordinates) and WF-H2 (no
  event at @{text c0}).
\<close>

axiomatization ec1 ec2 ec3 ec4 :: src_coord
where
  c0_lt_ec1:  "src_lt c0 ec1"
  and ec1_lt_ec2: "src_lt ec1 ec2"
  and ec2_lt_ec3: "src_lt ec2 ec3"
  and ec3_lt_ec4: "src_lt ec3 ec4"

lemma c0_le_ec1: "src_le c0 ec1"
  using c0_lt_ec1 by (simp add: src_lt_def)

lemma ec1_le_ec2: "src_le ec1 ec2"
  using ec1_lt_ec2 by (simp add: src_lt_def)

lemma ec2_le_ec3: "src_le ec2 ec3"
  using ec2_lt_ec3 by (simp add: src_lt_def)

lemma ec3_le_ec4: "src_le ec3 ec4"
  using ec3_lt_ec4 by (simp add: src_lt_def)

lemma c0_le_ec2: "src_le c0 ec2"
  using c0_le_ec1 ec1_le_ec2 src_le_trans by blast

lemma c0_le_ec3: "src_le c0 ec3"
  using c0_le_ec2 ec2_le_ec3 src_le_trans by blast

lemma c0_le_ec4: "src_le c0 ec4"
  using c0_le_ec3 ec3_le_ec4 src_le_trans by blast

lemma ec1_le_ec3: "src_le ec1 ec3"
  using ec1_le_ec2 ec2_le_ec3 src_le_trans by blast

lemma ec1_le_ec4: "src_le ec1 ec4"
  using ec1_le_ec3 ec3_le_ec4 src_le_trans by blast

lemma ec2_le_ec4: "src_le ec2 ec4"
  using ec2_le_ec3 ec3_le_ec4 src_le_trans by blast

lemma ec1_neq_ec2: "ec1 \<noteq> ec2"
  using ec1_lt_ec2 by (simp add: src_lt_def)

lemma ec2_neq_ec3: "ec2 \<noteq> ec3"
  using ec2_lt_ec3 by (simp add: src_lt_def)

lemma ec3_neq_ec4: "ec3 \<noteq> ec4"
  using ec3_lt_ec4 by (simp add: src_lt_def)

lemma c0_neq_ec1: "c0 \<noteq> ec1"
  using c0_lt_ec1 by (simp add: src_lt_def)

lemma c0_neq_ec2: "c0 \<noteq> ec2"
proof -
  have "src_le ec1 ec2" by (rule ec1_le_ec2)
  show ?thesis using c0_lt_ec1 \<open>src_le ec1 ec2\<close>
    by (metis src_lt_def src_le_antisym src_le_trans c0_le_ec1)
qed

lemma c0_neq_ec3: "c0 \<noteq> ec3"
proof -
  have "src_le c0 ec3" by (rule c0_le_ec3)
  have "src_lt c0 ec3" using c0_lt_ec1 ec1_le_ec3
    by (metis src_lt_def src_le_antisym src_le_trans \<open>src_le c0 ec3\<close>)
  thus ?thesis by (simp add: src_lt_def)
qed

lemma c0_neq_ec4: "c0 \<noteq> ec4"
proof -
  have "src_le c0 ec4" by (rule c0_le_ec4)
  have "src_lt c0 ec4" using c0_lt_ec1 ec1_le_ec4
    by (metis src_lt_def src_le_antisym src_le_trans \<open>src_le c0 ec4\<close>)
  thus ?thesis by (simp add: src_lt_def)
qed

lemma ec1_neq_ec3: "ec1 \<noteq> ec3"
proof -
  have "src_lt ec1 ec3" using ec1_lt_ec2 ec2_le_ec3
    by (metis src_lt_def src_le_antisym src_le_trans ec1_le_ec3)
  thus ?thesis by (simp add: src_lt_def)
qed

lemma ec1_neq_ec4: "ec1 \<noteq> ec4"
proof -
  have "src_lt ec1 ec4" using ec1_lt_ec2 ec2_le_ec4
    by (metis src_lt_def src_le_antisym src_le_trans ec1_le_ec4)
  thus ?thesis by (simp add: src_lt_def)
qed

lemma ec2_neq_ec4: "ec2 \<noteq> ec4"
proof -
  have "src_lt ec2 ec4" using ec2_lt_ec3 ec3_le_ec4
    by (metis src_lt_def src_le_antisym src_le_trans ec2_le_ec4)
  thus ?thesis by (simp add: src_lt_def)
qed

text \<open>
  Negative orderings used by the WF discharge and by Src
  computations below: @{text "ec_i"} is NOT @{text "src_le"} below
  @{text c0}, and the @{text src_lt} chain rules out backwards
  comparisons.
\<close>

lemma not_src_le_ec1_c0: "\<not> src_le ec1 c0"
  using c0_le_ec1 c0_neq_ec1 src_le_antisym by blast

lemma not_src_le_ec2_c0: "\<not> src_le ec2 c0"
  using c0_le_ec2 c0_neq_ec2 src_le_antisym by blast

lemma not_src_le_ec3_c0: "\<not> src_le ec3 c0"
  using c0_le_ec3 c0_neq_ec3 src_le_antisym by blast

lemma not_src_le_ec4_c0: "\<not> src_le ec4 c0"
  using c0_le_ec4 c0_neq_ec4 src_le_antisym by blast

lemma not_src_le_ec2_ec1: "\<not> src_le ec2 ec1"
  using ec1_le_ec2 ec1_neq_ec2 src_le_antisym by blast

lemma not_src_le_ec3_ec1: "\<not> src_le ec3 ec1"
  using ec1_le_ec3 ec1_neq_ec3 src_le_antisym by blast

lemma not_src_le_ec4_ec1: "\<not> src_le ec4 ec1"
  using ec1_le_ec4 ec1_neq_ec4 src_le_antisym by blast

lemma not_src_le_ec3_ec2: "\<not> src_le ec3 ec2"
  using ec2_le_ec3 ec2_neq_ec3 src_le_antisym by blast

lemma not_src_le_ec4_ec2: "\<not> src_le ec4 ec2"
  using ec2_le_ec4 ec2_neq_ec4 src_le_antisym by blast

lemma not_src_le_ec4_ec3: "\<not> src_le ec4 ec3"
  using ec3_le_ec4 ec3_neq_ec4 src_le_antisym by blast

lemma not_src_lt_ec1_ec1: "\<not> src_lt ec1 ec1" by (simp add: src_lt_def)
lemma not_src_lt_ec3_ec1: "\<not> src_lt ec3 ec1"
  using not_src_le_ec3_ec1 by (simp add: src_lt_def)
lemma not_src_lt_ec3_ec2: "\<not> src_lt ec3 ec2"
  using not_src_le_ec3_ec2 by (simp add: src_lt_def)
lemma not_src_lt_ec3_ec3: "\<not> src_lt ec3 ec3" by (simp add: src_lt_def)

subsection \<open>Witness base state and source history\<close>

definition b0_ex :: "nat \<rightharpoonup> nat" where
  "b0_ex = (\<lambda>k. if k = 100 then Some 5000
               else if k = 200 then Some 10000
               else None)"

definition H_ex :: "(nat, nat) src_history" where
  "H_ex = [ (ec1, Update 100 3000),
            (ec2, Insert 300 2500),
            (ec3, Update 200 12000),
            (ec4, Update 300 3500) ]"

lemma length_H_ex: "length H_ex = 4"
  by (simp add: H_ex_def)

lemma H_ex_nth_0: "H_ex ! 0 = (ec1, Update 100 3000)"
  by (simp add: H_ex_def)

lemma H_ex_nth_1: "H_ex ! 1 = (ec2, Insert 300 2500)"
  by (simp add: H_ex_def)

lemma H_ex_nth_2: "H_ex ! 2 = (ec3, Update 200 12000)"
  by (simp add: H_ex_def)

lemma H_ex_nth_3: "H_ex ! 3 = (ec4, Update 300 3500)"
  by (simp add: H_ex_def)

lemma set_H_ex:
  "set H_ex = { (ec1, Update 100 3000),
                (ec2, Insert 300 2500),
                (ec3, Update 200 12000),
                (ec4, Update 300 3500) }"
  by (simp add: H_ex_def)

subsection \<open>Witness run, chunks, and accessor values\<close>

text \<open>
  Single concrete run constant @{text ex_R} together with two
  concrete chunk constants @{text ex_ch_A} / @{text ex_ch_B}; all
  Layer 1 accessor values on these constants are fixed by axiom
  equations. WF1 sub-clause (e) per paper "The wellformed-DBLog-
  run predicate" -- @{text "\<forall>k. k \<notin> scope_of(R) \<longrightarrow>
  responsible_chunk(R, k) = None"} -- is captured here via
  @{text ex_resp_else}.
\<close>

axiomatization
  ex_R     :: "(nat, nat) run" and
  ex_ch_A  :: "(nat, nat) chunk" and
  ex_ch_B  :: "(nat, nat) chunk"
where
  ex_chunks_distinct:  "ex_ch_A \<noteq> ex_ch_B"
  and ex_scope:        "scope_of ex_R = {100, 200, 300}"
  and ex_frontier:     "frontier_of ex_R = ec4"
  and ex_chunks_set:   "chunks ex_R = {ex_ch_A, ex_ch_B}"
  and ex_dom_A:        "chunk_domain ex_R ex_ch_A = {100, 200}"
  and ex_dom_B:        "chunk_domain ex_R ex_ch_B = {300}"
  \<comment> \<open>No explicit @{text "ex_owns_*"} axioms are needed: with
       @{const owns} an @{command abbreviation} over
       @{text chunk_domain}, each ownership statement expands to a
       set-membership fact already implied by @{text ex_dom_A} or
       @{text ex_dom_B}, and the WF1 (a) + (d) discharge proofs cite
       the @{text "ex_dom_*"} axioms directly.\<close>
  and ex_resp_100:     "responsible_chunk ex_R 100 = Some ex_ch_A"
  and ex_resp_200:     "responsible_chunk ex_R 200 = Some ex_ch_A"
  and ex_resp_300:     "responsible_chunk ex_R 300 = Some ex_ch_B"
  and ex_resp_else:    "k \<noteq> 100 \<Longrightarrow> k \<noteq> 200 \<Longrightarrow> k \<noteq> 300
                          \<Longrightarrow> responsible_chunk ex_R k = None"
  and ex_read_coord_A: "chunk_read_coordinate ex_R ex_ch_A = ec1"
  and ex_read_coord_B: "chunk_read_coordinate ex_R ex_ch_B = ec3"
  and ex_lwm_A:        "chunk_lower_watermark ex_R ex_ch_A = ec1"
  and ex_uwm_A:        "chunk_upper_watermark ex_R ex_ch_A = ec1"
  and ex_lwm_B:        "chunk_lower_watermark ex_R ex_ch_B = ec3"
  and ex_uwm_B:        "chunk_upper_watermark ex_R ex_ch_B = ec3"
  and ex_src_history:  "src_history_of ex_R = H_ex"
  and ex_chunk_read_result_A_100:
    "chunk_read_result ex_R ex_ch_A 100 = Some (Some 3000)"
  and ex_chunk_read_result_A_200:
    "chunk_read_result ex_R ex_ch_A 200 = Some (Some 10000)"
  and ex_chunk_read_result_B_300:
    "chunk_read_result ex_R ex_ch_B 300 = Some (Some 2500)"
  and ex_cdc_events:
    "cdc_events_of ex_R = H_ex"
  and ex_chunks_list: "chunks_list ex_R = [ex_ch_A, ex_ch_B]"

text \<open>
  @{const clean_prefix_of} is a run-derived @{command definition}
  (@{thm clean_prefix_of_def}); for @{text ex_R} it is derived from the
  pinned accessors above rather than axiomatized on the run. The
  @{text ex_chunks_list} axiom pins @{term "chunks_list ex_R"} (an
  abstract accessor, constrained by @{thm chunks_list_set} /
  @{thm chunks_list_distinct} to a permutation of
  @{term "{ex_ch_A, ex_ch_B}"}) to one chunk enumeration, making the
  derived clean prefix a determinate computation.
\<close>

lemma ex_clean_prefix:
  "clean_prefix_of ex_R
     = [ Cdc ec1 (Update 100 3000),
         Refresh (100::nat) (Some (3000::nat))  ec1,
         Refresh 200 (Some 10000) ec1,
         Cdc ec2 (Insert 300 2500),
         Cdc ec3 (Update 200 12000),
         Refresh 300 (Some 2500) ec3,
         Cdc ec4 (Update 300 3500) ]"
proof -
  have dA: "sorted_list_of_set {100::nat, 200} = [100, 200]" by eval
  have dB: "sorted_list_of_set {300::nat} = [300]" by eval
  show ?thesis
    unfolding clean_prefix_of_def canonical_clean_prefix_def
              cdc_event_replays_def chunk_read_refreshes_def
    by (simp add: ex_chunks_list ex_dom_A ex_dom_B
                  ex_read_coord_A ex_read_coord_B
                  ex_chunk_read_result_A_100 ex_chunk_read_result_A_200
                  ex_chunk_read_result_B_300
                  ex_cdc_events ex_scope ex_frontier H_ex_def dA dB
                  List.map_filter_simps sort_key_def
                  ec1_le_ec2[unfolded src_le_eq_less_eq]
                  ec1_le_ec3[unfolded src_le_eq_less_eq]
                  ec1_le_ec4[unfolded src_le_eq_less_eq]
                  ec2_le_ec3[unfolded src_le_eq_less_eq]
                  ec2_le_ec4[unfolded src_le_eq_less_eq]
                  ec3_le_ec4[unfolded src_le_eq_less_eq]
                  not_src_le_ec2_ec1[unfolded src_le_eq_less_eq]
                  not_src_le_ec3_ec1[unfolded src_le_eq_less_eq]
                  not_src_le_ec4_ec1[unfolded src_le_eq_less_eq]
                  not_src_le_ec3_ec2[unfolded src_le_eq_less_eq]
                  not_src_le_ec4_ec2[unfolded src_le_eq_less_eq]
                  not_src_le_ec4_ec3[unfolded src_le_eq_less_eq])
qed

lemma chunks_ex_R_eq:
  "(ch \<in> chunks ex_R) \<longleftrightarrow> (ch = ex_ch_A \<or> ch = ex_ch_B)"
  using ex_chunks_set by simp

subsection \<open>Source-state computations on the example\<close>

text \<open>
  @{const Src} computations on the example data: the values
  @{text "Src b0_ex H_ex c"} takes at the chunk-read coordinates
  (used by WF6) and at the frontier (used by the final virtual-cut
  equality). Each lemma's proof unfolds @{const Src} +
  @{const latest_src_event} and reduces to a finite filter over
  @{text "[0, 1, 2, 3]"} using the @{text H_ex} nth lookups + the
  @{text src_le} chain.
\<close>

text \<open>
  Reusable helper: the candidate-index list specialised to the
  example. @{term "[0..<length H_ex]"} = @{text "[0, 1, 2, 3]"};
  filtering this list by a per-index predicate reduces by direct
  list computation under @{const filter}'s simp rules.
\<close>

lemma upt_length_H_ex: "[0..<length H_ex] = [0, 1, 2, 3]"
proof -
  have "length H_ex = 4" by (rule length_H_ex)
  thus ?thesis by (simp add: upt_rec)
qed

lemma latest_src_event_H_ex_ec1_100:
  "latest_src_event H_ex ec1 100 = Some 0"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_ex ! i)) ec1
                \<and> key_of (hist_event (H_ex ! i)) = (100::nat)"
  have "filter ?P [0, 1, 2, 3] = [0]"
    using src_le_refl[where c=ec1] not_src_le_ec2_ec1
          not_src_le_ec3_ec1 not_src_le_ec4_ec1
          H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
    by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_ex by simp
qed

lemma latest_src_event_H_ex_ec1_200:
  "latest_src_event H_ex ec1 200 = None"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_ex ! i)) ec1
                \<and> key_of (hist_event (H_ex ! i)) = (200::nat)"
  have "filter ?P [0, 1, 2, 3] = []"
    using src_le_refl[where c=ec1] not_src_le_ec2_ec1
          not_src_le_ec3_ec1 not_src_le_ec4_ec1
          H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
    by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_ex by simp
qed

lemma latest_src_event_H_ex_ec3_300:
  "latest_src_event H_ex ec3 300 = Some 1"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_ex ! i)) ec3
                \<and> key_of (hist_event (H_ex ! i)) = (300::nat)"
  have "filter ?P [0, 1, 2, 3] = [1]"
    using ec2_le_ec3 src_le_refl[where c=ec3] not_src_le_ec4_ec3
          H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
    by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_ex by simp
qed

lemma latest_src_event_H_ex_ec4_100:
  "latest_src_event H_ex ec4 100 = Some 0"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_ex ! i)) ec4
                \<and> key_of (hist_event (H_ex ! i)) = (100::nat)"
  have "filter ?P [0, 1, 2, 3] = [0]"
    using ec1_le_ec4 ec2_le_ec4 ec3_le_ec4 src_le_refl[where c=ec4]
          H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
    by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_ex by simp
qed

lemma latest_src_event_H_ex_ec4_200:
  "latest_src_event H_ex ec4 200 = Some 2"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_ex ! i)) ec4
                \<and> key_of (hist_event (H_ex ! i)) = (200::nat)"
  have "filter ?P [0, 1, 2, 3] = [2]"
    using ec1_le_ec4 ec2_le_ec4 ec3_le_ec4 src_le_refl[where c=ec4]
          H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
    by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_ex by simp
qed

lemma latest_src_event_H_ex_ec4_300:
  "latest_src_event H_ex ec4 300 = Some 3"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_ex ! i)) ec4
                \<and> key_of (hist_event (H_ex ! i)) = (300::nat)"
  have "filter ?P [0, 1, 2, 3] = [1, 3]"
    using ec1_le_ec4 ec2_le_ec4 ec3_le_ec4 src_le_refl[where c=ec4]
          H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
    by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_ex by simp
qed

text \<open>
  @{const Src} values at the chunk-read coordinates and at the
  frontier. WF6 uses the chunk-read-coordinate values; the final
  virtual-cut equality uses the frontier values.
\<close>

lemma Src_b0_ex_H_ex_ec1_100:
  "Src b0_ex H_ex ec1 100 = Some 3000"
  unfolding Src_def using latest_src_event_H_ex_ec1_100 H_ex_nth_0
  by simp

lemma Src_b0_ex_H_ex_ec1_200:
  "Src b0_ex H_ex ec1 200 = Some 10000"
  unfolding Src_def using latest_src_event_H_ex_ec1_200
  by (simp add: b0_ex_def)

lemma Src_b0_ex_H_ex_ec3_300:
  "Src b0_ex H_ex ec3 300 = Some 2500"
  unfolding Src_def using latest_src_event_H_ex_ec3_300 H_ex_nth_1
  by simp

lemma Src_b0_ex_H_ex_ec4_100:
  "Src b0_ex H_ex ec4 100 = Some 3000"
  unfolding Src_def using latest_src_event_H_ex_ec4_100 H_ex_nth_0
  by simp

lemma Src_b0_ex_H_ex_ec4_200:
  "Src b0_ex H_ex ec4 200 = Some 12000"
  unfolding Src_def using latest_src_event_H_ex_ec4_200 H_ex_nth_2
  by simp

lemma Src_b0_ex_H_ex_ec4_300:
  "Src b0_ex H_ex ec4 300 = Some 3500"
  unfolding Src_def using latest_src_event_H_ex_ec4_300 H_ex_nth_3
  by simp

subsection \<open>Wellformedness of the example source history\<close>

text \<open>
  WF-H1 / WF-H2 / WF-H3 hold for @{text H_ex} by an enumeration of
  the (at most) sixteen valid index pairs. Each clause is proven by
  unfolding @{text H_ex} to a literal four-element list and reducing
  the @{text "<"} bound on indices via @{text less_Suc_eq} so
  @{text simp} can dispatch each case directly.
\<close>

lemma less_4_cases: "(i :: nat) < 4 \<Longrightarrow> i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
  by linarith

lemma wf_h_ex_WFH1:
  "\<forall>i. Suc i < length H_ex
         \<longrightarrow> src_le (hist_coord (H_ex ! i))
                     (hist_coord (H_ex ! Suc i))"
proof (intro allI impI)
  fix i assume "Suc i < length H_ex"
  hence si_lt: "Suc i < 4" by (simp add: length_H_ex)
  hence i_lt: "i < 3" by linarith
  hence i_cases: "i = 0 \<or> i = 1 \<or> i = 2" by linarith
  consider (a) "i = 0" | (b) "i = 1" | (c) "i = 2" using i_cases by blast
  thus "src_le (hist_coord (H_ex ! i)) (hist_coord (H_ex ! Suc i))"
  proof cases
    case a thus ?thesis using ec1_le_ec2 by (simp add: H_ex_def)
  next
    case b thus ?thesis using ec2_le_ec3 by (simp add: H_ex_def)
  next
    case c thus ?thesis using ec3_le_ec4 by (simp add: H_ex_def)
  qed
qed

lemma wf_h_ex_WFH2:
  "\<forall>i. i < length H_ex \<longrightarrow> hist_coord (H_ex ! i) \<noteq> c0"
proof (intro allI impI)
  fix i assume "i < length H_ex"
  hence i_lt: "i < 4" by (simp add: length_H_ex)
  hence i_cases: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
    by (rule less_4_cases)
  consider (a) "i = 0" | (b) "i = 1" | (c) "i = 2" | (d) "i = 3"
    using i_cases by blast
  thus "hist_coord (H_ex ! i) \<noteq> c0"
  proof cases
    case a thus ?thesis using c0_neq_ec1 by (simp add: H_ex_def)
  next
    case b thus ?thesis using c0_neq_ec2 by (simp add: H_ex_def)
  next
    case c thus ?thesis using c0_neq_ec3 by (simp add: H_ex_def)
  next
    case d thus ?thesis using c0_neq_ec4 by (simp add: H_ex_def)
  qed
qed

lemma wf_h_ex_WFH3:
  "\<forall>i j. i < length H_ex \<and> j < length H_ex \<and> i \<noteq> j
            \<longrightarrow> source_pos_order H_ex i j \<or> source_pos_order H_ex j i"
proof (intro allI impI)
  fix i j
  assume A: "i < length H_ex \<and> j < length H_ex \<and> i \<noteq> j"
  hence i_lt: "i < 4" and j_lt: "j < 4" and ij_ne: "i \<noteq> j"
    by (auto simp: length_H_ex)
  have i_cases: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
    using i_lt by (rule less_4_cases)
  have j_cases: "j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3"
    using j_lt by (rule less_4_cases)
  \<comment> \<open>For each (i, j) pair with i \<noteq> j we either have i < j (and the
      coords are src_lt-related forward) or j < i (the reverse).\<close>
  show "source_pos_order H_ex i j \<or> source_pos_order H_ex j i"
  proof (cases "i < j")
    case True
    \<comment> \<open>i < j: hist_coord(H_ex ! i) src_lt-precedes hist_coord(H_ex ! j).\<close>
    show ?thesis
    proof (rule disjI1)
      show "source_pos_order H_ex i j"
        unfolding source_pos_order_def
      proof (rule disjI1)
        show "src_lt (hist_coord (H_ex ! i)) (hist_coord (H_ex ! j))"
          using i_cases j_cases True
                H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
                ec1_lt_ec2 ec2_lt_ec3 ec3_lt_ec4
                ec1_le_ec3 ec1_le_ec4 ec2_le_ec4
                ec1_neq_ec3 ec1_neq_ec4 ec2_neq_ec4
                src_lt_def
          by auto
      qed
    qed
  next
    case False
    hence j_lt_i: "j < i" using ij_ne by linarith
    show ?thesis
    proof (rule disjI2)
      show "source_pos_order H_ex j i"
        unfolding source_pos_order_def
      proof (rule disjI1)
        show "src_lt (hist_coord (H_ex ! j)) (hist_coord (H_ex ! i))"
          using i_cases j_cases j_lt_i
                H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
                ec1_lt_ec2 ec2_lt_ec3 ec3_lt_ec4
                ec1_le_ec3 ec1_le_ec4 ec2_le_ec4
                ec1_neq_ec3 ec1_neq_ec4 ec2_neq_ec4
                src_lt_def
          by auto
      qed
    qed
  qed
qed

lemma wf_h_ex: "wellformed_src_history H_ex"
  unfolding wellformed_src_history_def
  using wf_h_ex_WFH1 wf_h_ex_WFH2 wf_h_ex_WFH3
  by blast

subsection \<open>Apply on the example clean prefix\<close>

text \<open>
  Auxiliary @{const Apply} computation on the example clean prefix.
  The left-fold of @{const apply_step} over the explicit 7-event
  list reduces by case analysis: chunk A's refreshes for keys 100
  and 200 are \<^emph>\<open>raw-form\<close> present in the prefix; key 200's
  refresh is dominated at @{const Apply} time by the c3 CDC update;
  chunk B's refresh for key 300 is dominated by the c4 CDC update.
  Net result: key 100 \<mapsto> 3000, key 200 \<mapsto> 12000, key 300 \<mapsto> 3500.
\<close>

lemma apply_clean_prefix_ex:
  "Apply (clean_prefix_of ex_R)
     = (\<lambda>k. if k = (100::nat) then Some (3000::nat)
            else if k = 200 then Some 12000
            else if k = 300 then Some 3500
            else None)"
proof -
  have step:
    "Apply (clean_prefix_of ex_R)
       = foldl apply_step (\<lambda>_. None)
           [ Cdc ec1 (Update 100 3000),
             Refresh (100::nat) (Some (3000::nat)) ec1,
             Refresh 200 (Some 10000) ec1,
             Cdc ec2 (Insert 300 2500),
             Cdc ec3 (Update 200 12000),
             Refresh 300 (Some 2500) ec3,
             Cdc ec4 (Update 300 3500) ]"
    unfolding Apply_def ex_clean_prefix by (rule refl)
  show ?thesis
    unfolding step by (auto simp: fun_eq_iff fun_upd_def)
qed

subsection \<open>Wellformedness of the example run\<close>

text \<open>
  @{text "ex_wellformed_dblog_run"} discharges
  @{const wellformed_dblog_run} on the
  @{text "(b0_ex, ex_R, H_ex)"} instance. Each conjunct (WF0
  sub-conjuncts, WF1 (a)..(g), WF2 coverage, WF2 faithfulness, WF2
  order-preserving sublist, WF2 multiplicity, WF4, WF5, WF6 main,
  WF6 row-absence, and WF7 forward+reverse) is dischargeable by case
  analysis on the witness's axiomatized accessor values plus the
  helper computation lemmas above.
\<close>

lemma ex_wellformed_dblog_run:
  "wellformed_dblog_run b0_ex ex_R H_ex"
  unfolding wellformed_dblog_run_def
proof (intro conjI)
  \<comment> \<open>WF0 part 1: source-history binding.\<close>
  show "src_history_of ex_R = H_ex" by (rule ex_src_history)
next
  \<comment> \<open>WF0 part 2: source-history wellformedness.\<close>
  show "wellformed_src_history H_ex" by (rule wf_h_ex)
next
  \<comment> \<open>WF1 (a): unique responsible chunk per in-scope key.
       @{const owns} expands to set membership in
       @{const chunk_domain}, so the @{text "ex_dom_A"} /
       @{text "ex_dom_B"} axioms discharge both halves.\<close>
  show "\<forall>k\<in>scope_of ex_R. \<exists>!ch. ch \<in> chunks ex_R \<and> owns ex_R ch k"
  proof
    fix k :: nat assume "k \<in> scope_of ex_R"
    hence k_cases: "k = 100 \<or> k = 200 \<or> k = 300"
      using ex_scope by simp
    show "\<exists>!ch. ch \<in> chunks ex_R \<and> owns ex_R ch k"
    proof (cases "k = 100")
      case True
      have "ex_ch_A \<in> chunks ex_R \<and> owns ex_R ex_ch_A k"
        using ex_chunks_set ex_dom_A True by simp
      moreover have "\<And>ch. ch \<in> chunks ex_R \<and> owns ex_R ch k
                            \<Longrightarrow> ch = ex_ch_A"
        using chunks_ex_R_eq ex_dom_A ex_dom_B True by auto
      ultimately show ?thesis by blast
    next
      case False
      hence k_or: "k = 200 \<or> k = 300" using k_cases by simp
      show ?thesis
      proof (cases "k = 200")
        case True
        have "ex_ch_A \<in> chunks ex_R \<and> owns ex_R ex_ch_A k"
          using ex_chunks_set ex_dom_A True by simp
        moreover have "\<And>ch. ch \<in> chunks ex_R \<and> owns ex_R ch k
                              \<Longrightarrow> ch = ex_ch_A"
          using chunks_ex_R_eq ex_dom_A ex_dom_B True by auto
        ultimately show ?thesis by blast
      next
        case False
        hence k300: "k = 300" using k_or by simp
        have "ex_ch_B \<in> chunks ex_R \<and> owns ex_R ex_ch_B k"
          using ex_chunks_set ex_dom_B k300 by simp
        moreover have "\<And>ch. ch \<in> chunks ex_R \<and> owns ex_R ch k
                              \<Longrightarrow> ch = ex_ch_B"
          using chunks_ex_R_eq ex_dom_A ex_dom_B k300 by auto
        ultimately show ?thesis by blast
      qed
    qed
  qed
next
  \<comment> \<open>WF1 (b): chunk domains pairwise disjoint.\<close>
  show "\<forall>ch1\<in>chunks ex_R. \<forall>ch2\<in>chunks ex_R.
          ch1 \<noteq> ch2
            \<longrightarrow> chunk_domain ex_R ch1 \<inter> chunk_domain ex_R ch2 = {}"
    using chunks_ex_R_eq ex_dom_A ex_dom_B by auto
next
  \<comment> \<open>WF1 (c): canonical chunk-ownership domain equals scope.\<close>
  show "canonical_chunk_ownership_domain ex_R = scope_of ex_R"
    unfolding canonical_chunk_ownership_domain_def
    using ex_chunks_set ex_dom_A ex_dom_B ex_scope by auto
next
  \<comment> \<open>WF1 (d): responsible_chunk \<longleftrightarrow> ownership predicate.\<close>
  show "\<forall>k\<in>scope_of ex_R. \<forall>ch.
          responsible_chunk ex_R k = Some ch
            \<longleftrightarrow> ch \<in> chunks ex_R \<and> owns ex_R ch k"
  proof (intro ballI allI)
    fix k :: nat and ch :: "(nat, nat) chunk"
    assume "k \<in> scope_of ex_R"
    hence k_cases: "k = 100 \<or> k = 200 \<or> k = 300"
      using ex_scope by simp
    show "responsible_chunk ex_R k = Some ch
            \<longleftrightarrow> ch \<in> chunks ex_R \<and> owns ex_R ch k"
    proof (cases "k = 100")
      case True
      then have rc: "responsible_chunk ex_R k = Some ex_ch_A"
        using ex_resp_100 by simp
      show ?thesis
      proof
        assume "responsible_chunk ex_R k = Some ch"
        with rc have "ch = ex_ch_A" by simp
        thus "ch \<in> chunks ex_R \<and> owns ex_R ch k"
          using ex_chunks_set ex_dom_A True by simp
      next
        assume A: "ch \<in> chunks ex_R \<and> owns ex_R ch k"
        have "ch = ex_ch_A"
          using A chunks_ex_R_eq ex_dom_A ex_dom_B True by auto
        with rc show "responsible_chunk ex_R k = Some ch" by simp
      qed
    next
      case False
      hence k_or: "k = 200 \<or> k = 300" using k_cases by simp
      show ?thesis
      proof (cases "k = 200")
        case True
        then have rc: "responsible_chunk ex_R k = Some ex_ch_A"
          using ex_resp_200 by simp
        show ?thesis
        proof
          assume "responsible_chunk ex_R k = Some ch"
          with rc have "ch = ex_ch_A" by simp
          thus "ch \<in> chunks ex_R \<and> owns ex_R ch k"
            using ex_chunks_set ex_dom_A True by simp
        next
          assume A: "ch \<in> chunks ex_R \<and> owns ex_R ch k"
          have "ch = ex_ch_A"
            using A chunks_ex_R_eq ex_dom_A ex_dom_B True by auto
          with rc show "responsible_chunk ex_R k = Some ch" by simp
        qed
      next
        case False
        hence k300: "k = 300" using k_or by simp
        then have rc: "responsible_chunk ex_R k = Some ex_ch_B"
          using ex_resp_300 by simp
        show ?thesis
        proof
          assume "responsible_chunk ex_R k = Some ch"
          with rc have "ch = ex_ch_B" by simp
          thus "ch \<in> chunks ex_R \<and> owns ex_R ch k"
            using ex_chunks_set ex_dom_B k300 by simp
        next
          assume A: "ch \<in> chunks ex_R \<and> owns ex_R ch k"
          have "ch = ex_ch_B"
            using A chunks_ex_R_eq ex_dom_A ex_dom_B k300 by auto
          with rc show "responsible_chunk ex_R k = Some ch" by simp
        qed
      qed
    qed
  qed
next
  \<comment> \<open>WF1 (e): out-of-scope keys have no responsible chunk.\<close>
  show "\<forall>k. k \<notin> scope_of ex_R \<longrightarrow> responsible_chunk ex_R k = None"
    using ex_scope ex_resp_else by auto
next
  \<comment> \<open>WF1 (f) part 1: scope is finite.\<close>
  show "finite (scope_of ex_R)" using ex_scope by simp
next
  \<comment> \<open>WF1 (f) part 2: chunk domains are finite.\<close>
  show "\<forall>ch\<in>chunks ex_R. finite (chunk_domain ex_R ch)"
    using chunks_ex_R_eq ex_dom_A ex_dom_B by auto
next
  \<comment> \<open>WF1 (g): every chunk has a non-empty domain.\<close>
  show "\<forall>ch\<in>chunks ex_R. chunk_domain ex_R ch \<noteq> {}"
    using chunks_ex_R_eq ex_dom_A ex_dom_B by auto
next
  \<comment> \<open>WF2 coverage: observed CDC reaches every in-scope key.\<close>
  show "\<forall>k\<in>scope_of ex_R.
          covers_ordinary_cdc ex_R k (frontier_of ex_R)"
  proof
    fix k :: nat assume "k \<in> scope_of ex_R"
    hence k_cases: "k = 100 \<or> k = 200 \<or> k = 300"
      using ex_scope by simp
    show "covers_ordinary_cdc ex_R k (frontier_of ex_R)"
    proof (cases "k = 100")
      case True
      \<comment> \<open>chunk A's chunk_read_coordinate = ec1; events strictly
          after ec1 with key=100: NONE (only event for key 100 is
          at ec1 itself, which is NOT strictly greater than ec1).\<close>
      show ?thesis
        unfolding covers_ordinary_cdc_def
      proof (intro exI[where x = ex_ch_A] conjI allI impI)
        show "responsible_chunk ex_R k = Some ex_ch_A"
          using ex_resp_100 True by simp
      next
        fix i
        assume i_lt: "i < length (src_history_of ex_R)"
           and chunk_lt: "src_lt (chunk_read_coordinate ex_R ex_ch_A)
                                  (hist_coord (src_history_of ex_R ! i))"
           and to_f: "src_le (hist_coord (src_history_of ex_R ! i))
                              (frontier_of ex_R)"
           and key_eq: "key_of (hist_event (src_history_of ex_R ! i)) = k"
        \<comment> \<open>For key 100: only index 0 has key=100, but its coord
            ec1 fails the strict src_lt ec1 < coord premise.\<close>
        have i_lt4: "i < 4"
          using i_lt ex_src_history length_H_ex by simp
        have i_cases: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
          using i_lt4 by (rule less_4_cases)
        have False
        proof -
          consider (a) "i = 0" | (b) "i = 1"
                 | (c) "i = 2" | (d) "i = 3"
            using i_cases by blast
          thus False
          proof cases
            case a
            then show False using chunk_lt ex_src_history
                                  ex_read_coord_A H_ex_nth_0
                                  not_src_lt_ec1_ec1 by simp
          next
            case b
            then show False using key_eq ex_src_history
                                  H_ex_nth_1 True by simp
          next
            case c
            then show False using key_eq ex_src_history
                                  H_ex_nth_2 True by simp
          next
            case d
            then show False using key_eq ex_src_history
                                  H_ex_nth_3 True by simp
          qed
        qed
        thus "src_history_of ex_R ! i \<in> set (cdc_events_of ex_R)"
          ..
      qed
    next
      case False
      hence k_or: "k = 200 \<or> k = 300" using k_cases by simp
      show ?thesis
      proof (cases "k = 200")
        case True
        \<comment> \<open>chunk A's chunk_read_coordinate = ec1; events strictly
            after ec1 with key=200: index 2 = (ec3, Update 200
            12000); ec3 \<le> ec4 = frontier; the event is in
            cdc_events_of (which equals H_ex).\<close>
        show ?thesis
          unfolding covers_ordinary_cdc_def
        proof (intro exI[where x = ex_ch_A] conjI allI impI)
          show "responsible_chunk ex_R k = Some ex_ch_A"
            using ex_resp_200 True by simp
        next
          fix i
          assume i_lt: "i < length (src_history_of ex_R)"
             and chunk_lt: "src_lt (chunk_read_coordinate ex_R ex_ch_A)
                                    (hist_coord (src_history_of ex_R ! i))"
             and to_f: "src_le (hist_coord (src_history_of ex_R ! i))
                                (frontier_of ex_R)"
             and key_eq: "key_of (hist_event (src_history_of ex_R ! i)) = k"
          have i_lt4: "i < 4"
            using i_lt ex_src_history length_H_ex by simp
          have i_cases: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
            using i_lt4 by (rule less_4_cases)
          consider (a) "i = 0" | (b) "i = 1"
                 | (c) "i = 2" | (d) "i = 3"
            using i_cases by blast
          thus "src_history_of ex_R ! i \<in> set (cdc_events_of ex_R)"
          proof cases
            case a
            then show ?thesis using chunk_lt ex_src_history
                                    ex_read_coord_A H_ex_nth_0
                                    not_src_lt_ec1_ec1 by simp
          next
            case b
            then show ?thesis using key_eq ex_src_history
                                    H_ex_nth_1 True by simp
          next
            case c
            then show ?thesis using ex_src_history ex_cdc_events
                                    H_ex_nth_2 set_H_ex c by simp
          next
            case d
            then show ?thesis using key_eq ex_src_history
                                    H_ex_nth_3 True by simp
          qed
        qed
      next
        case False
        hence k300: "k = 300" using k_or by simp
        \<comment> \<open>chunk B's chunk_read_coordinate = ec3; events strictly
            after ec3 with key=300: index 3 = (ec4, Update 300
            3500); ec4 \<le> ec4; in cdc_events_of.\<close>
        show ?thesis
          unfolding covers_ordinary_cdc_def
        proof (intro exI[where x = ex_ch_B] conjI allI impI)
          show "responsible_chunk ex_R k = Some ex_ch_B"
            using ex_resp_300 k300 by simp
        next
          fix i
          assume i_lt: "i < length (src_history_of ex_R)"
             and chunk_lt: "src_lt (chunk_read_coordinate ex_R ex_ch_B)
                                    (hist_coord (src_history_of ex_R ! i))"
             and to_f: "src_le (hist_coord (src_history_of ex_R ! i))
                                (frontier_of ex_R)"
             and key_eq: "key_of (hist_event (src_history_of ex_R ! i)) = k"
          have i_lt4: "i < 4"
            using i_lt ex_src_history length_H_ex by simp
          have i_cases: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
            using i_lt4 by (rule less_4_cases)
          consider (a) "i = 0" | (b) "i = 1"
                 | (c) "i = 2" | (d) "i = 3"
            using i_cases by blast
          thus "src_history_of ex_R ! i \<in> set (cdc_events_of ex_R)"
          proof cases
            case a
            then show ?thesis using key_eq ex_src_history
                                    H_ex_nth_0 k300 by simp
          next
            case b
            then show ?thesis using chunk_lt ex_src_history
                                    ex_read_coord_B H_ex_nth_1
                                    not_src_lt_ec3_ec2 by simp
          next
            case c
            then show ?thesis using chunk_lt ex_src_history
                                    ex_read_coord_B H_ex_nth_2
                                    not_src_lt_ec3_ec3 by simp
          next
            case d
            then show ?thesis using ex_src_history ex_cdc_events
                                    H_ex_nth_3 set_H_ex d by simp
          qed
        qed
      qed
    qed
  qed
next
  \<comment> \<open>WF2 faithfulness: cdc_events_of \<subseteq> src_history_of
      (equal here); the in-scope-and-at-or-before-frontier filter
      holds everywhere in the example.\<close>
  show "\<forall>p\<in>set (cdc_events_of ex_R).
          key_of (hist_event p) \<in> scope_of ex_R
          \<and> src_le (hist_coord p) (frontier_of ex_R)
          \<longrightarrow> p \<in> set (src_history_of ex_R)"
    using ex_cdc_events ex_src_history by auto
next
  \<comment> \<open>WF2 order-preserving sublist: on the
      in-scope/at-or-before-frontier slice, cdc_events_of ex_R is an
      order-preserving sublist of src_history_of ex_R. For this
      witness, cdc_events_of ex_R = src_history_of ex_R (equal
      lists), so the identity function discharges the strict_mono ι
      obligation trivially.\<close>
  show "\<exists>\<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
          \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of ex_R
                                   \<and> src_le (hist_coord p) (frontier_of ex_R));
                 cdc_in_slice  = filter in_slice (cdc_events_of ex_R);
                 hist_in_slice = filter in_slice (src_history_of ex_R)
             in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                    \<iota> i < length hist_in_slice
                  \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
  proof (intro exI[where x="\<lambda>n :: nat. n"] conjI)
    show "strict_mono (\<lambda>n :: nat. n)" by (simp add: strict_mono_def)
  next
    have eq: "cdc_events_of ex_R = src_history_of ex_R"
      using ex_cdc_events ex_src_history by simp
    show "let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of ex_R
                                \<and> src_le (hist_coord p) (frontier_of ex_R));
              cdc_in_slice  = filter in_slice (cdc_events_of ex_R);
              hist_in_slice = filter in_slice (src_history_of ex_R)
          in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                 (\<lambda>n :: nat. n) i < length hist_in_slice
               \<and> cdc_in_slice ! i = hist_in_slice ! (\<lambda>n :: nat. n) i"
      using eq by (simp add: Let_def)
  qed
next
  \<comment> \<open>WF2 post-read same-key/same-coordinate multiplicity:
      cdc_events_of ex_R = src_history_of ex_R, so every filtered
      slice has identical multisets.\<close>
  show "\<forall>k\<in>scope_of ex_R. \<forall>ch c.
          responsible_chunk ex_R k = Some ch
          \<and> src_lt (chunk_read_coordinate ex_R ch) c
          \<and> src_le c (frontier_of ex_R)
          \<longrightarrow>
            mset (source_key_coord_slice k c (cdc_events_of ex_R))
            = mset (source_key_coord_slice k c (src_history_of ex_R))"
  proof (intro ballI allI impI)
    fix k :: nat and ch :: "(nat, nat) chunk" and c :: src_coord
    have eq: "cdc_events_of ex_R = src_history_of ex_R"
      using ex_cdc_events ex_src_history by simp
    show "mset (source_key_coord_slice k c (cdc_events_of ex_R))
          = mset (source_key_coord_slice k c (src_history_of ex_R))"
      using eq by simp
  qed
next
  \<comment> \<open>WF4: chunk-read evidence (watermark + totality + Refresh
      agreement on chunk_domain). Watermark axioms set lwm = uwm =
      chunk_read_coord; totality is by axiom; Refresh agreement is
      by chunk-and-key-case analysis against the explicit clean
      prefix.\<close>
  show "\<forall>ch\<in>chunks ex_R.
          src_le (chunk_lower_watermark ex_R ch)
                  (chunk_read_coordinate ex_R ch)
        \<and> src_le (chunk_read_coordinate ex_R ch)
                  (chunk_upper_watermark ex_R ch)
        \<and> (\<forall>k\<in>chunk_domain ex_R ch.
             \<exists>m. chunk_read_result ex_R ch k = Some m)
        \<and> (\<forall>k\<in>chunk_domain ex_R ch. \<forall>m.
             chunk_read_result ex_R ch k = Some m
               \<longleftrightarrow> Refresh k m (chunk_read_coordinate ex_R ch)
                    \<in> set (clean_prefix_of ex_R))"
  proof
    fix ch :: "(nat, nat) chunk"
    assume ch_in: "ch \<in> chunks ex_R"
    hence ch_cases: "ch = ex_ch_A \<or> ch = ex_ch_B"
      using chunks_ex_R_eq by simp
    show "src_le (chunk_lower_watermark ex_R ch)
                  (chunk_read_coordinate ex_R ch)
        \<and> src_le (chunk_read_coordinate ex_R ch)
                  (chunk_upper_watermark ex_R ch)
        \<and> (\<forall>k\<in>chunk_domain ex_R ch.
             \<exists>m. chunk_read_result ex_R ch k = Some m)
        \<and> (\<forall>k\<in>chunk_domain ex_R ch. \<forall>m.
             chunk_read_result ex_R ch k = Some m
               \<longleftrightarrow> Refresh k m (chunk_read_coordinate ex_R ch)
                    \<in> set (clean_prefix_of ex_R))"
    proof (cases "ch = ex_ch_A")
      case True
      \<comment> \<open>chunk A: domain {100, 200}; watermarks tight at ec1;
          Refresh agreement: chunk_read_result A 100 = Some (Some
          3000) iff Refresh 100 (Some 3000) ec1 \<in> clean_prefix
          (yes, item 2 in the prefix); same for key 200 (item 3).
          Other m values for key 100 are excluded because the only
          Refresh 100 _ ec1 in the prefix has m = Some 3000.\<close>
      show ?thesis
        using True ex_lwm_A ex_uwm_A ex_read_coord_A
              src_le_refl
              ex_dom_A
              ex_chunk_read_result_A_100
              ex_chunk_read_result_A_200
              ex_clean_prefix
        by auto
    next
      case False
      hence ch_B: "ch = ex_ch_B" using ch_cases by simp
      \<comment> \<open>chunk B: domain {300}; watermarks tight at ec3; Refresh
          agreement: chunk_read_result B 300 = Some (Some 2500)
          iff Refresh 300 (Some 2500) ec3 \<in> clean_prefix (yes,
          item 6 in the prefix). Other m values excluded by the
          singular Refresh 300 _ ec3 in the prefix.\<close>
      show ?thesis
        using ch_B ex_lwm_B ex_uwm_B ex_read_coord_B
              src_le_refl
              ex_dom_B
              ex_chunk_read_result_B_300
              ex_clean_prefix
              ec1_neq_ec3 ec1_neq_ec2 ec2_neq_ec3
        by auto
    qed
  qed
next
  \<comment> \<open>WF5: chunk-read coordinate at-or-before frontier.\<close>
  show "\<forall>ch\<in>chunks ex_R.
          src_le (chunk_read_coordinate ex_R ch) (frontier_of ex_R)"
    using chunks_ex_R_eq ex_read_coord_A ex_read_coord_B
          ex_frontier ec1_le_ec4 ec3_le_ec4
    by auto
next
  \<comment> \<open>WF6 main: refresh correctness against Src b0_ex H_ex
      (chunk_read_coordinate ex_R ch).\<close>
  show "\<forall>ch\<in>chunks ex_R. \<forall>k\<in>chunk_domain ex_R ch. \<forall>m.
          chunk_read_result ex_R ch k = Some m
            \<longrightarrow> m = Src b0_ex H_ex (chunk_read_coordinate ex_R ch) k"
  proof
    fix ch :: "(nat, nat) chunk"
    assume ch_in: "ch \<in> chunks ex_R"
    hence ch_cases: "ch = ex_ch_A \<or> ch = ex_ch_B"
      using chunks_ex_R_eq by simp
    show "\<forall>k\<in>chunk_domain ex_R ch. \<forall>m.
            chunk_read_result ex_R ch k = Some m
              \<longrightarrow> m = Src b0_ex H_ex (chunk_read_coordinate ex_R ch) k"
    proof (cases "ch = ex_ch_A")
      case True
      show ?thesis
        using True ex_dom_A
              ex_chunk_read_result_A_100
              ex_chunk_read_result_A_200
              ex_read_coord_A
              Src_b0_ex_H_ex_ec1_100
              Src_b0_ex_H_ex_ec1_200
        by auto
    next
      case False
      hence ch_B: "ch = ex_ch_B" using ch_cases by simp
      show ?thesis
        using ch_B ex_dom_B
              ex_chunk_read_result_B_300
              ex_read_coord_B
              Src_b0_ex_H_ex_ec3_300
        by auto
    qed
  qed
next
  \<comment> \<open>WF6 row-absence: vacuously true on ex_R — no in-domain
       key has chunk_read_result = Some None (all three observed
       values are Some (Some _)). Direct discharge via case analysis
       on the (ch, k) pair: in each of the three cases
       (ex_ch_A, 100), (ex_ch_A, 200), (ex_ch_B, 300), the
       chunk_read_result axiom contradicts the antecedent
       chunk_read_result = Some None.\<close>
  show "\<forall>ch\<in>chunks ex_R. \<forall>k\<in>chunk_domain ex_R ch.
          chunk_read_result ex_R ch k = Some None
            \<longrightarrow> row_absence_meaningful b0_ex H_ex ex_R ch k"
  proof (intro ballI impI)
    fix ch :: "(nat, nat) chunk" and k :: nat
    assume ch_in: "ch \<in> chunks ex_R"
       and k_in: "k \<in> chunk_domain ex_R ch"
       and crr: "chunk_read_result ex_R ch k = Some None"
    from ch_in chunks_ex_R_eq
      have ch_cases: "ch = ex_ch_A \<or> ch = ex_ch_B" by simp
    have False
    proof (cases "ch = ex_ch_A")
      case True
      with k_in ex_dom_A have "k = 100 \<or> k = 200" by simp
      with True crr ex_chunk_read_result_A_100
            ex_chunk_read_result_A_200 show False by auto
    next
      case False
      with ch_cases have ch_B: "ch = ex_ch_B" by simp
      with k_in ex_dom_B have "k = 300" by simp
      with ch_B crr ex_chunk_read_result_B_300 show False by simp
    qed
    thus "row_absence_meaningful b0_ex H_ex ex_R ch k" ..
  qed
next
  \<comment> \<open>WF7 forward: every observed CDC event in scope and
       at-or-before frontier appears as a Cdc replay event in
       clean_prefix_of(R). Discharges by case analysis on the 4
       elements of the explicit cdc_events_of(ex_R) = H_ex list;
       each maps to its corresponding Cdc event in clean_prefix_of
       ex_R.\<close>
  show "\<forall>p \<in> set (cdc_events_of ex_R).
          key_of (hist_event p) \<in> scope_of ex_R
          \<and> src_le (hist_coord p) (frontier_of ex_R)
          \<longrightarrow> Cdc (hist_coord p) (hist_event p)
                \<in> set (clean_prefix_of ex_R)"
  proof (intro ballI impI)
    fix p :: "src_coord \<times> (nat, nat) source_event"
    assume p_in: "p \<in> set (cdc_events_of ex_R)"
    hence p_cases: "p = (ec1, Update 100 3000)
                    \<or> p = (ec2, Insert 300 2500)
                    \<or> p = (ec3, Update 200 12000)
                    \<or> p = (ec4, Update 300 3500)"
      using ex_cdc_events set_H_ex by simp
    show "Cdc (hist_coord p) (hist_event p)
            \<in> set (clean_prefix_of ex_R)"
      using p_cases ex_clean_prefix by fastforce
  qed
next
  \<comment> \<open>WF7 reverse: every Cdc event in clean_prefix_of(R) in
       scope and at-or-before frontier has a witness in
       cdc_events_of(R). Discharges by case analysis on the 7
       elements of the explicit clean_prefix_of(ex_R) list; the 3
       Refresh elements fail the Cdc-shape antecedent by datatype
       distinctness, the 4 Cdc elements have direct witnesses in
       cdc_events_of ex_R = H_ex.\<close>
  show "\<forall>e c. Cdc c e \<in> set (clean_prefix_of ex_R)
                 \<and> key_of e \<in> scope_of ex_R
                 \<and> src_le c (frontier_of ex_R)
                 \<longrightarrow> (c, e) \<in> set (cdc_events_of ex_R)"
  proof (intro allI impI)
    fix e :: "(nat, nat) source_event" and c :: src_coord
    assume "Cdc c e \<in> set (clean_prefix_of ex_R)
              \<and> key_of e \<in> scope_of ex_R
              \<and> src_le c (frontier_of ex_R)"
    hence cdc_in: "Cdc c e \<in> set (clean_prefix_of ex_R)" by simp
    have list_eq: "Cdc c e \<in> set [ Cdc ec1 (Update 100 3000),
                                    Refresh (100::nat) (Some (3000::nat)) ec1,
                                    Refresh 200 (Some 10000) ec1,
                                    Cdc ec2 (Insert 300 2500),
                                    Cdc ec3 (Update 200 12000),
                                    Refresh 300 (Some 2500) ec3,
                                    Cdc ec4 (Update 300 3500) ]"
      using cdc_in ex_clean_prefix by simp
    hence "(c = ec1 \<and> e = Update 100 3000)
            \<or> (c = ec2 \<and> e = Insert 300 2500)
            \<or> (c = ec3 \<and> e = Update 200 12000)
            \<or> (c = ec4 \<and> e = Update 300 3500)"
      by auto
    thus "(c, e) \<in> set (cdc_events_of ex_R)"
      using ex_cdc_events set_H_ex by auto
  qed
qed

subsection \<open>Virtual-cut equality on the example (Layer 2 conclusion)\<close>

text \<open>
  Headline of this theory: the assembled replay's per-key state,
  restricted to the chunk-covered scope, equals the source state at
  the chosen frontier restricted to the same scope. This is the
  conclusion of paper Lemma 1.1 ("Wellformed-run replay equality on
  scope") on the running-example instance.

  The paper-level reading is:
    ``Apply(clean_prefix_of(ex_R)) restricted to scope_of(ex_R)
      equals Src(b0_ex, H_ex, frontier_of(ex_R)) restricted to
      scope_of(ex_R).''

  Coverage of the seven-item replay sequence: items 1 + 2 establish
  key 100 \<mapsto> 3000 (CDC + matching refresh; refresh confirms);
  item 3 establishes key 200 \<mapsto> 10000 (chunk A's stale
  observation); item 4 establishes key 300 \<mapsto> 2500 (Carol's
  insert); item 5 overrides key 200 to 12000 (CDC dominates chunk
  A's stale refresh); item 6 confirms key 300 = 2500 (chunk B's
  stale refresh; redundant, will be overridden); item 7 overrides
  key 300 to 3500 (CDC dominates chunk B's stale refresh).

  Source-state reading at frontier ec4: latest event for key 100 is
  the c1 update; latest event for key 200 is the c3 update; latest
  event for key 300 is the c4 update; @{text b0_ex} contributes
  Carol's @{term None} (overridden by the c2 insert). Per-key
  outcomes therefore agree across both views, on each of the three
  keys in scope.
\<close>

theorem ex_virtual_cut_holds:
  "restrict (Apply (clean_prefix_of ex_R)) (scope_of ex_R)
     = restrict (Src b0_ex H_ex (frontier_of ex_R)) (scope_of ex_R)"
proof
  fix k :: nat
  show "restrict (Apply (clean_prefix_of ex_R)) (scope_of ex_R) k
          = restrict (Src b0_ex H_ex (frontier_of ex_R)) (scope_of ex_R) k"
  proof (cases "k \<in> scope_of ex_R")
    case True
    hence k_cases: "k = 100 \<or> k = 200 \<or> k = 300"
      using ex_scope by simp
    show ?thesis
    proof (cases "k = 100")
      case True
      then show ?thesis
        unfolding restrict_def
        using \<open>k \<in> scope_of ex_R\<close>
              apply_clean_prefix_ex
              Src_b0_ex_H_ex_ec4_100
              ex_frontier
        by simp
    next
      case False
      hence "k = 200 \<or> k = 300" using k_cases by simp
      show ?thesis
      proof (cases "k = 200")
        case True
        then show ?thesis
          unfolding restrict_def
          using \<open>k \<in> scope_of ex_R\<close>
                apply_clean_prefix_ex
                Src_b0_ex_H_ex_ec4_200
                ex_frontier
          by simp
      next
        case False
        hence k300: "k = 300" using \<open>k = 200 \<or> k = 300\<close> by simp
        then show ?thesis
          unfolding restrict_def
          using \<open>k \<in> scope_of ex_R\<close>
                apply_clean_prefix_ex
                Src_b0_ex_H_ex_ec4_300
                ex_frontier
          by simp
      qed
    qed
  next
    case False
    show ?thesis
      unfolding restrict_def using False by simp
  qed
qed

text \<open>
  Composite "wellformed plus virtual-cut" theorem on the running
  example: the @{text "(b0_ex, ex_R, H_ex)"} instance satisfies
  @{const wellformed_dblog_run} AND its assembled replay equals the
  source state at the frontier on the chunk-covered scope. Together
  these two facts exhibit the Layer 2 source-side soundness
  conclusion (paper Lemma 1.1) on a non-trivial concrete instance.
\<close>

theorem ex_wellformed_and_virtual_cut:
  "wellformed_dblog_run b0_ex ex_R H_ex
    \<and> restrict (Apply (clean_prefix_of ex_R)) (scope_of ex_R)
        = restrict (Src b0_ex H_ex (frontier_of ex_R)) (scope_of ex_R)"
  using ex_wellformed_dblog_run ex_virtual_cut_holds by blast

end
