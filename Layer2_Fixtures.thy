theory Layer2_Fixtures
  imports
    Virtual_Cut
    Layer01_Witnesses
    Layer01_Virtual_Cut_Example
    Layer01_Witness_Topics
    Layer01_Fixtures
begin

text \<open>
  Layer 2 fixture bundle. This theory collects the Layer 2
  fixture cases and connects them to the live Isabelle objects:

    \<^item> positive witnesses are lifted through
      @{thm wellformed_run_implies_virtual_cut};
    \<^item> WF-clause rejection rows reuse the Layer 1 negative
      fixtures, because Layer 2's theorem ranges over the same
      @{const wellformed_dblog_run} predicate;
    \<^item> canonical-clean-prefix rows that are structurally
      impossible are proved directly against
      @{const canonical_clean_prefix} / @{const cdc_event_replays}.

  No new run-carrier axioms are introduced here.
\<close>


section \<open>Positive Layer 2 witness lifts\<close>

theorem layer2_witness_virtual_cut_state:
  "virtual_cut_state b0_w (clean_prefix_of wit_R) (scope_of wit_R)
                     (frontier_of wit_R) H_w"
  using wf_witness_holds by (rule wellformed_run_implies_virtual_cut)

theorem layer2_worked_example_virtual_cut_state:
  "virtual_cut_state b0_ex (clean_prefix_of ex_R) (scope_of ex_R)
                     (frontier_of ex_R) H_ex"
  using ex_wellformed_dblog_run by (rule wellformed_run_implies_virtual_cut)

theorem layer2_topic1_virtual_cut_state:
  "virtual_cut_state b0_t1 (clean_prefix_of t1_R) (scope_of t1_R)
                     (frontier_of t1_R) H_t1"
  using t1_wellformed_dblog_run by (rule wellformed_run_implies_virtual_cut)

theorem layer2_topic2_virtual_cut_state:
  "virtual_cut_state b0_t2 (clean_prefix_of t2_R) (scope_of t2_R)
                     (frontier_of t2_R) H_t2"
  using t2_wellformed_dblog_run by (rule wellformed_run_implies_virtual_cut)


section \<open>Layer 2 WF-clause rejection fixtures\<close>

text \<open>
  These rows are Layer 2 rows because they protect the hypotheses of
  @{thm wellformed_run_implies_virtual_cut}. The counterexample
  shapes themselves are exactly the rejected @{const wellformed_dblog_run}
  shapes already encoded in Layer01_Fixtures.
\<close>

theorem fix_layer2_missing_cdc_event_rejected:
  "\<not> wellformed_dblog_run b0_md R_md H_md"
  by (rule fix_miss_dom_rejected)

theorem fix_layer2_overlapping_chunk_scope_rejected:
  "\<not> wellformed_dblog_run b0_ov R_ov H_ov"
  by (rule fix_overlap_rejected)

theorem fix_layer2_same_coordinate_cdc_order_rejected:
  "\<not> wellformed_dblog_run b0_do R_do H_do"
  by (rule fix_dup_order_rejected)

\<comment> \<open>Alias of @{text fix_layer2_same_coordinate_cdc_order_rejected}:
     both fixture-table labels name the same same-coordinate
     CDC-order counterexample @{text "(b0_do, R_do, H_do)"}; the
     theorem is retained under both names for cross-reference.\<close>
theorem fix_layer2_cdc_events_out_of_source_order_same_coord_rejected:
  "\<not> wellformed_dblog_run b0_do R_do H_do"
  by (rule fix_dup_order_rejected)

theorem fix_layer2_hallucinated_cdc_event_rejected:
  "\<not> wellformed_dblog_run b0_ec R_ec []"
  by (rule fix_extra_cdc_rejected)

theorem fix_layer2_future_refresh_from_chunk_read_after_frontier_rejected:
  "\<not> wellformed_dblog_run b0_caf R_caf H_caf"
  by (rule fix_after_f_rejected)

theorem fix_layer2_wrong_chunk_read_value_rejected:
  "\<not> wellformed_dblog_run b0_wr R_wr H_wr"
  by (rule fix_wrong_r_rejected)


section \<open>Canonical-clean-prefix structural fixtures\<close>

definition l2_one_refresh_read :: "(nat, nat) chunk_read_record" where
  "l2_one_refresh_read =
     \<lparr> crr_domain = {1},
       crr_read_coord = c0,
       crr_observation =
         (\<lambda>k. if k = (1::nat) then Some (Some (5::nat)) else None) \<rparr>"

lemma l2_one_refreshes:
  "chunk_read_refreshes l2_one_refresh_read =
     [Refresh (1::nat) (Some (5::nat)) c0]"
  unfolding l2_one_refresh_read_def chunk_read_refreshes_def
            List.map_filter_def
  by simp

axiomatization l2_cp_c1 :: src_coord
  where l2_cp_c0_lt_c1: "src_lt c0 l2_cp_c1"

lemma l2_cp_not_le_c0: "\<not> l2_cp_c1 \<le> c0"
  using l2_cp_c0_lt_c1
  unfolding less_eq_src_coord_def src_lt_def
  by (metis src_le_antisym)

theorem fix_layer2_misordered_clean_prefix_rejected:
  "canonical_clean_prefix
     [l2_one_refresh_read]
     [(l2_cp_c1, Update (1::nat) (7::nat))]
     {1} l2_cp_c1
   \<noteq> [Cdc l2_cp_c1 (Update (1::nat) (7::nat)),
       Refresh (1::nat) (Some (5::nat)) c0]"
  using l2_cp_c0_lt_c1 l2_cp_not_le_c0
  unfolding canonical_clean_prefix_def cdc_event_replays_def
            List.map_filter_def
  by (simp add: l2_one_refreshes less_src_coord_def src_lt_def)

theorem fix_layer2_extra_refresh_in_scope_rejected:
  "canonical_clean_prefix [l2_one_refresh_read] [] {1} c0
   \<noteq> [Refresh (1::nat) (Some (5::nat)) c0,
       Refresh (1::nat) (Some (99::nat)) c0]"
  unfolding canonical_clean_prefix_def cdc_event_replays_def
            List.map_filter_def
  by (simp add: l2_one_refreshes)

axiomatization l2_future_c1 :: src_coord
  where l2_future_c0_lt_c1: "src_lt c0 l2_future_c1"

lemma l2_future_not_le_c0: "\<not> l2_future_c1 \<le> c0"
  using l2_future_c0_lt_c1
  unfolding less_eq_src_coord_def src_lt_def
  by (metis src_le_antisym)

theorem fix_layer2_future_cdc_in_clean_prefix_rejected:
  "Cdc l2_future_c1 (Update (1::nat) (7::nat))
     \<notin> set (canonical_clean_prefix []
          [(l2_future_c1, Update (1::nat) (7::nat))] {1} c0)"
  using l2_future_not_le_c0
  unfolding canonical_clean_prefix_def cdc_event_replays_def
            List.map_filter_def
  by simp


section \<open>Frontier off-by-one subcases\<close>

axiomatization
      l2_fo_before :: src_coord
  and l2_fo_frontier :: src_coord
  and l2_fo_after :: src_coord
where
      l2_fo_before_lt_frontier: "src_lt l2_fo_before l2_fo_frontier"
  and l2_fo_frontier_lt_after:  "src_lt l2_fo_frontier l2_fo_after"

lemma l2_fo_before_le_frontier: "l2_fo_before \<le> l2_fo_frontier"
  using l2_fo_before_lt_frontier
  unfolding less_eq_src_coord_def src_lt_def by simp

lemma l2_fo_after_not_le_frontier: "\<not> l2_fo_after \<le> l2_fo_frontier"
  using l2_fo_frontier_lt_after
  unfolding less_eq_src_coord_def src_lt_def
  by (metis src_le_antisym)

theorem fix_layer2_frontier_off_by_one_before_included:
  "Cdc l2_fo_before (Update (1::nat) (7::nat))
     \<in> set (cdc_event_replays {1} l2_fo_frontier
          [(l2_fo_before, Update (1::nat) (7::nat))])"
  using l2_fo_before_le_frontier
  unfolding cdc_event_replays_def List.map_filter_def
  by simp

theorem fix_layer2_frontier_off_by_one_equal_included:
  "Cdc l2_fo_frontier (Update (1::nat) (7::nat))
     \<in> set (cdc_event_replays {1} l2_fo_frontier
          [(l2_fo_frontier, Update (1::nat) (7::nat))])"
  unfolding cdc_event_replays_def List.map_filter_def
  by (simp add: less_eq_src_coord_def src_le_refl)

theorem fix_layer2_frontier_off_by_one_after_rejected:
  "Cdc l2_fo_after (Update (1::nat) (7::nat))
     \<notin> set (cdc_event_replays {1} l2_fo_frontier
          [(l2_fo_after, Update (1::nat) (7::nat))])"
  using l2_fo_after_not_le_frontier
  unfolding cdc_event_replays_def List.map_filter_def
  by simp


section \<open>Bundle marker\<close>

theorem layer2_fixture_bundle_landed:
  "virtual_cut_state b0_w (clean_prefix_of wit_R) (scope_of wit_R)
                     (frontier_of wit_R) H_w
   \<and> \<not> wellformed_dblog_run b0_md R_md H_md
   \<and> \<not> wellformed_dblog_run b0_do R_do H_do
   \<and> Cdc l2_fo_frontier (Update (1::nat) (7::nat))
        \<in> set (cdc_event_replays {1} l2_fo_frontier
             [(l2_fo_frontier, Update (1::nat) (7::nat))])"
  using layer2_witness_virtual_cut_state
        fix_layer2_missing_cdc_event_rejected
        fix_layer2_same_coordinate_cdc_order_rejected
        fix_layer2_frontier_off_by_one_equal_included
  by blast

end
