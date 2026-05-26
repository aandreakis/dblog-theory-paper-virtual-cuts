theory Layer3_Fixtures
  imports Layer3_Witnesses
begin

text \<open>
  Layer 3 fixture bundle.  The positive accepted-certificate witness
  lives in the Layer3_Witnesses theory; this file collects the
  Layer 3 negative and boundary fixture cases.

  The fixtures are deliberately small.  The Layer 3 checker is
  specified through the primitive obligations of
  @{locale layer3_checker_substrate}; bad cases are therefore represented
  by showing that a candidate certificate/evidence pair is rejected,
  outside @{const checker_input_ok}, outside
  @{const faithful_source_observation}, or unable to satisfy those
  primitive obligations.  No fixture assumes the Layer 3 headline
  theorem as an axiom.

  Like the Layer 3 positive witness, these negative and boundary
  cases are abstract fixture scenarios: the verifier, materialization,
  and faithfulness behavior they exhibit is pinned by
  @{command axiomatization} over the primitive certificate / evidence
  predicates, not computed by a definitional or executable verifier.
\<close>


section \<open>Reusable coherence facts\<close>

lemma layer3_cert_accessor_determinacy:
  assumes "cert_accessors_agree C R1"
      and "cert_accessors_agree C R2"
  shows "scope_of R1 = scope_of R2
       \<and> frontier_of R1 = frontier_of R2
       \<and> clean_prefix_of R1 = clean_prefix_of R2"
  using assms
  unfolding cert_accessors_agree_def
  by simp

lemma layer3_mismatched_prefix_not_accessor_agree:
  assumes "cert_accessors_agree C R1"
      and "clean_prefix_of R2 \<noteq> clean_prefix_of R1"
  shows "\<not> cert_accessors_agree C R2"
  using assms
  unfolding cert_accessors_agree_def
  by auto


section \<open>Fixture constants\<close>

axiomatization
    l3_unmapped_E :: "(nat, nat) evidence"
where
    l3_unmapped_reject:
      "verify l3_C l3_unmapped_E = Reject"
  and l3_unmapped_not_bound:
      "\<not> evidence_bound_to_cert l3_C l3_unmapped_E"
  and l3_unmapped_no_materialization:
      "\<forall>R. \<not> materializes_run l3_C l3_unmapped_E R"

axiomatization
    l3_nowit_C :: "(nat, nat) cert"
  and l3_nowit_E :: "(nat, nat) evidence"
where
    l3_nowit_accept:
      "verify l3_nowit_C l3_nowit_E = Accept"
  and l3_nowit_bound:
      "evidence_bound_to_cert l3_nowit_C l3_nowit_E"
  and l3_nowit_schema:
      "source_side_schema_supported l3_nowit_C l3_nowit_E"
  and l3_nowit_no_materialization:
      "\<forall>R. \<not> materializes_run l3_nowit_C l3_nowit_E R"

axiomatization
    l3_alt_E :: "(nat, nat) evidence"
  and l3_alt_R :: "(nat, nat) run"
where
    l3_alt_reject:
      "verify l3_C l3_alt_E = Reject"
  and l3_alt_materializes:
      "materializes_run l3_C l3_alt_E l3_alt_R"
  and l3_alt_scope:
      "scope_of l3_alt_R = scope_of ex_R"
  and l3_alt_frontier:
      "frontier_of l3_alt_R = frontier_of ex_R"
  and l3_alt_chunks:
      "chunks l3_alt_R = {}"
  and l3_alt_cdc_events:
      "cdc_events_of l3_alt_R = []"

text \<open>
  @{const clean_prefix_of} is a run-derived @{command definition}
  (@{thm clean_prefix_of_def}); for @{text l3_alt_R} it is derived from
  the pinned accessors above rather than axiomatized on the run. The
  @{text l3_alt_chunks} and @{text l3_alt_cdc_events} axioms (no chunks,
  no observed CDC events) are the inputs from which
  @{term "clean_prefix_of l3_alt_R"} is then computed.
\<close>

lemma l3_alt_chunks_list: "chunks_list l3_alt_R = []"
  using chunks_list_set[of l3_alt_R] l3_alt_chunks by simp

lemma l3_alt_clean_prefix: "clean_prefix_of l3_alt_R = []"
  unfolding clean_prefix_of_def canonical_clean_prefix_def
            cdc_event_replays_def
  using l3_alt_chunks_list l3_alt_cdc_events
  by (simp add: List.map_filter_simps)

axiomatization
    l3_unfaithful_Raw :: raw_observation
where
    l3_unfaithful_raw_distinct:
      "l3_unfaithful_Raw \<noteq> l3_Raw"

definition l3_wrong_b0 :: "nat \<rightharpoonup> nat" where
  "l3_wrong_b0 = (\<lambda>k. if k = 200 then Some (999::nat) else b0_ex k)"

definition l3_wrong_H :: "(nat, nat) src_history" where
  "l3_wrong_H = []"

axiomatization
    l3_empty_C :: "(nat, nat) cert"
where
    l3_empty_scope:
      "scope l3_empty_C = {}"

axiomatization
    l3_unknown_E :: "(nat, nat) evidence"
where
    l3_unknown_unsupported:
      "verify l3_C l3_unknown_E = Unsupported"
  and l3_unknown_not_schema:
      "\<not> source_side_schema_supported l3_C l3_unknown_E"

axiomatization
    l3_other_C :: "(nat, nat) cert"
where
    l3_other_reject:
      "verify l3_other_C l3_E = Reject"
  and l3_other_not_bound:
      "\<not> evidence_bound_to_cert l3_other_C l3_E"


section \<open>Certificate/evidence binding failures\<close>

theorem layer3_unmapped_certificate_evidence_rejected:
  "verify l3_C l3_unmapped_E \<noteq> Accept
   \<and> \<not> checker_input_ok l3_C l3_unmapped_E
   \<and> (\<forall>R. \<not> materializes_run l3_C l3_unmapped_E R)"
  using l3_unmapped_reject l3_unmapped_not_bound
        l3_unmapped_no_materialization
  unfolding checker_input_ok_def
  by simp

theorem layer3_cert_evidence_binding_mismatch_rejected:
  "verify l3_other_C l3_E \<noteq> Accept
   \<and> \<not> checker_input_ok l3_other_C l3_E"
  using l3_other_reject l3_other_not_bound
  unfolding checker_input_ok_def
  by simp


section \<open>Materialization and non-circular substrate\<close>

lemma l3_nowit_checker_input_ok:
  "checker_input_ok l3_nowit_C l3_nowit_E"
  using l3_nowit_bound l3_nowit_schema
  unfolding checker_input_ok_def
  by simp

theorem layer3_accepted_but_witness_undefined_blocks_substrate:
  assumes materialization_obligation:
    "\<lbrakk>verify l3_nowit_C l3_nowit_E = Accept;
      checker_input_ok l3_nowit_C l3_nowit_E\<rbrakk>
      \<Longrightarrow> \<exists>R. materializes_run l3_nowit_C l3_nowit_E R"
  shows False
  using materialization_obligation[OF l3_nowit_accept l3_nowit_checker_input_ok]
        l3_nowit_no_materialization
  by blast

theorem layer3_non_circular_checker_spec_obligations:
  "verify l3_C l3_E = Accept
   \<and> checker_input_ok l3_C l3_E
   \<and> (\<exists>R. materializes_run l3_C l3_E R)
   \<and> (\<forall>R. materializes_run l3_C l3_E R
       \<longrightarrow> cert_accessors_agree l3_C R)
   \<and> (\<forall>R b0 H Raw.
       materializes_run l3_C l3_E R
       \<longrightarrow> faithful_source_observation l3_E b0 H Raw
       \<longrightarrow> wellformed_dblog_run b0 R H)"
proof -
  have mat_imp: "\<forall>R. materializes_run l3_C l3_E R
       \<longrightarrow> cert_accessors_agree l3_C R"
    using l3_materializes_iff l3_cert_accessors_agree_ex by auto
  have wf_imp: "\<forall>R b0 H Raw.
       materializes_run l3_C l3_E R
       \<longrightarrow> faithful_source_observation l3_E b0 H Raw
       \<longrightarrow> wellformed_dblog_run b0 R H"
  proof (intro allI impI)
    fix R :: "(nat, nat) run"
      and b0 :: "nat \<rightharpoonup> nat"
      and H :: "(nat, nat) src_history"
      and Raw :: raw_observation
    assume mat: "materializes_run l3_C l3_E R"
       and faithful: "faithful_source_observation l3_E b0 H Raw"
    have "R = ex_R"
      using mat l3_materializes_iff by blast
    moreover have "b0 = b0_ex" and "H = H_ex"
      using faithful l3_faithful_iff by blast+
    ultimately show "wellformed_dblog_run b0 R H"
      using ex_wellformed_dblog_run by simp
  qed
  show ?thesis
    using l3_verify_accept l3_checker_input_ok l3_materializes_ex
          mat_imp wf_imp
    by blast
qed


section \<open>Coherence and determinacy\<close>

lemma l3_alt_clean_prefix_differs:
  "clean_prefix_of l3_alt_R \<noteq> clean_prefix_of ex_R"
  using l3_alt_clean_prefix ex_clean_prefix by simp

lemma l3_alt_not_accessor_agree:
  "\<not> cert_accessors_agree l3_C l3_alt_R"
  using l3_cert_accessors_agree_ex l3_alt_clean_prefix_differs
        layer3_mismatched_prefix_not_accessor_agree
  by blast

theorem layer3_two_evidence_bundle_determinacy_fixture:
  "verify l3_C l3_alt_E \<noteq> Accept
   \<and> materializes_run l3_C l3_alt_E l3_alt_R
   \<and> \<not> cert_run_coherent l3_C l3_alt_E l3_alt_R"
  using l3_alt_reject l3_alt_materializes l3_alt_not_accessor_agree
  unfolding cert_run_coherent_def
  by simp

theorem layer3_cert_run_coherence_mismatch_rejected:
  "\<not> cert_run_coherent l3_C l3_E l3_alt_R"
  using l3_alt_not_accessor_agree
  unfolding cert_run_coherent_def
  by simp

theorem layer3_same_evidence_two_run_determinacy:
  "cert_accessors_agree l3_C R1
   \<Longrightarrow> cert_accessors_agree l3_C R2
   \<Longrightarrow> scope_of R1 = scope_of R2
     \<and> frontier_of R1 = frontier_of R2
     \<and> clean_prefix_of R1 = clean_prefix_of R2"
  by (rule layer3_cert_accessor_determinacy)

theorem layer3_same_evidence_mismatched_run_not_coherent:
  "\<not> cert_run_coherent l3_C l3_E l3_alt_R"
  by (rule layer3_cert_run_coherence_mismatch_rejected)


section \<open>Faithfulness negatives\<close>

lemma l3_wrong_b0_neq:
  "l3_wrong_b0 \<noteq> b0_ex"
  unfolding l3_wrong_b0_def b0_ex_def
  by (rule notI, drule fun_cong[where x=200], simp)

lemma l3_wrong_H_neq:
  "l3_wrong_H \<noteq> H_ex"
  unfolding l3_wrong_H_def H_ex_def
  by simp

theorem layer3_raw_observation_faithfulness_negative:
  "verify l3_C l3_E = Accept
   \<and> checker_input_ok l3_C l3_E
   \<and> \<not> faithful_source_observation l3_E b0_ex H_ex l3_unfaithful_Raw"
  using l3_verify_accept l3_checker_input_ok l3_unfaithful_raw_distinct
        l3_faithful_iff
  by blast

theorem layer3_raw_base_state_mismatch_rejected:
  "\<not> faithful_source_observation l3_E l3_wrong_b0 H_ex l3_Raw"
  using l3_wrong_b0_neq l3_faithful_iff
  by blast

theorem layer3_wrong_history_mismatch_rejected:
  "\<not> faithful_source_observation l3_E b0_ex l3_wrong_H l3_Raw"
  using l3_wrong_H_neq l3_faithful_iff
  by blast


section \<open>Empty-scope boundary\<close>

theorem layer3_empty_scope_virtual_cut_boundary:
  assumes "scope C = {}"
  shows "virtual_cut b0 C H"
  using assms
  unfolding virtual_cut_def virtual_cut_state_def restrict_def
  by simp

theorem layer3_empty_scope_boundary_not_positive_witness:
  "virtual_cut b0_ex l3_empty_C H_ex
   \<and> scope l3_empty_C = {}
   \<and> scope l3_C \<noteq> {}"
  using l3_empty_scope l3_scope_nonempty
        layer3_empty_scope_virtual_cut_boundary[OF l3_empty_scope]
  by simp


section \<open>Unknown or ignored evidence fields\<close>

theorem layer3_unknown_ignored_field_rejected:
  "verify l3_C l3_unknown_E = Unsupported
   \<and> verify l3_C l3_unknown_E \<noteq> Accept
   \<and> \<not> checker_input_ok l3_C l3_unknown_E"
  using l3_unknown_unsupported l3_unknown_not_schema
  unfolding checker_input_ok_def
  by simp


section \<open>Bundle marker\<close>

theorem layer3_fixture_bundle_landed:
  "verify l3_C l3_unmapped_E \<noteq> Accept
   \<and> (\<forall>R. \<not> materializes_run l3_C l3_unmapped_E R)
   \<and> verify l3_C l3_alt_E \<noteq> Accept
   \<and> \<not> cert_run_coherent l3_C l3_E l3_alt_R
   \<and> \<not> faithful_source_observation l3_E b0_ex H_ex l3_unfaithful_Raw
   \<and> \<not> faithful_source_observation l3_E l3_wrong_b0 H_ex l3_Raw
   \<and> scope l3_empty_C = {}
   \<and> verify l3_C l3_unknown_E = Unsupported
   \<and> verify l3_other_C l3_E \<noteq> Accept
   \<and> \<not> faithful_source_observation l3_E b0_ex l3_wrong_H l3_Raw"
  using layer3_unmapped_certificate_evidence_rejected
        layer3_two_evidence_bundle_determinacy_fixture
        layer3_cert_run_coherence_mismatch_rejected
        layer3_raw_observation_faithfulness_negative
        layer3_raw_base_state_mismatch_rejected
        layer3_empty_scope_boundary_not_positive_witness
        layer3_unknown_ignored_field_rejected
        layer3_cert_evidence_binding_mismatch_rejected
        layer3_wrong_history_mismatch_rejected
  by blast

end
