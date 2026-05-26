theory Layer3_Witnesses
  imports Virtual_Cut Layer01_Virtual_Cut_Example
begin

text \<open>
  Layer 3 accepted-certificate positive witness.

  This theory exercises the Layer 3 checker substrate on an
  axiomatized positive witness triple (a concrete
  certificate/evidence/Raw triple fixed by @{command axiomatization},
  not by a definitional checker construction). It reuses the
  running-example run @{const ex_R}, whose wellformedness is already
  proved in @{thm ex_wellformed_dblog_run}. The new Layer 3 constants
  below therefore witness only certificate/evidence behavior:

    \<^item> @{term l3_C} is accepted against @{term l3_E};
    \<^item> the evidence is bound to the certificate and belongs to the
      source-side checker schema;
    \<^item> the accepted pair materializes exactly the running-example
      run @{term ex_R};
    \<^item> certificate accessors agree with @{term ex_R}'s run
      accessors; and
    \<^item> @{term l3_Raw} is a faithful raw observation for the same
      @{term b0_ex} and @{term H_ex}.

  Relative to this axiomatized certificate/evidence/Raw fixture, the
  witness is non-vacuous: nonempty scope, non-base frontier, at least
  one chunk-read Refresh, a value-changing ordinary CDC event whose
  value matters, and an explicit faithful Raw/b0/H witness.
\<close>

section \<open>Accepted certificate/evidence instance\<close>

axiomatization
  l3_C   :: "(nat, nat) cert" and
  l3_E   :: "(nat, nat) evidence" and
  l3_Raw :: raw_observation
where
  l3_verify_accept:
    "verify l3_C l3_E = Accept"
and
  l3_evidence_bound:
    "evidence_bound_to_cert l3_C l3_E"
and
  l3_schema_supported:
    "source_side_schema_supported l3_C l3_E"
and
  l3_scope:
    "scope l3_C = scope_of ex_R"
and
  l3_frontier:
    "frontier l3_C = frontier_of ex_R"
and
  l3_clean_prefix:
    "clean_prefix l3_C = clean_prefix_of ex_R"
and
  l3_materializes_iff:
    "materializes_run l3_C l3_E R \<longleftrightarrow> R = ex_R"
and
  l3_faithful_iff:
    "faithful_source_observation l3_E b0 H Raw
      \<longleftrightarrow> b0 = b0_ex \<and> H = H_ex \<and> Raw = l3_Raw"

lemma l3_checker_input_ok:
  "checker_input_ok l3_C l3_E"
  unfolding checker_input_ok_def
  using l3_evidence_bound l3_schema_supported
  by blast

lemma l3_materializes_ex:
  "materializes_run l3_C l3_E ex_R"
  using l3_materializes_iff by simp

lemma l3_faithful_positive:
  "faithful_source_observation l3_E b0_ex H_ex l3_Raw"
  using l3_faithful_iff by simp

lemma l3_cert_accessors_agree_ex:
  "cert_accessors_agree l3_C ex_R"
  unfolding cert_accessors_agree_def
  using l3_scope l3_frontier l3_clean_prefix
  by simp

lemma l3_cert_run_coherent_ex:
  "cert_run_coherent l3_C l3_E ex_R"
  unfolding cert_run_coherent_def
  using l3_materializes_ex l3_cert_accessors_agree_ex
  by blast

section \<open>Checker-substrate interpretation\<close>

interpretation l3_witness_substrate: layer3_checker_substrate l3_C l3_E
proof
  assume "verify l3_C l3_E = Accept"
  show "checker_input_ok l3_C l3_E"
    by (rule l3_checker_input_ok)
next
  assume "verify l3_C l3_E = Accept"
     and "checker_input_ok l3_C l3_E"
  show "\<exists>R. materializes_run l3_C l3_E R"
    using l3_materializes_ex by blast
next
  fix R :: "(nat, nat) run"
  assume "verify l3_C l3_E = Accept"
     and "checker_input_ok l3_C l3_E"
     and mat: "materializes_run l3_C l3_E R"
  hence "R = ex_R"
    using l3_materializes_iff by blast
  thus "cert_accessors_agree l3_C R"
    using l3_cert_accessors_agree_ex by simp
next
  fix R :: "(nat, nat) run"
    and b0 :: "nat \<rightharpoonup> nat"
    and H :: "(nat, nat) src_history"
    and Raw :: raw_observation
  assume "verify l3_C l3_E = Accept"
     and "checker_input_ok l3_C l3_E"
     and mat: "materializes_run l3_C l3_E R"
     and faithful: "faithful_source_observation l3_E b0 H Raw"
  have R_eq: "R = ex_R"
    using mat l3_materializes_iff by blast
  have b0_eq: "b0 = b0_ex" and H_eq: "H = H_ex"
    using faithful l3_faithful_iff by blast+
  show "wellformed_dblog_run b0 R H"
    using ex_wellformed_dblog_run R_eq b0_eq H_eq by simp
qed

theorem l3_witness_accepted_certificate_implies_wellformed_run:
  "\<exists>R. wellformed_dblog_run b0_ex R H_ex
      \<and> cert_run_coherent l3_C l3_E R"
  using l3_witness_substrate.accepted_certificate_implies_wellformed_run
          [OF l3_verify_accept l3_faithful_positive]
  by blast

theorem l3_witness_accepted_virtual_cut_sound:
  "virtual_cut b0_ex l3_C H_ex"
  using l3_witness_substrate.accepted_virtual_cut_sound
          [OF l3_verify_accept l3_faithful_positive] .

section \<open>Non-vacuity and faithful Raw facts\<close>

lemma l3_scope_nonempty:
  "scope l3_C \<noteq> {}"
  using l3_scope ex_scope by simp

lemma l3_frontier_nonbase:
  "frontier l3_C \<noteq> c0"
  using l3_frontier ex_frontier c0_neq_ec4 by auto

lemma l3_clean_prefix_has_chunk_read:
  "Refresh (200::nat) (Some (10000::nat)) ec1
     \<in> set (clean_prefix l3_C)"
  using l3_clean_prefix ex_clean_prefix by simp

lemma l3_clean_prefix_has_value_changing_cdc:
  "Cdc ec3 (Update (200::nat) (12000::nat))
     \<in> set (clean_prefix l3_C)"
  using l3_clean_prefix ex_clean_prefix by simp

lemma l3_value_changes_on_key_200:
  "b0_ex 200 = Some 10000
   \<and> Apply (clean_prefix l3_C) 200 = Some 12000
   \<and> Src b0_ex H_ex (frontier l3_C) 200 = Some 12000"
  using l3_clean_prefix l3_frontier apply_clean_prefix_ex
        Src_b0_ex_H_ex_ec4_200 ex_frontier
  by (simp add: b0_ex_def)

theorem layer3_faithful_positive_raw_witness:
  "faithful_source_observation l3_E b0_ex H_ex l3_Raw"
  by (rule l3_faithful_positive)

theorem layer3_accepted_certificate_positive_witness:
  "\<exists>C E Raw b0 H R.
      verify C E = Accept
    \<and> faithful_source_observation E b0 H Raw
    \<and> checker_input_ok C E
    \<and> materializes_run C E R
    \<and> wellformed_dblog_run b0 R H
    \<and> cert_run_coherent C E R
    \<and> virtual_cut b0 C H
    \<and> scope C \<noteq> {}
    \<and> frontier C \<noteq> c0
    \<and> (\<exists>k m c. Refresh k (Some m) c \<in> set (clean_prefix C))
    \<and> Cdc ec3 (Update (200::nat) (12000::nat)) \<in> set (clean_prefix C)
    \<and> b0 200 = Some 10000
    \<and> Apply (clean_prefix C) 200 = Some 12000
    \<and> Src b0 H (frontier C) 200 = Some 12000"
proof -
  have refresh: "\<exists>k m c. Refresh k (Some m) c \<in> set (clean_prefix l3_C)"
    using l3_clean_prefix_has_chunk_read by blast
  show ?thesis
    using l3_verify_accept l3_faithful_positive l3_checker_input_ok
          l3_materializes_ex ex_wellformed_dblog_run
          l3_cert_run_coherent_ex l3_witness_accepted_virtual_cut_sound
          l3_scope_nonempty l3_frontier_nonbase refresh
          l3_clean_prefix_has_value_changing_cdc
          l3_value_changes_on_key_200
    by blast
qed

end
