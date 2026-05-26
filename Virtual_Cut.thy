theory Virtual_Cut
  imports Source_History Replay Scope DBLog_Run
begin

text \<open>
  Central formal object of the paper: the @{text virtual_cut}
  predicate over certificates.

  The virtual cut is a three-argument predicate
  @{text "virtual_cut b0 C H"}: under a deployment base state
  @{text b0}, certificate @{text C}, and source history @{text H},
  the replay of @{text "clean_prefix C"} on @{text "scope C"} equals
  the source state at @{text "frontier C"}. It is the
  certificate-accessor instance of the factored source-side core
  predicate @{text virtual_cut_state} (below), which both this
  cert-side definition and the Layer 2 run-side soundness theorem
  reduce to.

  The reader-facing paper notation suppresses the
  universally-quantified base state: the paper writes
  @{text "virtual_cut(C, H)"} where the formal predicate is
  @{text "virtual_cut b0 C H"}.

  This theory also assembles the Layer 3 checker substrate: the
  certificate carrier and accessors, the @{text verify_result}
  enumeration (@{text "Accept | Reject | Unsupported"}), the
  evidence and observation primitives, and the
  @{text materializes_run} relation (deliberately non-functional)
  support the @{text layer3_checker_substrate} locale, under whose
  primitive checker obligations the composed soundness theorem
  @{text accepted_virtual_cut_sound} is proved.

  Certificate accessors are bare-named (@{text "scope C"},
  @{text "frontier C"}, @{text "clean_prefix C"}); run accessors, in
  @{text DBLog_Run}, carry the @{text "_of"} suffix.
\<close>

subsection \<open>Certificate carrier and accessors\<close>

text \<open>
  Certificate accessors are bare-named --- @{text "scope C"},
  @{text "frontier C"}, @{text "clean_prefix C"} --- to mirror the
  paper's notation. Run accessors live in @{text DBLog_Run} with the
  @{text "_of"} suffix.
\<close>

typedecl ('k, 'v) cert

consts
  scope        :: "('k, 'v) cert \<Rightarrow> 'k set"
  frontier     :: "('k, 'v) cert \<Rightarrow> frontier"
  clean_prefix :: "('k, 'v) cert \<Rightarrow> ('k, 'v) replay_event list"

subsection \<open>Virtual cut state (factored core predicate)\<close>

text \<open>
  @{text virtual_cut_state} is the source-side extensional-equality
  core that both Layer 2 (over runs) and the Layer 3 cert-side
  @{text virtual_cut} reduce to:

  @{text "virtual_cut_state b0 \<sigma> K f H
            \<longleftrightarrow>
          restrict (Apply \<sigma>) K = restrict (Src b0 H f) K"}.

  The factoring abstracts over how @{text \<sigma>}, @{text K}, and
  @{text f} are obtained: certificate accessors
  @{text "(clean_prefix C, scope C, frontier C)"} on the cert side;
  run accessors @{text "(clean_prefix_of R, scope_of R,
  frontier_of R)"} on the run side. Both reduce to the same
  @{text virtual_cut_state} conclusion under their respective
  context --- cert: faithful evidence, verifier accept, and cert/run
  coherence; run: a wellformed DBLog run.

  The reader-facing paper notation suppresses the
  universally-quantified base state: the paper writes
  @{text "virtual_cut_state(\<sigma>, K, f, H)"} where the formal
  predicate is @{text "virtual_cut_state b0 \<sigma> K f H"} --- the
  same suppression convention that @{text virtual_cut} and
  @{text Src} use.
\<close>

definition virtual_cut_state
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) replay_event list \<Rightarrow> 'k set
      \<Rightarrow> frontier \<Rightarrow> ('k, 'v) src_history \<Rightarrow> bool"
where
  "virtual_cut_state b0 \<sigma> K f H \<longleftrightarrow>
     restrict (Apply \<sigma>) K = restrict (Src b0 H f) K"

subsection \<open>Virtual cut (cert-side instance of virtual cut state)\<close>

text \<open>
  On @{text "scope C"}, the replay of @{text "clean_prefix C"}
  equals the source state at @{text "frontier C"} under base state
  @{text b0}. @{text virtual_cut} is expressed as the
  certificate-accessor instance of @{text virtual_cut_state}; the
  expanded form
    @{text "Apply (clean_prefix C) \<restriction> scope C
            = Src b0 H (frontier C) \<restriction> scope C"}
  is recovered by unfolding @{text virtual_cut_def} and
  @{text virtual_cut_state_def}.
\<close>

definition virtual_cut
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) cert \<Rightarrow> ('k, 'v) src_history \<Rightarrow> bool"
where
  "virtual_cut b0 C H \<longleftrightarrow>
     virtual_cut_state b0 (clean_prefix C) (scope C) (frontier C) H"

subsection \<open>Layer 2 source-side soundness (over runs)\<close>

text \<open>
  Layer 2 ranges over runs, not certificates. Its conclusion is the
  run-side instance of @{text virtual_cut_state}; the cert-side
  @{text virtual_cut} predicate is reserved for Layer 3 composition
  via @{text cert_run_coherence}. @{text wellformed_dblog_run}, in
  @{text DBLog_Run}, is a real @{command definition} with a
  three-argument signature and a seven-clause body (WF0 / WF1 with
  subclauses (a)-(g) / WF2 with coverage, faithfulness, order-
  preserving sublist, and post-read multiplicity conjuncts / WF4 /
  WF5 / WF6 main + row-absence / WF7 forward + reverse). See
  @{text DBLog_Run} for the authoritative clause list.

  Paper Lemma 1.1 ("Wellformed-run replay equality on scope"):

  \<^verbatim>\<open>
    For any base state b0, any wellformed source history H, and any
    run R such that wellformed-DBLog-run(b0, R, H):

      Apply(clean_prefix_of(R)) \<restriction> scope_of(R)
        = Src(b0, H, frontier_of(R)) \<restriction> scope_of(R)
  \<close>

  The theorem below states this conclusion as
  @{text "virtual_cut_state b0 (clean_prefix_of R) (scope_of R)
  (frontier_of R) H"}; the expanded replay-equality form is
  recovered by unfolding @{thm virtual_cut_state_def}. It is proved
  by unfolding the factored @{const virtual_cut_state} predicate and
  applying the per-key equality lemma
  @{thm clean_prefix_of_per_key_replay_equals_source} pointwise.

  The result is \<^emph>\<open>Conditional\<close> at the paper level, on
  @{text "wellformed_dblog_run b0 R H"}; the Isabelle theorem is
  proved under that premise.
\<close>

theorem wellformed_run_implies_virtual_cut:
  assumes "wellformed_dblog_run b0 R H"
  shows
    "virtual_cut_state b0 (clean_prefix_of R) (scope_of R)
                       (frontier_of R) H"
  unfolding virtual_cut_state_def restrict_def
  by (intro ext)
     (auto intro: clean_prefix_of_per_key_replay_equals_source[OF assms])

subsection \<open>Layer 3 checker substrate: cert/evidence bridge + soundness\<close>

text \<open>
  @{text materializes_run} witnesses that an accepted certificate,
  paired with faithful evidence, can be associated with an abstract
  DBLog run. The relation is non-functional by design: verifier
  acceptance plus coherence, not the bare relation alone, prevents
  an accepted proof from choosing an arbitrary convenient run.

  @{text raw_observation} is the abstract carrier of external
  source-side observations. The predicate
  @{text "faithful_source_observation E b0 H Raw"} ties the evidence
  @{text E} to a fixed deployment base state @{text b0}, source
  history @{text H}, and raw observation @{text Raw}; its
  obligations are computed from the certificate-bound evidence
  @{text E}, and the assumption is discharged at deployment, not
  inside the model.

  @{text verify_result} is the verifier's result enumeration. The
  headline theorem reads @{text "verify C E = Accept"}; the result
  type reserves @{text Reject} / @{text Unsupported} for the
  rejection and parser branches that a concrete verifier
  distinguishes.

  The Layer 3 development introduces three theorems:
    \<^item> the intermediate
      @{text accepted_certificate_implies_wellformed_run}
      stated below (cert + evidence yields an existentially
      witnessed run @{text R} with @{text wellformed_dblog_run});
    \<^item> the cert / run coherence predicate and bridge lemma
      stated below; @{text cert_run_coherent} packages
      @{text materializes_run} with accessor agreement so the
      evidence parameter is load-bearing;
    \<^item> the composed @{text accepted_virtual_cut_sound} (the
      paper headline, also stated below), whose proof composes
      @{text accepted_certificate_implies_wellformed_run}
      (existentially witnessed @{text R}) with Layer 2's
      @{text wellformed_run_implies_virtual_cut} on @{text "(R, b0)"}
      and @{text cert_run_coherence} to substitute run accessors
      back to certificate accessors.

  The non-circular proof substrate is made explicit by the
  @{text layer3_checker_substrate} locale below. The locale does not
  assume the accepted-certificate theorem; instead it separates four
  primitive checker obligations:
    \<^item> accepted input is bound to the certificate and belongs to
      the source-side checker schema;
    \<^item> accepted input has at least one materialized run witness;
    \<^item> accepted materializations agree with the certificate
      semantic accessors; and
    \<^item> faithful accepted materializations are wellformed runs
      against the same @{text b0}, @{text H}, and @{text Raw}.
  The theorem is then proved inside the locale from those primitive
  obligations.
\<close>

typedecl ('k, 'v) evidence
typedecl raw_observation

datatype verify_result = Accept | Reject | Unsupported

consts
  verify                       :: "('k::linorder, 'v) cert \<Rightarrow> ('k, 'v) evidence \<Rightarrow> verify_result"
  faithful_source_observation  :: "('k::linorder, 'v) evidence \<Rightarrow> ('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) src_history \<Rightarrow> raw_observation \<Rightarrow> bool"
  materializes_run             :: "('k::linorder, 'v) cert \<Rightarrow> ('k, 'v) evidence \<Rightarrow> ('k, 'v) run \<Rightarrow> bool"
  evidence_bound_to_cert       :: "('k::linorder, 'v) cert \<Rightarrow> ('k, 'v) evidence \<Rightarrow> bool"
  source_side_schema_supported :: "('k::linorder, 'v) cert \<Rightarrow> ('k, 'v) evidence \<Rightarrow> bool"

definition checker_input_ok
  :: "('k::linorder, 'v) cert \<Rightarrow> ('k, 'v) evidence \<Rightarrow> bool"
where
  "checker_input_ok C E \<longleftrightarrow>
     evidence_bound_to_cert C E \<and> source_side_schema_supported C E"

definition cert_accessors_agree
  :: "('k::linorder, 'v) cert \<Rightarrow> ('k, 'v) run \<Rightarrow> bool"
where
  "cert_accessors_agree C R \<longleftrightarrow>
     scope C = scope_of R
   \<and> frontier C = frontier_of R
   \<and> clean_prefix C = clean_prefix_of R"

definition cert_run_coherent
  :: "('k::linorder, 'v) cert \<Rightarrow> ('k, 'v) evidence \<Rightarrow> ('k, 'v) run \<Rightarrow> bool"
where
  "cert_run_coherent C E R \<longleftrightarrow>
     materializes_run C E R \<and> cert_accessors_agree C R"

lemma cert_run_coherence:
  assumes "cert_run_coherent C E R"
  shows   "scope C = scope_of R
         \<and> frontier C = frontier_of R
         \<and> clean_prefix C = clean_prefix_of R"
  using assms
  unfolding cert_run_coherent_def cert_accessors_agree_def
  by blast

lemma cert_run_coherent_virtual_cut_state_subst:
  assumes "cert_accessors_agree C R"
      and "virtual_cut_state b0 (clean_prefix_of R) (scope_of R)
                             (frontier_of R) H"
  shows   "virtual_cut_state b0 (clean_prefix C) (scope C)
                             (frontier C) H"
  using assms
  unfolding cert_accessors_agree_def
  by simp

locale layer3_checker_substrate =
  fixes C :: "('k::linorder, 'v) cert"
    and E :: "('k, 'v) evidence"
  assumes accepted_input_ok:
    "verify C E = Accept \<Longrightarrow> checker_input_ok C E"
  and accepted_has_materialization:
    "\<lbrakk>verify C E = Accept; checker_input_ok C E\<rbrakk>
      \<Longrightarrow> \<exists>R. materializes_run C E R"
  and accepted_materialization_agrees:
    "\<And>R. \<lbrakk>verify C E = Accept; checker_input_ok C E;
      materializes_run C E R\<rbrakk>
      \<Longrightarrow> cert_accessors_agree C R"
  and faithful_materialization_wellformed:
    "\<And>R b0 H Raw. \<lbrakk>verify C E = Accept; checker_input_ok C E;
      materializes_run C E R; faithful_source_observation E b0 H Raw\<rbrakk>
      \<Longrightarrow> wellformed_dblog_run b0 R H"
begin

theorem accepted_certificate_implies_wellformed_run:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and Raw :: raw_observation
  assumes accept: "verify C E = Accept"
      and faithful: "faithful_source_observation E b0 H Raw"
  shows   "\<exists>R. wellformed_dblog_run b0 R H \<and> cert_run_coherent C E R"
proof -
  have input_ok: "checker_input_ok C E"
    by (rule accepted_input_ok[OF accept])
  then obtain R where mat: "materializes_run C E R"
    using accepted_has_materialization[OF accept input_ok] by blast
  have wf: "wellformed_dblog_run b0 R H"
    by (rule faithful_materialization_wellformed[OF accept input_ok mat faithful])
  have agree: "cert_accessors_agree C R"
    by (rule accepted_materialization_agrees[OF accept input_ok mat])
  have coherent: "cert_run_coherent C E R"
    using mat agree
    unfolding cert_run_coherent_def
    by blast
  show ?thesis
    using wf coherent by blast
qed

theorem accepted_virtual_cut_sound:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and Raw :: raw_observation
  assumes accept: "verify C E = Accept"
      and faithful: "faithful_source_observation E b0 H Raw"
  shows   "virtual_cut b0 C H"
proof -
  obtain R where wf: "wellformed_dblog_run b0 R H"
      and coherent: "cert_run_coherent C E R"
    using accepted_certificate_implies_wellformed_run[OF accept faithful]
    by blast
  have agree: "cert_accessors_agree C R"
    using coherent unfolding cert_run_coherent_def by blast
  have run_vcs:
    "virtual_cut_state b0 (clean_prefix_of R) (scope_of R)
                       (frontier_of R) H"
    using wellformed_run_implies_virtual_cut[OF wf] .
  have cert_vcs:
    "virtual_cut_state b0 (clean_prefix C) (scope C) (frontier C) H"
    using cert_run_coherent_virtual_cut_state_subst[OF agree run_vcs] .
  show ?thesis
    unfolding virtual_cut_def
    using cert_vcs .
qed

end

end
