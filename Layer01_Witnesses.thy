theory Layer01_Witnesses
  imports DBLog_Run
begin

text \<open>
  Layer 1 wellformed-run positive witness.

  This theory exhibits a concrete non-vacuity witness for the Layer 1
  wellformed-DBLog-run predicate, discharging the seven-clause
  obligation (paper's "Wellformed run positive witness"):

    1. @{text b0} is non-empty (at least one key with non-@{term None});
    2. @{term "scope_of R"} is non-empty;
    3. @{text "card (chunks R) \<ge> 2"} (at least two chunks
       partitioning @{term "scope_of R"});
    4. at least one chunk whose chunk-read coordinate is at-or-below
       the earliest source event in @{text H} for some in-scope key
       (i.e., the chunk reads from base/pre-read state); the witness
       below uses @{text c0} as the chunk-read coordinate, which is
       at-or-below every source coordinate by @{thm c0_least};
    5. at least one ordinary CDC event in @{term "clean_prefix_of R"}
       post-chunk-read (after some chunk's read coordinate);
    6. at least one delete event OR one chunk-read-absence
       (@{text "Refresh k None c"}) case;
    7. @{term "Apply (clean_prefix_of R)"} restricted to
       @{term "scope_of R"} is non-trivial (neither the empty map
       nor the @{text b0}-on-scope map).

  The seven-clause obligation exhibits the wellformed-run predicate's
  non-vacuity: the witness instance constructed here shows the
  predicate is inhabited --- satisfiable at a concrete fixture
  instance. That is all a positive witness establishes;
  load-bearingness of the individual wellformedness clauses is
  exercised separately by the negative fixtures in theory
  @{text Layer01_Fixtures}.

  Construction approach. The Layer 1 run carrier
  @{typ "('k, 'v) run"} is a typedecl (no constructors), and the run
  accessors are @{command consts} (no defining axioms). The witness
  therefore cannot be a closed-form @{command definition} of a run
  with computable accessor values. Instead, the witness uses an
  @{command axiomatization} block to introduce a single concrete run
  constant @{text wit_R} along with axiom equations fixing each
  accessor's value on @{text wit_R}. The axioms are fixture axioms
  over fresh constants: they pin the accessor values of a new run
  constant @{text wit_R} and two new chunk constants @{text wit_ch1}
  / @{text wit_ch2}, and assert no global property of the abstract
  Layer 1 vocabulary, which stays unconstrained on every other run /
  chunk.

  Choice of types. The witness fixes @{text "'k = nat"} and
  @{text "'v = nat"} -- concrete, decidable types that let the
  7-clause obligations decompose to first-order computations.
  Concrete types are required to populate
  @{term "scope_of wit_R"} with a literal set @{text "{0, 1}"} and
  to populate @{text b0_w} with a literal partial map. One positive
  witness at one concrete type pair suffices for the non-vacuity
  obligation.

  Witness data summary:

    \<^item> @{text b0_w}:           key 7 \<mapsto> Some 100; all other
                              keys \<mapsto> None
                              (clauses 1, 7);
    \<^item> @{text H_w}:           @{text "[(c1_w, Insert 0 42),
                                          (c2_w, Delete 1)]"}
                              (events at distinct coordinates
                              @{text c1_w}, @{text c2_w} both above
                              @{text c0}; clauses 4, 5, 6, 7);
    \<^item> @{term "scope_of wit_R"}:        @{text "{0, 1}"} (clause 2);
    \<^item> @{term "chunks wit_R"}:           @{text "{wit_ch1, wit_ch2}"},
                                       distinct (clause 3);
    \<^item> @{term "chunk_domain wit_R wit_ch1"}:  @{text "{0}"};
                                       @{term "chunk_domain wit_R wit_ch2"}: @{text "{1}"}
                                       (strict partition over scope);
    \<^item> @{term "chunk_read_coordinate wit_R wit_ch1"}: @{text c0}
                                       (pre-history; clause 4);
                                       @{term "chunk_read_coordinate wit_R wit_ch2"}: @{text c2_w}
                                       (frontier);
    \<^item> @{term "frontier_of wit_R"}:     @{text c2_w};
    \<^item> @{term "chunk_read_result wit_R wit_ch1 0"}: @{text "Some None"}
                                       (key 0 unobserved at @{text c0};
                                        chunk-read absence);
                                       @{term "chunk_read_result wit_R wit_ch2 1"}: @{text "Some None"}
                                       (key 1 absent at @{text c2_w} -- key 1
                                        was deleted by the same-coord
                                        @{text Delete} event, post-which
                                        the chunk read observes None);
    \<^item> @{term "cdc_events_of wit_R"}:   @{text "[(c1_w, Insert 0 42),
                                                    (c2_w, Delete 1)]"};
    \<^item> @{term "clean_prefix_of wit_R"}: @{text "[Refresh 0 None c0,
                                                    Cdc c1_w (Insert 0 42),
                                                    Cdc c2_w (Delete 1),
                                                    Refresh 1 None c2_w]"}
                                       (clauses 5, 6, 7).

  @{const Apply} on this clean prefix produces
  @{text "(key 0 \<mapsto> Some 42, all others \<mapsto> None)"} (lemma
  @{text apply_clean_prefix_witness} below). This theory's witness
  theorem packages the seven wellformed-run clauses; it does
  \<^emph>\<open>not\<close> assert the Lemma 1.1 replay equality
  @{text "Apply (clean_prefix_of R) \<restriction> scope_of R
          = Src b0 H (frontier_of R) \<restriction> scope_of R"}.
  A positive witness that additionally carries the Lemma 1.1
  conclusion is the Topic 1 witness in @{text Layer01_Witness_Topics}.

  Witness theorem composition. The final theorem
  @{text wellformed_run_positive_witness} packages the seven
  paper-side clauses in existential form together with a
  @{const wellformed_dblog_run} conjunct at the witness instance
  @{text "(b0_w, wit_R, H_w)"}.

  Discharge proof shape: each clause of the wellformed-run body (WF0
  / WF1 / WF2 / WF4 / WF5 / WF6 / WF7) is dischargeable by case
  analysis on the witness's axiomatized accessor values plus the
  helper computation lemmas below (latest source event = @{term None}
  at @{text c0} for key 0; @{const Src} = @{term None} at the
  chunk-read coordinates for the in-domain keys; the pair shape of
  @{text wit_cdc_events} matched against @{text wit_clean_prefix} by
  @{text auto}). WF6 carries a row-absence conjunct
  (@{text row_absence_meaningful}); WF7 carries a bidirectional
  clean-prefix CDC-coherence conjunct.
\<close>

subsection \<open>Witness source coordinates\<close>

text \<open>
  Two source coordinates above @{text c0}, with @{text c0} below
  @{text c1_w} and @{text c1_w} below @{text c2_w}. The
  @{const src_lt} chain ensures the witness's source history events
  at @{text c1_w} and @{text c2_w} respect WF-H1 (non-decreasing
  source coordinates) and WF-H2 (no event at @{text c0}).
\<close>

axiomatization c1_w c2_w :: src_coord
where
  c0_lt_c1_w: "src_lt c0 c1_w"
  and c1_w_lt_c2_w: "src_lt c1_w c2_w"

lemma c0_neq_c1_w: "c0 \<noteq> c1_w"
  using c0_lt_c1_w by (simp add: src_lt_def)

lemma c0_le_c1_w: "src_le c0 c1_w"
  using c0_lt_c1_w by (simp add: src_lt_def)

lemma c1_w_neq_c2_w: "c1_w \<noteq> c2_w"
  using c1_w_lt_c2_w by (simp add: src_lt_def)

lemma c0_neq_c2_w: "c0 \<noteq> c2_w"
proof -
  have "src_le c1_w c2_w" using c1_w_lt_c2_w by (simp add: src_lt_def)
  hence "src_le c0 c2_w" using c0_le_c1_w src_le_trans by blast
  moreover have "c0 \<noteq> c1_w" by (rule c0_neq_c1_w)
  ultimately show ?thesis
    using c0_lt_c1_w c1_w_lt_c2_w
    by (metis src_lt_def src_le_antisym)
qed

subsection \<open>Witness base state and source history\<close>

definition b0_w :: "nat \<rightharpoonup> nat" where
  "b0_w = (\<lambda>k. if k = 7 then Some 100 else None)"

definition H_w :: "(nat, nat) src_history" where
  "H_w = [(c1_w, Insert 0 42), (c2_w, Delete 1)]"

subsection \<open>Witness run, chunks, and accessor values\<close>

text \<open>
  Single concrete run constant @{text wit_R} together with two
  concrete chunk constants @{text wit_ch1} / @{text wit_ch2}; all
  Layer 1 accessor values on these constants are fixed by axiom.

  The two @{const chunk_read_result} axiom equations cover the
  in-domain key cases that the seven witness clauses need to
  exercise; out-of-scope and out-of-domain combinations are left
  unconstrained at the consts level (the abstract Layer 1 vocabulary
  remains unconstrained on every other run / chunk). WF1 sub-clause
  (e) per paper "The wellformed-DBLog-run predicate" --
  @{text "\<forall>k. k \<notin> scope_of(R) \<longrightarrow>
                       responsible_chunk(R, k) = None"} -- is
  captured here via @{text wit_resp_else}.
\<close>

axiomatization
  wit_R    :: "(nat, nat) run" and
  wit_ch1  :: "(nat, nat) chunk" and
  wit_ch2  :: "(nat, nat) chunk"
where
  wit_chunks_distinct:    "wit_ch1 \<noteq> wit_ch2"
  and wit_scope:          "scope_of wit_R = {0, 1}"
  and wit_frontier:       "frontier_of wit_R = c2_w"
  and wit_chunks_set:     "chunks wit_R = {wit_ch1, wit_ch2}"
  and wit_dom_1:          "chunk_domain wit_R wit_ch1 = {0}"
  and wit_dom_2:          "chunk_domain wit_R wit_ch2 = {1}"
  \<comment> \<open>No separate ownership axioms are needed: @{const owns} is an
       @{command abbreviation} over @{text chunk_domain}, so
       @{text "owns wit_R wit_ch1 0"} is the set-membership fact
       @{text "0 \<in> chunk_domain wit_R wit_ch1"}, which follows from
       @{text wit_dom_1} by @{text simp}.\<close>
  and wit_resp_0:         "responsible_chunk wit_R 0 = Some wit_ch1"
  and wit_resp_1:         "responsible_chunk wit_R 1 = Some wit_ch2"
  and wit_resp_else:      "k \<noteq> 0 \<Longrightarrow> k \<noteq> 1
                            \<Longrightarrow> responsible_chunk wit_R k = None"
  and wit_read_coord_1:   "chunk_read_coordinate wit_R wit_ch1 = c0"
  and wit_read_coord_2:   "chunk_read_coordinate wit_R wit_ch2 = c2_w"
  and wit_lwm_1:          "chunk_lower_watermark wit_R wit_ch1 = c0"
  and wit_uwm_1:          "chunk_upper_watermark wit_R wit_ch1 = c0"
  and wit_lwm_2:          "chunk_lower_watermark wit_R wit_ch2 = c2_w"
  and wit_uwm_2:          "chunk_upper_watermark wit_R wit_ch2 = c2_w"
  and wit_src_history:    "src_history_of wit_R = H_w"
  and wit_chunk_read_result_1_0:
    "chunk_read_result wit_R wit_ch1 0 = Some None"
  and wit_chunk_read_result_2_1:
    "chunk_read_result wit_R wit_ch2 1 = Some None"
  and wit_cdc_events:
    "cdc_events_of wit_R
       = [(c1_w, Insert 0 42), (c2_w, Delete 1)]"
  and wit_chunks_list: "chunks_list wit_R = [wit_ch1, wit_ch2]"

text \<open>
  @{const clean_prefix_of} is a run-derived @{command definition}
  (@{thm clean_prefix_of_def}); for @{text wit_R} it is derived from
  the pinned accessors above rather than axiomatized on the run. The
  @{text wit_chunks_list} axiom pins @{term "chunks_list wit_R"} (an
  abstract accessor, constrained by @{thm chunks_list_set} /
  @{thm chunks_list_distinct} to a permutation of
  @{term "{wit_ch1, wit_ch2}"}) to one chunk enumeration, making the
  derived clean prefix a determinate computation.
\<close>

lemma wit_clean_prefix:
  "clean_prefix_of wit_R
     = [ Refresh (0::nat) (None::nat option) c0,
         Cdc c1_w (Insert 0 42),
         Cdc c2_w (Delete 1),
         Refresh 1 None c2_w ]"
proof -
  have d0: "sorted_list_of_set {0::nat} = [0]" by eval
  have d1: "sorted_list_of_set {Suc 0} = [Suc 0]" by eval
  have le12: "src_le c1_w c2_w"
    using c1_w_lt_c2_w by (simp add: src_lt_def)
  have le02: "src_le c0 c2_w"
    using c0_le_c1_w le12 src_le_trans by blast
  have n10: "\<not> src_le c1_w c0"
    using c0_le_c1_w c0_neq_c1_w src_le_antisym by blast
  have n20: "\<not> src_le c2_w c0"
    using le02 c0_neq_c2_w src_le_antisym by blast
  have n21: "\<not> src_le c2_w c1_w"
    using le12 c1_w_neq_c2_w src_le_antisym by blast
  show ?thesis
    unfolding clean_prefix_of_def canonical_clean_prefix_def
              cdc_event_replays_def chunk_read_refreshes_def
    by (simp add: wit_chunks_list wit_dom_1 wit_dom_2
                  wit_read_coord_1 wit_read_coord_2
                  wit_chunk_read_result_1_0
                  wit_chunk_read_result_2_1[unfolded One_nat_def]
                  wit_cdc_events wit_scope wit_frontier d0 d1 One_nat_def
                  List.map_filter_simps sort_key_def
                  c0_le_c1_w[unfolded src_le_eq_less_eq]
                  le02[unfolded src_le_eq_less_eq]
                  le12[unfolded src_le_eq_less_eq]
                  n10[unfolded src_le_eq_less_eq]
                  n20[unfolded src_le_eq_less_eq]
                  n21[unfolded src_le_eq_less_eq])
qed

subsection \<open>The seven witness clauses\<close>

text \<open>
  Each of the 7 clauses in the wellformed-run-positive-witness
  obligation is discharged below as a separate lemma. The proofs
  are direct unfoldings of the @{command axiomatization} above plus
  the @{const Apply} computation on the explicit clean-prefix list.
\<close>

lemma witness_clause_1_b0_nonempty: "b0_w \<noteq> Map.empty"
proof -
  have "b0_w 7 \<noteq> Map.empty 7" by (simp add: b0_w_def)
  thus ?thesis by metis
qed

lemma witness_clause_2_scope_nonempty: "scope_of wit_R \<noteq> {}"
  using wit_scope by simp

lemma witness_clause_3_two_chunks: "card (chunks wit_R) = 2"
  using wit_chunks_set wit_chunks_distinct by simp

lemma witness_clause_3_two_chunks_ge:
  "2 \<le> card (chunks wit_R)"
  using witness_clause_3_two_chunks by simp

lemma witness_clause_4_chunk_read_at_c0:
  "wit_ch1 \<in> chunks wit_R
   \<and> chunk_read_coordinate wit_R wit_ch1 = c0"
  using wit_chunks_set wit_read_coord_1 by simp

lemma witness_clause_5_post_chunk_read_cdc:
  "Cdc c1_w (Insert 0 42) \<in> set (clean_prefix_of wit_R)
   \<and> src_lt (chunk_read_coordinate wit_R wit_ch1) c1_w"
  using wit_clean_prefix wit_read_coord_1 c0_lt_c1_w by simp

lemma witness_clause_6_delete_event:
  "Cdc c2_w (Delete (1::nat)) \<in> set (clean_prefix_of wit_R)"
  using wit_clean_prefix by simp

lemma witness_clause_6_chunk_read_absence:
  "Refresh (0::nat) (None::nat option) c0
     \<in> set (clean_prefix_of wit_R)"
  using wit_clean_prefix by simp

text \<open>
  Auxiliary @{const Apply} computation on the witness clean prefix.
  The left-fold of @{const apply_step} over the explicit four-event
  list reduces by case analysis: the initial @{text "Refresh 0 None
  c0"} preserves the empty per-key state (it sets key 0 to @{term None},
  which is already @{term None}); the @{text "Cdc c1_w (Insert 0 42)"}
  sets key 0 to @{term "Some 42"}; the @{text "Cdc c2_w (Delete 1)"}
  sets key 1 to @{term None} (already @{term None}, no change); the
  final @{text "Refresh 1 None c2_w"} sets key 1 to @{term None}
  (no change). Net result: only key 0 carries @{term "Some 42"}.
\<close>

lemma apply_clean_prefix_witness:
  "Apply (clean_prefix_of wit_R)
     = (\<lambda>k. if k = (0::nat) then Some (42::nat) else None)"
proof -
  have "Apply (clean_prefix_of wit_R)
          = foldl apply_step (\<lambda>_. None)
              [ Refresh (0::nat) (None::nat option) c0,
                Cdc c1_w (Insert 0 42),
                Cdc c2_w (Delete 1),
                Refresh 1 None c2_w ]"
    unfolding Apply_def wit_clean_prefix by (rule refl)
  also have "\<dots> = (\<lambda>k. if k = (0::nat) then Some (42::nat) else None)"
    by (auto simp: fun_eq_iff fun_upd_def)
  finally show ?thesis .
qed

lemma witness_clause_7_apply_nonempty:
  "restrict (Apply (clean_prefix_of wit_R)) (scope_of wit_R)
     \<noteq> Map.empty"
proof
  assume H: "restrict (Apply (clean_prefix_of wit_R))
                       (scope_of wit_R)
              = Map.empty"
  hence "restrict (Apply (clean_prefix_of wit_R))
                  (scope_of wit_R) 0
           = Map.empty 0" by simp
  hence "(if (0::nat) \<in> scope_of wit_R
            then Apply (clean_prefix_of wit_R) 0
            else None) = None"
    unfolding restrict_def by simp
  moreover have "(0::nat) \<in> scope_of wit_R"
    using wit_scope by simp
  ultimately have "Apply (clean_prefix_of wit_R) 0 = None"
    by simp
  thus False
    using apply_clean_prefix_witness by simp
qed

lemma witness_clause_7_apply_differs_from_b0:
  "restrict (Apply (clean_prefix_of wit_R)) (scope_of wit_R)
     \<noteq> restrict b0_w (scope_of wit_R)"
proof
  assume H: "restrict (Apply (clean_prefix_of wit_R))
                       (scope_of wit_R)
              = restrict b0_w (scope_of wit_R)"
  hence "restrict (Apply (clean_prefix_of wit_R))
                  (scope_of wit_R) 0
           = restrict b0_w (scope_of wit_R) 0" by simp
  moreover have "(0::nat) \<in> scope_of wit_R"
    using wit_scope by simp
  ultimately have
    "Apply (clean_prefix_of wit_R) 0 = b0_w 0"
    unfolding restrict_def by simp
  thus False
    using apply_clean_prefix_witness
    unfolding b0_w_def by simp
qed

subsection \<open>Helper computation lemmas for the WF discharge\<close>

text \<open>
  Auxiliary facts about source-coordinate ordering and
  @{const Src} / @{const latest_src_event} on the witness data, used
  by the wellformed-run discharge below.
\<close>

lemma src_le_c0_c2_w: "src_le c0 c2_w"
  using c0_least by simp

lemma src_le_c1_w_c2_w: "src_le c1_w c2_w"
  using c1_w_lt_c2_w by (simp add: src_lt_def)

lemma not_src_le_c1_w_c0: "\<not> src_le c1_w c0"
  using c0_le_c1_w c0_neq_c1_w src_le_antisym by blast

lemma not_src_le_c2_w_c0: "\<not> src_le c2_w c0"
  using src_le_c0_c2_w c0_neq_c2_w src_le_antisym by blast

lemma not_src_lt_c2_w_c1_w: "\<not> src_lt c2_w c1_w"
proof
  assume H: "src_lt c2_w c1_w"
  hence "src_le c2_w c1_w" "c2_w \<noteq> c1_w" by (simp_all add: src_lt_def)
  with src_le_c1_w_c2_w have "c1_w = c2_w"
    using src_le_antisym by blast
  with \<open>c2_w \<noteq> c1_w\<close> show False by simp
qed

lemma not_src_lt_c2_w_c2_w: "\<not> src_lt c2_w c2_w"
  by (simp add: src_lt_def)

lemma length_H_w: "length H_w = 2"
  by (simp add: H_w_def)

lemma H_w_nth_0: "H_w ! 0 = (c1_w, Insert 0 42)"
  by (simp add: H_w_def)

lemma H_w_nth_1: "H_w ! 1 = (c2_w, Delete (1::nat))"
  by (simp add: H_w_def)

lemma set_H_w:
  "set H_w = {(c1_w, Insert 0 42), (c2_w, Delete (1::nat))}"
  by (simp add: H_w_def)

lemma latest_src_event_H_w_c0_0:
  "latest_src_event H_w c0 (0::nat) = None"
  unfolding latest_src_event_def
  using length_H_w H_w_nth_0 H_w_nth_1
        not_src_le_c1_w_c0 not_src_le_c2_w_c0
  by (simp add: numeral_2_eq_2)

lemma latest_src_event_H_w_c2_w_1:
  "latest_src_event H_w c2_w (1::nat) = Some 1"
  unfolding latest_src_event_def
  using length_H_w H_w_nth_0 H_w_nth_1
        src_le_c1_w_c2_w src_le_refl[where c=c2_w]
  by (simp add: numeral_2_eq_2)

lemma Src_b0_w_H_w_c0_0: "Src b0_w H_w c0 (0::nat) = None"
  unfolding Src_def using latest_src_event_H_w_c0_0
  by (simp add: b0_w_def)

lemma Src_b0_w_H_w_c2_w_1: "Src b0_w H_w c2_w (1::nat) = None"
  unfolding Src_def using latest_src_event_H_w_c2_w_1 H_w_nth_1
  by simp

subsection \<open>WF body discharge on the concrete witness\<close>

text \<open>
  The wellformed-run body is discharged on the witness instance
  @{text "(b0_w, wit_R, H_w)"} against the
  @{const wellformed_dblog_run} definition. Each of the conjuncts
  (WF0 sub-conjuncts + WF1 (a)..(g) + WF2 coverage + WF2 faithfulness
  + WF4 + WF5 + WF6 main + WF6 row-absence + WF7 forward + WF7
  reverse) is dischargeable by case analysis on the witness's
  axiomatized accessor values plus the helper computation lemmas
  above.
\<close>

lemma wf_h_w: "wellformed_src_history H_w"
  unfolding wellformed_src_history_def
  using length_H_w H_w_nth_0 H_w_nth_1
        src_le_c1_w_c2_w c0_neq_c1_w c0_neq_c2_w
        c1_w_lt_c2_w not_src_lt_c2_w_c1_w
  by (auto simp: source_pos_order_def numeral_2_eq_2
                 less_Suc_eq nth_Cons')

lemma chunks_wit_R_eq:
  "(ch \<in> chunks wit_R) \<longleftrightarrow> (ch = wit_ch1 \<or> ch = wit_ch2)"
  using wit_chunks_set by simp

lemma wf_witness_holds: "wellformed_dblog_run b0_w wit_R H_w"
  unfolding wellformed_dblog_run_def
proof (intro conjI)
  \<comment> \<open>WF0 part 1: source-history binding.\<close>
  show "src_history_of wit_R = H_w" by (rule wit_src_history)
next
  \<comment> \<open>WF0 part 2: source-history wellformedness.\<close>
  show "wellformed_src_history H_w" by (rule wf_h_w)
next
  \<comment> \<open>WF1 (a): unique responsible chunk per in-scope key.
       @{const owns} expands to set membership in @{const chunk_domain},
       so the @{text "wit_dom_1"} / @{text "wit_dom_2"} axioms
       discharge both the existence and uniqueness halves.\<close>
  show "\<forall>k\<in>scope_of wit_R. \<exists>!ch. ch \<in> chunks wit_R \<and> owns wit_R ch k"
  proof
    fix k :: nat
    assume "k \<in> scope_of wit_R"
    hence k_cases: "k = 0 \<or> k = 1" using wit_scope by simp
    show "\<exists>!ch. ch \<in> chunks wit_R \<and> owns wit_R ch k"
    proof (cases "k = 0")
      case True
      have "wit_ch1 \<in> chunks wit_R \<and> owns wit_R wit_ch1 k"
        using wit_chunks_set wit_dom_1 True by simp
      moreover have "\<And>ch. ch \<in> chunks wit_R \<and> owns wit_R ch k \<Longrightarrow> ch = wit_ch1"
        using chunks_wit_R_eq wit_dom_1 wit_dom_2 True by auto
      ultimately show ?thesis by blast
    next
      case False
      hence k1: "k = 1" using k_cases by simp
      have "wit_ch2 \<in> chunks wit_R \<and> owns wit_R wit_ch2 k"
        using wit_chunks_set wit_dom_2 k1 by simp
      moreover have "\<And>ch. ch \<in> chunks wit_R \<and> owns wit_R ch k \<Longrightarrow> ch = wit_ch2"
        using chunks_wit_R_eq wit_dom_1 wit_dom_2 k1 by auto
      ultimately show ?thesis by blast
    qed
  qed
next
  \<comment> \<open>WF1 (b): chunk domains pairwise disjoint.\<close>
  show "\<forall>ch1\<in>chunks wit_R. \<forall>ch2\<in>chunks wit_R.
          ch1 \<noteq> ch2 \<longrightarrow> chunk_domain wit_R ch1 \<inter> chunk_domain wit_R ch2 = {}"
    using chunks_wit_R_eq wit_dom_1 wit_dom_2 by auto
next
  \<comment> \<open>WF1 (c): canonical chunk-ownership domain equals scope.\<close>
  show "canonical_chunk_ownership_domain wit_R = scope_of wit_R"
    unfolding canonical_chunk_ownership_domain_def
    using wit_chunks_set wit_dom_1 wit_dom_2 wit_scope by auto
next
  \<comment> \<open>WF1 (d): responsible_chunk \<longleftrightarrow> ownership predicate (in scope).\<close>
  show "\<forall>k\<in>scope_of wit_R. \<forall>ch.
          responsible_chunk wit_R k = Some ch
            \<longleftrightarrow> ch \<in> chunks wit_R \<and> owns wit_R ch k"
  proof (intro ballI allI)
    fix k :: nat and ch :: "(nat, nat) chunk"
    assume "k \<in> scope_of wit_R"
    hence k_cases: "k = 0 \<or> k = 1" using wit_scope by simp
    show "responsible_chunk wit_R k = Some ch
            \<longleftrightarrow> ch \<in> chunks wit_R \<and> owns wit_R ch k"
    proof (cases "k = 0")
      case True
      then have rc: "responsible_chunk wit_R k = Some wit_ch1"
        using wit_resp_0 by simp
      show ?thesis
      proof
        assume "responsible_chunk wit_R k = Some ch"
        with rc have "ch = wit_ch1" by simp
        thus "ch \<in> chunks wit_R \<and> owns wit_R ch k"
          using wit_chunks_set wit_dom_1 True by simp
      next
        assume A: "ch \<in> chunks wit_R \<and> owns wit_R ch k"
        have "ch = wit_ch1"
          using A chunks_wit_R_eq wit_dom_1 wit_dom_2 True by auto
        with rc show "responsible_chunk wit_R k = Some ch" by simp
      qed
    next
      case False
      hence k1: "k = 1" using k_cases by simp
      then have rc: "responsible_chunk wit_R k = Some wit_ch2"
        using wit_resp_1 by simp
      show ?thesis
      proof
        assume "responsible_chunk wit_R k = Some ch"
        with rc have "ch = wit_ch2" by simp
        thus "ch \<in> chunks wit_R \<and> owns wit_R ch k"
          using wit_chunks_set wit_dom_2 k1 by simp
      next
        assume A: "ch \<in> chunks wit_R \<and> owns wit_R ch k"
        have "ch = wit_ch2"
          using A chunks_wit_R_eq wit_dom_1 wit_dom_2 k1 by auto
        with rc show "responsible_chunk wit_R k = Some ch" by simp
      qed
    qed
  qed
next
  \<comment> \<open>WF1 (e): out-of-scope keys have no responsible chunk.\<close>
  show "\<forall>k. k \<notin> scope_of wit_R \<longrightarrow> responsible_chunk wit_R k = None"
    using wit_scope wit_resp_else by auto
next
  \<comment> \<open>WF1 (f) part 1: scope is finite.\<close>
  show "finite (scope_of wit_R)" using wit_scope by simp
next
  \<comment> \<open>WF1 (f) part 2: chunk domains are finite.\<close>
  show "\<forall>ch\<in>chunks wit_R. finite (chunk_domain wit_R ch)"
    using chunks_wit_R_eq wit_dom_1 wit_dom_2 by auto
next
  \<comment> \<open>WF1 (g): every chunk has a non-empty domain.\<close>
  show "\<forall>ch\<in>chunks wit_R. chunk_domain wit_R ch \<noteq> {}"
    using chunks_wit_R_eq wit_dom_1 wit_dom_2 by auto
next
  \<comment> \<open>WF2 coverage: observed CDC reaches every in-scope key.\<close>
  show "\<forall>k\<in>scope_of wit_R. covers_ordinary_cdc wit_R k (frontier_of wit_R)"
  proof
    fix k :: nat assume "k \<in> scope_of wit_R"
    hence k_cases: "k = 0 \<or> k = 1" using wit_scope by simp
    show "covers_ordinary_cdc wit_R k (frontier_of wit_R)"
    proof (cases "k = 0")
      case True
      show ?thesis
        unfolding covers_ordinary_cdc_def
      proof (intro exI[where x = wit_ch1] conjI allI impI)
        show "responsible_chunk wit_R k = Some wit_ch1"
          using wit_resp_0 True by simp
      next
        fix i assume i_lt: "i < length (src_history_of wit_R)"
           and chunk_lt: "src_lt (chunk_read_coordinate wit_R wit_ch1)
                                  (hist_coord (src_history_of wit_R ! i))"
           and to_f: "src_le (hist_coord (src_history_of wit_R ! i))
                              (frontier_of wit_R)"
           and key_eq: "key_of (hist_event (src_history_of wit_R ! i)) = k"
        show "src_history_of wit_R ! i \<in> set (cdc_events_of wit_R)"
          using i_lt chunk_lt to_f key_eq True
                wit_src_history wit_cdc_events length_H_w
                H_w_nth_0 H_w_nth_1
          by (cases "i = 0"; cases "i = 1"; auto simp: numeral_2_eq_2 set_H_w)
      qed
    next
      case False
      hence k1: "k = 1" using k_cases by simp
      show ?thesis
        unfolding covers_ordinary_cdc_def
      proof (intro exI[where x = wit_ch2] conjI allI impI)
        show "responsible_chunk wit_R k = Some wit_ch2"
          using wit_resp_1 k1 by simp
      next
        fix i assume i_lt: "i < length (src_history_of wit_R)"
           and chunk_lt: "src_lt (chunk_read_coordinate wit_R wit_ch2)
                                  (hist_coord (src_history_of wit_R ! i))"
           and to_f: "src_le (hist_coord (src_history_of wit_R ! i))
                              (frontier_of wit_R)"
           and key_eq: "key_of (hist_event (src_history_of wit_R ! i)) = k"
        \<comment> \<open>chunk_lt premise is FALSE: chunk_read_coord wit_R wit_ch2 = c2_w
            and src_lt c2_w (H_w!i)'s coord is impossible.\<close>
        have False
          using i_lt chunk_lt
                wit_src_history wit_read_coord_2 length_H_w
                H_w_nth_0 H_w_nth_1
                not_src_lt_c2_w_c1_w not_src_lt_c2_w_c2_w
          by (cases "i = 0"; cases "i = 1"; auto simp: numeral_2_eq_2)
        thus "src_history_of wit_R ! i \<in> set (cdc_events_of wit_R)" ..
      qed
    qed
  qed
next
  \<comment> \<open>WF2 faithfulness: every in-scope, at-or-before-frontier
      observed CDC event appears in the source history --
      @{text cdc_events_of} is a subset of @{text src_history_of}
      (in fact equal here).\<close>
  show "\<forall>p\<in>set (cdc_events_of wit_R).
          key_of (hist_event p) \<in> scope_of wit_R
          \<and> src_le (hist_coord p) (frontier_of wit_R)
          \<longrightarrow> p \<in> set (src_history_of wit_R)"
    using wit_cdc_events wit_src_history set_H_w by auto
next
  \<comment> \<open>WF2 order-preserving sublist: on the
      in-scope/at-or-before-frontier slice, @{text cdc_events_of}
      wit_R is an order-preserving sublist of @{text src_history_of}
      wit_R. For this witness, @{text cdc_events_of} wit_R = H_w =
      @{text src_history_of} wit_R (the operator observed exactly
      all source events), so the in-scope slice on both sides is
      equal as a list and the identity function discharges the
      @{text strict_mono} \<iota> obligation trivially.\<close>
  show "\<exists>\<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
          \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of wit_R
                                   \<and> src_le (hist_coord p) (frontier_of wit_R));
                 cdc_in_slice  = filter in_slice (cdc_events_of wit_R);
                 hist_in_slice = filter in_slice (src_history_of wit_R)
             in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                    \<iota> i < length hist_in_slice
                  \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
  proof (intro exI[where x="\<lambda>n :: nat. n"] conjI)
    show "strict_mono (\<lambda>n :: nat. n)" by (simp add: strict_mono_def)
  next
    have eq: "cdc_events_of wit_R = src_history_of wit_R"
      using wit_cdc_events wit_src_history H_w_def by simp
    show "let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of wit_R
                                \<and> src_le (hist_coord p) (frontier_of wit_R));
              cdc_in_slice  = filter in_slice (cdc_events_of wit_R);
              hist_in_slice = filter in_slice (src_history_of wit_R)
          in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                 (\<lambda>n :: nat. n) i < length hist_in_slice
               \<and> cdc_in_slice ! i = hist_in_slice ! (\<lambda>n :: nat. n) i"
      using eq by (simp add: Let_def)
  qed
next
  \<comment> \<open>WF2 post-read same-key/same-coordinate multiplicity:
      @{text cdc_events_of} wit_R = @{text src_history_of} wit_R, so
      every filtered slice has identical multisets.\<close>
  show "\<forall>k\<in>scope_of wit_R. \<forall>ch c.
          responsible_chunk wit_R k = Some ch
          \<and> src_lt (chunk_read_coordinate wit_R ch) c
          \<and> src_le c (frontier_of wit_R)
          \<longrightarrow>
            mset (source_key_coord_slice k c (cdc_events_of wit_R))
            = mset (source_key_coord_slice k c (src_history_of wit_R))"
  proof (intro ballI allI impI)
    fix k :: nat and ch :: "(nat, nat) chunk" and c :: src_coord
    have eq: "cdc_events_of wit_R = src_history_of wit_R"
      using wit_cdc_events wit_src_history H_w_def by simp
    show "mset (source_key_coord_slice k c (cdc_events_of wit_R))
          = mset (source_key_coord_slice k c (src_history_of wit_R))"
      using eq by simp
  qed
next
  \<comment> \<open>WF4: chunk-read evidence (watermark + totality + Refresh agreement).\<close>
  show "\<forall>ch\<in>chunks wit_R.
          src_le (chunk_lower_watermark wit_R ch) (chunk_read_coordinate wit_R ch)
        \<and> src_le (chunk_read_coordinate wit_R ch) (chunk_upper_watermark wit_R ch)
        \<and> (\<forall>k\<in>chunk_domain wit_R ch. \<exists>m. chunk_read_result wit_R ch k = Some m)
        \<and> (\<forall>k\<in>chunk_domain wit_R ch. \<forall>m.
             chunk_read_result wit_R ch k = Some m
               \<longleftrightarrow> Refresh k m (chunk_read_coordinate wit_R ch)
                    \<in> set (clean_prefix_of wit_R))"
  proof
    fix ch :: "(nat, nat) chunk"
    assume ch_in: "ch \<in> chunks wit_R"
    hence ch_cases: "ch = wit_ch1 \<or> ch = wit_ch2"
      using chunks_wit_R_eq by simp
    show "src_le (chunk_lower_watermark wit_R ch) (chunk_read_coordinate wit_R ch)
        \<and> src_le (chunk_read_coordinate wit_R ch) (chunk_upper_watermark wit_R ch)
        \<and> (\<forall>k\<in>chunk_domain wit_R ch. \<exists>m. chunk_read_result wit_R ch k = Some m)
        \<and> (\<forall>k\<in>chunk_domain wit_R ch. \<forall>m.
             chunk_read_result wit_R ch k = Some m
               \<longleftrightarrow> Refresh k m (chunk_read_coordinate wit_R ch)
                    \<in> set (clean_prefix_of wit_R))"
    proof (cases "ch = wit_ch1")
      case True
      show ?thesis
        using True wit_lwm_1 wit_uwm_1 wit_read_coord_1 src_le_refl
              wit_dom_1 wit_chunk_read_result_1_0 wit_clean_prefix
        by auto
    next
      case False
      hence "ch = wit_ch2" using ch_cases by simp
      show ?thesis
        using \<open>ch = wit_ch2\<close> wit_lwm_2 wit_uwm_2 wit_read_coord_2 src_le_refl
              wit_dom_2 wit_chunk_read_result_2_1 wit_clean_prefix
              c0_neq_c2_w c1_w_neq_c2_w
        by auto
    qed
  qed
next
  \<comment> \<open>WF5: chunk-read coordinate at-or-before frontier.\<close>
  show "\<forall>ch\<in>chunks wit_R.
          src_le (chunk_read_coordinate wit_R ch) (frontier_of wit_R)"
    using chunks_wit_R_eq wit_read_coord_1 wit_read_coord_2 wit_frontier
          src_le_c0_c2_w src_le_refl
    by auto
next
  \<comment> \<open>WF6 main: refresh correctness against
       Src b0_w H_w (chunk-read coord).\<close>
  show "\<forall>ch\<in>chunks wit_R. \<forall>k\<in>chunk_domain wit_R ch. \<forall>m.
          chunk_read_result wit_R ch k = Some m
            \<longrightarrow> m = Src b0_w H_w (chunk_read_coordinate wit_R ch) k"
  proof
    fix ch :: "(nat, nat) chunk" assume ch_in: "ch \<in> chunks wit_R"
    hence ch_cases: "ch = wit_ch1 \<or> ch = wit_ch2"
      using chunks_wit_R_eq by simp
    show "\<forall>k\<in>chunk_domain wit_R ch. \<forall>m.
            chunk_read_result wit_R ch k = Some m
              \<longrightarrow> m = Src b0_w H_w (chunk_read_coordinate wit_R ch) k"
    proof (cases "ch = wit_ch1")
      case True
      show ?thesis
        using True wit_dom_1 wit_chunk_read_result_1_0
              wit_read_coord_1 Src_b0_w_H_w_c0_0
        by auto
    next
      case False
      hence "ch = wit_ch2" using ch_cases by simp
      show ?thesis
        using \<open>ch = wit_ch2\<close> wit_dom_2 wit_chunk_read_result_2_1
              wit_read_coord_2 Src_b0_w_H_w_c2_w_1
        by auto
    qed
  qed
next
  \<comment> \<open>WF6 row-absence: when @{text chunk_read_result} observed
       @{text "Some None"} for an in-domain key,
       @{text row_absence_meaningful} holds. Discharged via direct
       case analysis on @{text chunks_wit_R_eq} + the
       @{text "wit_dom_*"} axioms + the @{text Src} lemmas;
       @{text row_absence_meaningful_def} is unfolded inside each
       case so the @{text simp} call has a small, targeted goal.\<close>
  show "\<forall>ch\<in>chunks wit_R. \<forall>k\<in>chunk_domain wit_R ch.
          chunk_read_result wit_R ch k = Some None
            \<longrightarrow> row_absence_meaningful b0_w H_w wit_R ch k"
  proof (intro ballI impI)
    fix ch :: "(nat, nat) chunk" and k :: nat
    assume ch_in: "ch \<in> chunks wit_R"
       and k_in: "k \<in> chunk_domain wit_R ch"
       and crr: "chunk_read_result wit_R ch k = Some None"
    from ch_in chunks_wit_R_eq
      have ch_cases: "ch = wit_ch1 \<or> ch = wit_ch2" by simp
    show "row_absence_meaningful b0_w H_w wit_R ch k"
    proof (cases "ch = wit_ch1")
      case True
      with k_in wit_dom_1 have k0: "k = 0" by simp
      show ?thesis
        unfolding row_absence_meaningful_def
        using True k0 wit_dom_1 wit_read_coord_1 Src_b0_w_H_w_c0_0
        by simp
    next
      case False
      with ch_cases have ch_2: "ch = wit_ch2" by simp
      with k_in wit_dom_2 have k1: "k = 1" by simp
      show ?thesis
        unfolding row_absence_meaningful_def
        using ch_2 k1 wit_dom_2 wit_read_coord_2 Src_b0_w_H_w_c2_w_1
        by simp
    qed
  qed
next
  \<comment> \<open>WF7 forward (clean-prefix CDC coherence): every observed
       CDC event in scope and at-or-before frontier appears as a
       @{text Cdc} replay event in @{text "clean_prefix_of R"}.
       Witness data: @{text cdc_events_of} wit_R = @{text "[(c1_w,
       Insert 0 42), (c2_w, Delete 1)]"}, both @{text Cdc} events
       present in @{text clean_prefix_of} wit_R; the proof discharges
       the conclusion directly without evaluating the antecedent.\<close>
  show "\<forall>p \<in> set (cdc_events_of wit_R).
          key_of (hist_event p) \<in> scope_of wit_R
          \<and> src_le (hist_coord p) (frontier_of wit_R)
          \<longrightarrow> Cdc (hist_coord p) (hist_event p)
                \<in> set (clean_prefix_of wit_R)"
  proof (intro ballI impI)
    fix p :: "src_coord \<times> (nat, nat) source_event"
    assume p_in: "p \<in> set (cdc_events_of wit_R)"
    hence p_cases: "p = (c1_w, Insert 0 42) \<or> p = (c2_w, Delete 1)"
      using wit_cdc_events by simp
    show "Cdc (hist_coord p) (hist_event p)
            \<in> set (clean_prefix_of wit_R)"
      using p_cases wit_clean_prefix by fastforce
  qed
next
  \<comment> \<open>WF7 reverse (clean-prefix CDC coherence): every @{text Cdc}
       event in @{text "clean_prefix_of R"} in scope and
       at-or-before frontier has a witness in @{text "cdc_events_of
       R"}. The proof case-splits on the four elements of the
       explicit @{text clean_prefix_of} list; the two @{text Refresh}
       elements fail the @{text Cdc}-shape antecedent by datatype
       distinctness, the two @{text Cdc} elements have direct
       witnesses in @{text cdc_events_of}.\<close>
  show "\<forall>e c. Cdc c e \<in> set (clean_prefix_of wit_R)
                 \<and> key_of e \<in> scope_of wit_R
                 \<and> src_le c (frontier_of wit_R)
                 \<longrightarrow> (c, e) \<in> set (cdc_events_of wit_R)"
  proof (intro allI impI)
    fix e :: "(nat, nat) source_event" and c :: src_coord
    assume "Cdc c e \<in> set (clean_prefix_of wit_R)
              \<and> key_of e \<in> scope_of wit_R
              \<and> src_le c (frontier_of wit_R)"
    hence cdc_in: "Cdc c e \<in> set (clean_prefix_of wit_R)" by simp
    have list_eq: "Cdc c e \<in> set [Refresh (0::nat) (None::nat option) c0,
                                    Cdc c1_w (Insert 0 42),
                                    Cdc c2_w (Delete 1),
                                    Refresh 1 None c2_w]"
      using cdc_in wit_clean_prefix by simp
    hence "(c = c1_w \<and> e = Insert 0 42)
            \<or> (c = c2_w \<and> e = Delete 1)"
      by auto
    thus "(c, e) \<in> set (cdc_events_of wit_R)"
      using wit_cdc_events by auto
  qed
qed

subsection \<open>Witness existence theorem\<close>

text \<open>
  The witness existence theorem packages the seven paper-side
  clauses in existential form together with the
  @{const wellformed_dblog_run} predicate at the witness instance
  @{text "(b0_w, wit_R, H_w)"}. The WF body conjunct is discharged
  via @{thm wf_witness_holds} above; the existential theorem
  establishes Layer 1 non-vacuity.
\<close>

theorem wellformed_run_positive_witness:
  "\<exists> (b0 :: nat \<rightharpoonup> nat) (R :: (nat, nat) run)
      (H :: (nat, nat) src_history).
        wellformed_dblog_run b0 R H
      \<and> b0 \<noteq> Map.empty
      \<and> scope_of R \<noteq> {}
      \<and> 2 \<le> card (chunks R)
      \<and> (\<exists> ch \<in> chunks R. chunk_read_coordinate R ch = c0)
      \<and> (\<exists> ch \<in> chunks R. \<exists> c e.
              Cdc c e \<in> set (clean_prefix_of R)
            \<and> src_lt (chunk_read_coordinate R ch) c)
      \<and> ( (\<exists> c k. Cdc c (Delete k) \<in> set (clean_prefix_of R))
        \<or> (\<exists> k c. Refresh k None c \<in> set (clean_prefix_of R)) )
      \<and> restrict (Apply (clean_prefix_of R)) (scope_of R)
          \<noteq> Map.empty
      \<and> restrict (Apply (clean_prefix_of R)) (scope_of R)
          \<noteq> restrict b0 (scope_of R)"
proof (intro exI[where x = b0_w] exI[where x = wit_R] exI[where x = H_w]
             conjI)
  show "wellformed_dblog_run b0_w wit_R H_w" by (rule wf_witness_holds)
next
  show "b0_w \<noteq> Map.empty" by (rule witness_clause_1_b0_nonempty)
next
  show "scope_of wit_R \<noteq> {}" by (rule witness_clause_2_scope_nonempty)
next
  show "2 \<le> card (chunks wit_R)" by (rule witness_clause_3_two_chunks_ge)
next
  show "\<exists> ch \<in> chunks wit_R. chunk_read_coordinate wit_R ch = c0"
    using witness_clause_4_chunk_read_at_c0 by blast
next
  show "\<exists> ch \<in> chunks wit_R. \<exists> c e.
          Cdc c e \<in> set (clean_prefix_of wit_R)
        \<and> src_lt (chunk_read_coordinate wit_R ch) c"
    using witness_clause_5_post_chunk_read_cdc
          witness_clause_4_chunk_read_at_c0 by blast
next
  show "(\<exists> c k. Cdc c (Delete k) \<in> set (clean_prefix_of wit_R))
          \<or> (\<exists> k c. Refresh k None c
                     \<in> set (clean_prefix_of wit_R))"
    using witness_clause_6_delete_event by blast
next
  show "restrict (Apply (clean_prefix_of wit_R)) (scope_of wit_R)
          \<noteq> Map.empty"
    by (rule witness_clause_7_apply_nonempty)
next
  show "restrict (Apply (clean_prefix_of wit_R)) (scope_of wit_R)
          \<noteq> restrict b0_w (scope_of wit_R)"
    by (rule witness_clause_7_apply_differs_from_b0)
qed

end
