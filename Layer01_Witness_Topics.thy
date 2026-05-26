theory Layer01_Witness_Topics
  imports DBLog_Run
begin

text \<open>
  Layer 1 Topic 1 and Topic 2 positive witnesses.

  This theory exhibits two concrete positive witnesses for Layer 1:

    \<^item> Topic 1 positive witness (clean-prefix-carrier shape): a
      Layer 1 run with at least one chunk and one ordinary CDC event
      where wellformedness holds AND Lemma 1.1's conclusion is
      non-trivially true. It exercises the clean-prefix-carrier shape
      specifically -- distinct from the wellformed-run positive
      witness of theory @{text Layer01_Witnesses}, which exercises
      the full WF body without the Lemma 1.1 conclusion;
    \<^item> Topic 2 positive witness (multi-chunk partition shape): a
      wellformed run with at least two chunks partitioning a
      non-empty scope. It exercises the chunk-partition shape
      specifically.

  Construction approach. The Layer 1 run carrier @{typ "('k, 'v) run"}
  is a @{command typedecl} with no constructors, and the run accessors
  are @{command consts} with no defining axioms. Each witness uses an
  @{command axiomatization} block to introduce a fresh run constant
  (and one or two fresh chunk constants) with axiom equations fixing
  every accessor value the WF body or the Lemma 1.1 equality
  references. The axioms are fixture axioms over fresh constants:
  they assert no global property of the abstract Layer 1 vocabulary,
  which each witness leaves unconstrained on every other run / chunk.

  Choice of types. Both witnesses fix @{text "'k = nat"} and
  @{text "'v = nat"} -- concrete decidable types that let the WF body
  decompose to first-order computation. The two witnesses use disjoint
  key ranges so the per-witness narratives stay independent (Topic 1:
  key @{text 1}; Topic 2: keys @{text 10} and @{text 20}).

  Witness independence. The two witness blocks below introduce
  disjoint families of constants (@{text "t1_R / t1_ch / b0_t1 / H_t1
  / ct1"} and @{text "t2_R / t2_chA / t2_chB / b0_t2 / H_t2"}); they
  do not consume each other's data and can be read or audited in
  either order. Each existential theorem packages the corresponding
  paper-side obligation in @{text "\<exists>"} form against the witness
  instance.
\<close>

section \<open>Topic 1 positive witness (clean-prefix-carrier shape)\<close>

text \<open>
  Topic 1 obligation: a Layer 1 run with at least one chunk + one
  ordinary CDC event where wellformedness holds AND Lemma 1.1's
  conclusion is non-trivially true. The witness below uses the
  smallest data shape that exercises both aspects:

    \<^item> single source coordinate @{text ct1} above @{text c0}
      (so the witness has exactly one ordinary CDC event past the
      chunk-read coordinate);
    \<^item> single in-scope key (key @{text 1}; @{text "b0_t1 1 = Some 5"}
      so the chunk reads from a non-empty @{text b0});
    \<^item> single chunk @{text t1_ch} reading at @{text c0} (the chunk
      reads pre-history; chunk-read result is @{text "Some (Some 5)"}
      for key @{text 1}, matching @{text "Src(b0_t1, H_t1, c0) 1 =
      b0_t1 1 = Some 5"});
    \<^item> single source event @{text "Update 1 7"} at @{text ct1};
      frontier = @{text ct1};
    \<^item> clean prefix = @{text "[Refresh 1 (Some 5) c0,
      Cdc ct1 (Update 1 7)]"};
    \<^item> @{const Apply} on this clean prefix yields
      @{text "(1 \<mapsto> Some 7)"}; @{text "Src(b0_t1, H_t1, ct1) 1 = Some 7"}
      (the @{text Update}'s value); restricted to scope @{text "{1}"},
      both views agree (Lemma 1.1 conclusion holds), AND the result
      differs from @{text "b0_t1 \<restriction> {1} = (1 \<mapsto> Some 5)"}
      (the equality is non-trivial: the CDC event has effect).

  This shape is minimal: removing the source event leaves Lemma 1.1's
  conclusion holding only because both @{const Apply} and @{const Src}
  reduce to the chunk-read observation (the equality would still hold
  but trivially); removing the chunk leaves no clean-prefix carrier;
  removing the in-scope key leaves the equality trivially true on
  empty restriction.
\<close>

subsection \<open>Topic 1 source coordinate\<close>

axiomatization ct1 :: src_coord
  where c0_lt_ct1: "src_lt c0 ct1"

lemma c0_le_ct1: "src_le c0 ct1"
  using c0_lt_ct1 by (simp add: src_lt_def)

lemma c0_neq_ct1: "c0 \<noteq> ct1"
  using c0_lt_ct1 by (simp add: src_lt_def)

lemma not_src_le_ct1_c0: "\<not> src_le ct1 c0"
  using c0_le_ct1 c0_neq_ct1 src_le_antisym by blast

lemma src_le_ct1_ct1: "src_le ct1 ct1"
  by (rule src_le_refl)

subsection \<open>Topic 1 base state and source history\<close>

definition b0_t1 :: "nat \<rightharpoonup> nat" where
  "b0_t1 = (\<lambda>k. if k = 1 then Some 5 else None)"

definition H_t1 :: "(nat, nat) src_history" where
  "H_t1 = [(ct1, Update 1 7)]"

lemma length_H_t1: "length H_t1 = 1"
  by (simp add: H_t1_def)

lemma H_t1_nth_0: "H_t1 ! 0 = (ct1, Update 1 7)"
  by (simp add: H_t1_def)

lemma set_H_t1: "set H_t1 = {(ct1, Update 1 7)}"
  by (simp add: H_t1_def)

subsection \<open>Topic 1 run, chunk, and accessor values\<close>

text \<open>
  Single concrete run constant @{text t1_R} together with a single
  concrete chunk constant @{text t1_ch}; all Layer 1 accessor values
  are fixed by axiom. WF1 sub-clauses (a) (e) (responsible-chunk
  agreement on / off scope) are captured here via @{text t1_resp_1}
  + @{text t1_resp_else}.
\<close>

axiomatization
  t1_R  :: "(nat, nat) run" and
  t1_ch :: "(nat, nat) chunk"
where
  t1_scope:        "scope_of t1_R = {1}"
  and t1_frontier: "frontier_of t1_R = ct1"
  and t1_chunks_set: "chunks t1_R = {t1_ch}"
  and t1_dom:      "chunk_domain t1_R t1_ch = {1}"
  \<comment> \<open>No separate ownership axiom is needed: @{text "owns t1_R t1_ch 1"}
       follows from @{text t1_dom} via @{const owns} = set membership.\<close>
  and t1_resp_1:   "responsible_chunk t1_R 1 = Some t1_ch"
  and t1_resp_else: "k \<noteq> 1 \<Longrightarrow> responsible_chunk t1_R k = None"
  and t1_read_coord: "chunk_read_coordinate t1_R t1_ch = c0"
  and t1_lwm:      "chunk_lower_watermark t1_R t1_ch = c0"
  and t1_uwm:      "chunk_upper_watermark t1_R t1_ch = c0"
  and t1_src_history: "src_history_of t1_R = H_t1"
  and t1_chunk_read_result_1:
    "chunk_read_result t1_R t1_ch 1 = Some (Some 5)"
  and t1_cdc_events:
    "cdc_events_of t1_R = [(ct1, Update 1 7)]"

text \<open>
  @{const clean_prefix_of} is a run-derived @{command definition}
  (@{thm clean_prefix_of_def}); for @{text t1_R} it is derived from the
  pinned accessors above rather than axiomatized on the run. The single
  chunk fixes @{term "chunks_list t1_R"} up to @{thm chunks_list_set} /
  @{thm chunks_list_distinct}.
\<close>

lemma t1_chunks_list: "chunks_list t1_R = [t1_ch]"
proof -
  have s: "set (chunks_list t1_R) = {t1_ch}"
    using chunks_list_set[of t1_R] t1_chunks_set by simp
  have "length (chunks_list t1_R) = 1"
    using distinct_card[OF chunks_list_distinct[of t1_R]] s by simp
  with s show ?thesis
    by (cases "chunks_list t1_R") auto
qed

lemma t1_clean_prefix:
  "clean_prefix_of t1_R
     = [ Refresh (1::nat) (Some (5::nat)) c0,
         Cdc ct1 (Update 1 7) ]"
proof -
  have d1: "sorted_list_of_set {Suc 0} = [Suc 0]" by eval
  show ?thesis
    unfolding clean_prefix_of_def canonical_clean_prefix_def
              cdc_event_replays_def chunk_read_refreshes_def
    by (simp add: t1_chunks_list t1_dom t1_read_coord
                  t1_chunk_read_result_1[unfolded One_nat_def]
                  t1_cdc_events t1_scope t1_frontier d1 One_nat_def
                  List.map_filter_simps sort_key_def
                  c0_le_ct1[unfolded src_le_eq_less_eq]
                  not_src_le_ct1_c0[unfolded src_le_eq_less_eq])
qed

lemma chunks_t1_R_eq:
  "(ch \<in> chunks t1_R) \<longleftrightarrow> (ch = t1_ch)"
  using t1_chunks_set by simp

subsection \<open>Source-state computations on the Topic 1 instance\<close>

text \<open>
  @{const Src} reductions at the chunk-read coordinate @{text c0}
  (used by WF6) and at the frontier @{text ct1} (used by the Lemma
  1.1 conclusion). Each lemma reduces by @{const filter}-list
  computation over @{text "[0]"}.
\<close>

lemma upt_length_H_t1: "[0..<length H_t1] = [0]"
  by (simp add: length_H_t1)

lemma latest_src_event_H_t1_c0_1:
  "latest_src_event H_t1 c0 (1::nat) = None"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_t1 ! i)) c0
                \<and> key_of (hist_event (H_t1 ! i)) = (1::nat)"
  have "filter ?P [0] = []"
    using H_t1_nth_0 not_src_le_ct1_c0 by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_t1 by simp
qed

lemma latest_src_event_H_t1_ct1_1:
  "latest_src_event H_t1 ct1 (1::nat) = Some 0"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_t1 ! i)) ct1
                \<and> key_of (hist_event (H_t1 ! i)) = (1::nat)"
  have "filter ?P [0] = [0]"
    using H_t1_nth_0 src_le_ct1_ct1 by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_t1 by simp
qed

lemma Src_b0_t1_H_t1_c0_1: "Src b0_t1 H_t1 c0 (1::nat) = Some 5"
  unfolding Src_def using latest_src_event_H_t1_c0_1
  by (simp add: b0_t1_def)

lemma Src_b0_t1_H_t1_ct1_1: "Src b0_t1 H_t1 ct1 (1::nat) = Some 7"
  unfolding Src_def using latest_src_event_H_t1_ct1_1 H_t1_nth_0
  by simp

subsection \<open>Wellformedness of the Topic 1 source history\<close>

lemma wf_h_t1: "wellformed_src_history H_t1"
  unfolding wellformed_src_history_def
  using length_H_t1 H_t1_nth_0 c0_neq_ct1
  by (auto simp: source_pos_order_def)

subsection \<open>Apply on the Topic 1 clean prefix\<close>

text \<open>
  The two-event clean prefix reduces by left-fold:
  @{text "Refresh 1 (Some 5) c0"} sets key @{text 1} to
  @{term "Some (5::nat)"}; @{text "Cdc ct1 (Update 1 7)"} overrides
  key @{text 1} to @{term "Some (7::nat)"}; the net result is
  @{text "(1 \<mapsto> Some 7)"} on the empty starting map.
\<close>

lemma apply_clean_prefix_t1:
  "Apply (clean_prefix_of t1_R)
     = (\<lambda>k. if k = (1::nat) then Some (7::nat) else None)"
proof -
  have "Apply (clean_prefix_of t1_R)
          = foldl apply_step (\<lambda>_. None)
              [ Refresh (1::nat) (Some (5::nat)) c0,
                Cdc ct1 (Update 1 7) ]"
    unfolding Apply_def t1_clean_prefix by (rule refl)
  also have "\<dots> = (\<lambda>k. if k = (1::nat) then Some (7::nat) else None)"
    by (auto simp: fun_eq_iff fun_upd_def)
  finally show ?thesis .
qed

subsection \<open>Wellformedness of the Topic 1 run\<close>

text \<open>
  Discharge the wellformed-run body on the @{text "(b0_t1, t1_R,
  H_t1)"} instance by case analysis on the witness's axiomatized
  accessor values + the helper lemmas above. WF1 (b) is vacuous
  (single chunk); WF2 coverage exercises the single source event +
  single chunk path; WF6 reduces to the @{thm Src_b0_t1_H_t1_c0_1}
  computation.
\<close>

lemma t1_wellformed_dblog_run:
  "wellformed_dblog_run b0_t1 t1_R H_t1"
  unfolding wellformed_dblog_run_def
proof (intro conjI)
  \<comment> \<open>WF0 part 1.\<close>
  show "src_history_of t1_R = H_t1" by (rule t1_src_history)
next
  \<comment> \<open>WF0 part 2.\<close>
  show "wellformed_src_history H_t1" by (rule wf_h_t1)
next
  \<comment> \<open>WF1 (a): unique responsible chunk per in-scope key.
       The existence half cites @{text t1_dom} via @{const owns} =
       set membership.\<close>
  show "\<forall>k\<in>scope_of t1_R. \<exists>!ch. ch \<in> chunks t1_R \<and> owns t1_R ch k"
  proof
    fix k :: nat assume "k \<in> scope_of t1_R"
    hence k1: "k = 1" using t1_scope by simp
    show "\<exists>!ch. ch \<in> chunks t1_R \<and> owns t1_R ch k"
    proof
      show "t1_ch \<in> chunks t1_R \<and> owns t1_R t1_ch k"
        using t1_chunks_set t1_dom k1 by simp
    next
      fix ch assume "ch \<in> chunks t1_R \<and> owns t1_R ch k"
      thus "ch = t1_ch" using chunks_t1_R_eq by blast
    qed
  qed
next
  \<comment> \<open>WF1 (b): chunk domains pairwise disjoint -- vacuous on single chunk.\<close>
  show "\<forall>ch1\<in>chunks t1_R. \<forall>ch2\<in>chunks t1_R.
          ch1 \<noteq> ch2 \<longrightarrow> chunk_domain t1_R ch1 \<inter> chunk_domain t1_R ch2 = {}"
    using chunks_t1_R_eq by auto
next
  \<comment> \<open>WF1 (c): canonical chunk-ownership domain equals scope.\<close>
  show "canonical_chunk_ownership_domain t1_R = scope_of t1_R"
    unfolding canonical_chunk_ownership_domain_def
    using t1_chunks_set t1_dom t1_scope by auto
next
  \<comment> \<open>WF1 (d): responsible_chunk \<longleftrightarrow> ownership predicate.\<close>
  show "\<forall>k\<in>scope_of t1_R. \<forall>ch.
          responsible_chunk t1_R k = Some ch
            \<longleftrightarrow> ch \<in> chunks t1_R \<and> owns t1_R ch k"
  proof (intro ballI allI)
    fix k :: nat and ch :: "(nat, nat) chunk"
    assume "k \<in> scope_of t1_R"
    hence k1: "k = 1" using t1_scope by simp
    show "responsible_chunk t1_R k = Some ch
            \<longleftrightarrow> ch \<in> chunks t1_R \<and> owns t1_R ch k"
    proof
      assume "responsible_chunk t1_R k = Some ch"
      with t1_resp_1 k1 have "ch = t1_ch" by simp
      thus "ch \<in> chunks t1_R \<and> owns t1_R ch k"
        using t1_chunks_set t1_dom k1 by simp
    next
      assume A: "ch \<in> chunks t1_R \<and> owns t1_R ch k"
      have "ch = t1_ch" using A chunks_t1_R_eq by blast
      with t1_resp_1 k1 show "responsible_chunk t1_R k = Some ch" by simp
    qed
  qed
next
  \<comment> \<open>WF1 (e): out-of-scope keys have no responsible chunk.\<close>
  show "\<forall>k. k \<notin> scope_of t1_R \<longrightarrow> responsible_chunk t1_R k = None"
    using t1_scope t1_resp_else by auto
next
  \<comment> \<open>WF1 (f) part 1.\<close>
  show "finite (scope_of t1_R)" using t1_scope by simp
next
  \<comment> \<open>WF1 (f) part 2.\<close>
  show "\<forall>ch\<in>chunks t1_R. finite (chunk_domain t1_R ch)"
    using chunks_t1_R_eq t1_dom by auto
next
  \<comment> \<open>WF1 (g): every chunk has a non-empty domain.\<close>
  show "\<forall>ch\<in>chunks t1_R. chunk_domain t1_R ch \<noteq> {}"
    using chunks_t1_R_eq t1_dom by auto
next
  \<comment> \<open>WF2 coverage.\<close>
  show "\<forall>k\<in>scope_of t1_R. covers_ordinary_cdc t1_R k (frontier_of t1_R)"
  proof
    fix k :: nat assume "k \<in> scope_of t1_R"
    hence k1: "k = 1" using t1_scope by simp
    show "covers_ordinary_cdc t1_R k (frontier_of t1_R)"
      unfolding covers_ordinary_cdc_def
    proof (intro exI[where x = t1_ch] conjI allI impI)
      show "responsible_chunk t1_R k = Some t1_ch"
        using t1_resp_1 k1 by simp
    next
      fix i assume i_lt: "i < length (src_history_of t1_R)"
        and chunk_lt: "src_lt (chunk_read_coordinate t1_R t1_ch)
                              (hist_coord (src_history_of t1_R ! i))"
        and to_f: "src_le (hist_coord (src_history_of t1_R ! i))
                          (frontier_of t1_R)"
        and key_eq: "key_of (hist_event (src_history_of t1_R ! i)) = k"
      \<comment> \<open>i = 0 (only valid index).\<close>
      have i0: "i = 0"
        using i_lt t1_src_history length_H_t1 by simp
      show "src_history_of t1_R ! i \<in> set (cdc_events_of t1_R)"
        using i0 t1_src_history t1_cdc_events H_t1_nth_0
        by (simp add: H_t1_def)
    qed
  qed
next
  \<comment> \<open>WF2 faithfulness.\<close>
  show "\<forall>p\<in>set (cdc_events_of t1_R).
          key_of (hist_event p) \<in> scope_of t1_R
          \<and> src_le (hist_coord p) (frontier_of t1_R)
          \<longrightarrow> p \<in> set (src_history_of t1_R)"
    using t1_cdc_events t1_src_history set_H_t1 H_t1_def by auto
next
  \<comment> \<open>WF2 order-preserving sublist: for Topic 1,
      @{text cdc_events_of} t1_R = @{text src_history_of} t1_R = H_t1
      (single source event), so the identity function discharges
      the @{text strict_mono} \<iota> obligation trivially.\<close>
  show "\<exists>\<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
          \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of t1_R
                                   \<and> src_le (hist_coord p) (frontier_of t1_R));
                 cdc_in_slice  = filter in_slice (cdc_events_of t1_R);
                 hist_in_slice = filter in_slice (src_history_of t1_R)
             in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                    \<iota> i < length hist_in_slice
                  \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
  proof (intro exI[where x="\<lambda>n :: nat. n"] conjI)
    show "strict_mono (\<lambda>n :: nat. n)" by (simp add: strict_mono_def)
  next
    have eq: "cdc_events_of t1_R = src_history_of t1_R"
      using t1_cdc_events t1_src_history H_t1_def by simp
    show "let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of t1_R
                                \<and> src_le (hist_coord p) (frontier_of t1_R));
              cdc_in_slice  = filter in_slice (cdc_events_of t1_R);
              hist_in_slice = filter in_slice (src_history_of t1_R)
          in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                 (\<lambda>n :: nat. n) i < length hist_in_slice
               \<and> cdc_in_slice ! i = hist_in_slice ! (\<lambda>n :: nat. n) i"
      using eq by (simp add: Let_def)
  qed
next
  \<comment> \<open>WF2 post-read same-key/same-coordinate multiplicity:
      @{text cdc_events_of} t1_R = @{text src_history_of} t1_R, so
      every filtered slice has identical multisets.\<close>
  show "\<forall>k\<in>scope_of t1_R. \<forall>ch c.
          responsible_chunk t1_R k = Some ch
          \<and> src_lt (chunk_read_coordinate t1_R ch) c
          \<and> src_le c (frontier_of t1_R)
          \<longrightarrow>
            mset (source_key_coord_slice k c (cdc_events_of t1_R))
            = mset (source_key_coord_slice k c (src_history_of t1_R))"
  proof (intro ballI allI impI)
    fix k :: nat and ch :: "(nat, nat) chunk" and c :: src_coord
    have eq: "cdc_events_of t1_R = src_history_of t1_R"
      using t1_cdc_events t1_src_history H_t1_def by simp
    show "mset (source_key_coord_slice k c (cdc_events_of t1_R))
          = mset (source_key_coord_slice k c (src_history_of t1_R))"
      using eq by simp
  qed
next
  \<comment> \<open>WF4: chunk-read evidence.\<close>
  show "\<forall>ch\<in>chunks t1_R.
          src_le (chunk_lower_watermark t1_R ch) (chunk_read_coordinate t1_R ch)
        \<and> src_le (chunk_read_coordinate t1_R ch) (chunk_upper_watermark t1_R ch)
        \<and> (\<forall>k\<in>chunk_domain t1_R ch. \<exists>m. chunk_read_result t1_R ch k = Some m)
        \<and> (\<forall>k\<in>chunk_domain t1_R ch. \<forall>m.
             chunk_read_result t1_R ch k = Some m
               \<longleftrightarrow> Refresh k m (chunk_read_coordinate t1_R ch)
                    \<in> set (clean_prefix_of t1_R))"
  proof
    fix ch :: "(nat, nat) chunk" assume "ch \<in> chunks t1_R"
    hence ch_eq: "ch = t1_ch" using chunks_t1_R_eq by simp
    show "src_le (chunk_lower_watermark t1_R ch) (chunk_read_coordinate t1_R ch)
        \<and> src_le (chunk_read_coordinate t1_R ch) (chunk_upper_watermark t1_R ch)
        \<and> (\<forall>k\<in>chunk_domain t1_R ch. \<exists>m. chunk_read_result t1_R ch k = Some m)
        \<and> (\<forall>k\<in>chunk_domain t1_R ch. \<forall>m.
             chunk_read_result t1_R ch k = Some m
               \<longleftrightarrow> Refresh k m (chunk_read_coordinate t1_R ch)
                    \<in> set (clean_prefix_of t1_R))"
      using ch_eq t1_lwm t1_uwm t1_read_coord src_le_refl
            t1_dom t1_chunk_read_result_1 t1_clean_prefix
      by auto
  qed
next
  \<comment> \<open>WF5: chunk-read coordinate at-or-before frontier.\<close>
  show "\<forall>ch\<in>chunks t1_R.
          src_le (chunk_read_coordinate t1_R ch) (frontier_of t1_R)"
    using chunks_t1_R_eq t1_read_coord t1_frontier c0_le_ct1 by auto
next
  \<comment> \<open>WF6 main: refresh correctness against Src.\<close>
  show "\<forall>ch\<in>chunks t1_R. \<forall>k\<in>chunk_domain t1_R ch. \<forall>m.
          chunk_read_result t1_R ch k = Some m
            \<longrightarrow> m = Src b0_t1 H_t1 (chunk_read_coordinate t1_R ch) k"
  proof
    fix ch :: "(nat, nat) chunk" assume "ch \<in> chunks t1_R"
    hence ch_eq: "ch = t1_ch" using chunks_t1_R_eq by simp
    show "\<forall>k\<in>chunk_domain t1_R ch. \<forall>m.
            chunk_read_result t1_R ch k = Some m
              \<longrightarrow> m = Src b0_t1 H_t1 (chunk_read_coordinate t1_R ch) k"
      using ch_eq t1_dom t1_chunk_read_result_1 t1_read_coord
            Src_b0_t1_H_t1_c0_1
      by auto
  qed
next
  \<comment> \<open>WF6 row-absence: vacuously true on t1_R -- the only
       in-domain key (key 1 of t1_ch) has @{text chunk_read_result}
       = @{text "Some (Some 5)"}, not @{text "Some None"}.\<close>
  show "\<forall>ch\<in>chunks t1_R. \<forall>k\<in>chunk_domain t1_R ch.
          chunk_read_result t1_R ch k = Some None
            \<longrightarrow> row_absence_meaningful b0_t1 H_t1 t1_R ch k"
  proof (intro ballI impI)
    fix ch :: "(nat, nat) chunk" and k :: nat
    assume ch_in: "ch \<in> chunks t1_R"
       and k_in: "k \<in> chunk_domain t1_R ch"
       and crr: "chunk_read_result t1_R ch k = Some None"
    from ch_in chunks_t1_R_eq have ch_eq: "ch = t1_ch" by simp
    with k_in t1_dom have k1: "k = 1" by simp
    from ch_eq k1 crr t1_chunk_read_result_1 have False by simp
    thus "row_absence_meaningful b0_t1 H_t1 t1_R ch k" ..
  qed
next
  \<comment> \<open>WF7 forward: single observed CDC event @{text "(ct1, Update
       1 7)"}; its @{text Cdc} form is in @{text clean_prefix_of}
       t1_R.\<close>
  show "\<forall>p \<in> set (cdc_events_of t1_R).
          key_of (hist_event p) \<in> scope_of t1_R
          \<and> src_le (hist_coord p) (frontier_of t1_R)
          \<longrightarrow> Cdc (hist_coord p) (hist_event p)
                \<in> set (clean_prefix_of t1_R)"
  proof (intro ballI impI)
    fix p :: "src_coord \<times> (nat, nat) source_event"
    assume p_in: "p \<in> set (cdc_events_of t1_R)"
    hence "p = (ct1, Update 1 7)" using t1_cdc_events by simp
    thus "Cdc (hist_coord p) (hist_event p)
            \<in> set (clean_prefix_of t1_R)"
      using t1_clean_prefix by simp
  qed
next
  \<comment> \<open>WF7 reverse: the only @{text Cdc} in @{text clean_prefix_of}
       t1_R is @{text "Cdc ct1 (Update 1 7)"}.\<close>
  show "\<forall>e c. Cdc c e \<in> set (clean_prefix_of t1_R)
                 \<and> key_of e \<in> scope_of t1_R
                 \<and> src_le c (frontier_of t1_R)
                 \<longrightarrow> (c, e) \<in> set (cdc_events_of t1_R)"
  proof (intro allI impI)
    fix e :: "(nat, nat) source_event" and c :: src_coord
    assume "Cdc c e \<in> set (clean_prefix_of t1_R)
              \<and> key_of e \<in> scope_of t1_R
              \<and> src_le c (frontier_of t1_R)"
    hence cdc_in: "Cdc c e \<in> set (clean_prefix_of t1_R)" by simp
    have "Cdc c e \<in> set [Refresh (1::nat) (Some (5::nat)) c0,
                          Cdc ct1 (Update 1 7)]"
      using cdc_in t1_clean_prefix by simp
    hence "c = ct1 \<and> e = Update 1 7" by auto
    thus "(c, e) \<in> set (cdc_events_of t1_R)"
      using t1_cdc_events by simp
  qed
qed

subsection \<open>Topic 1 Lemma 1.1 conclusion (non-trivial)\<close>

text \<open>
  The Topic 1 obligation requires Lemma 1.1's conclusion to hold
  AND to be non-trivial. The first lemma below states the equality
  on the chosen scope; the second lemma states the non-triviality
  (the result differs from @{text b0_t1} on scope, witnessing that
  the CDC event's effect propagates through the clean prefix).
\<close>

lemma t1_virtual_cut_holds:
  "restrict (Apply (clean_prefix_of t1_R)) (scope_of t1_R)
     = restrict (Src b0_t1 H_t1 (frontier_of t1_R)) (scope_of t1_R)"
proof
  fix k :: nat
  show "restrict (Apply (clean_prefix_of t1_R)) (scope_of t1_R) k
          = restrict (Src b0_t1 H_t1 (frontier_of t1_R)) (scope_of t1_R) k"
  proof (cases "k \<in> scope_of t1_R")
    case True
    hence k1: "k = 1" using t1_scope by simp
    then show ?thesis
      unfolding restrict_def
      using \<open>k \<in> scope_of t1_R\<close>
            apply_clean_prefix_t1
            Src_b0_t1_H_t1_ct1_1
            t1_frontier
      by simp
  next
    case False
    show ?thesis
      unfolding restrict_def using False by simp
  qed
qed

lemma t1_virtual_cut_non_trivial:
  "restrict (Apply (clean_prefix_of t1_R)) (scope_of t1_R)
     \<noteq> restrict b0_t1 (scope_of t1_R)"
proof
  assume H: "restrict (Apply (clean_prefix_of t1_R)) (scope_of t1_R)
              = restrict b0_t1 (scope_of t1_R)"
  hence "restrict (Apply (clean_prefix_of t1_R)) (scope_of t1_R) 1
           = restrict b0_t1 (scope_of t1_R) 1" by simp
  moreover have "(1::nat) \<in> scope_of t1_R" using t1_scope by simp
  ultimately have "Apply (clean_prefix_of t1_R) 1 = b0_t1 1"
    unfolding restrict_def by simp
  thus False
    using apply_clean_prefix_t1 unfolding b0_t1_def by simp
qed

subsection \<open>Topic 1 existential witness theorem\<close>

text \<open>
  Existential package: there exists a Layer 1 instance @{text "(b0,
  R, H)"} such that @{const wellformed_dblog_run} holds, the run
  has at least one chunk, the clean prefix carries at least one
  ordinary CDC event, the Lemma 1.1 conclusion holds, AND the
  conclusion is non-trivial (Apply on scope differs from
  @{text b0} on scope).
\<close>

theorem topic1_positive_witness:
  "\<exists> (b0 :: nat \<rightharpoonup> nat) (R :: (nat, nat) run)
      (H :: (nat, nat) src_history).
        wellformed_dblog_run b0 R H
      \<and> chunks R \<noteq> {}
      \<and> (\<exists> c e. Cdc c e \<in> set (clean_prefix_of R))
      \<and> restrict (Apply (clean_prefix_of R)) (scope_of R)
          = restrict (Src b0 H (frontier_of R)) (scope_of R)
      \<and> restrict (Apply (clean_prefix_of R)) (scope_of R)
          \<noteq> restrict b0 (scope_of R)"
proof (intro exI[where x = b0_t1] exI[where x = t1_R] exI[where x = H_t1]
             conjI)
  show "wellformed_dblog_run b0_t1 t1_R H_t1"
    by (rule t1_wellformed_dblog_run)
next
  show "chunks t1_R \<noteq> {}" using t1_chunks_set by simp
next
  show "\<exists> c e. Cdc c e \<in> set (clean_prefix_of t1_R)"
    using t1_clean_prefix by auto
next
  show "restrict (Apply (clean_prefix_of t1_R)) (scope_of t1_R)
          = restrict (Src b0_t1 H_t1 (frontier_of t1_R)) (scope_of t1_R)"
    by (rule t1_virtual_cut_holds)
next
  show "restrict (Apply (clean_prefix_of t1_R)) (scope_of t1_R)
          \<noteq> restrict b0_t1 (scope_of t1_R)"
    by (rule t1_virtual_cut_non_trivial)
qed

section \<open>Topic 2 positive witness (multi-chunk partition shape)\<close>

text \<open>
  Topic 2 obligation: a wellformed run with at least two chunks
  partitioning a non-empty scope. The witness below uses the
  smallest data shape that exercises the multi-chunk partition:

    \<^item> two in-scope keys (key @{text 10} and key @{text 20});
      @{text "b0_t2 10 = Some 100"}, @{text "b0_t2 20 = Some 200"};
    \<^item> two chunks @{text t2_chA} (owns @{text 10}) and
      @{text t2_chB} (owns @{text 20}); strict partition;
    \<^item> empty source history (no source events past @{text c0}); both
      chunks read at @{text c0}; @{text "frontier = c0"};
    \<^item> chunk-read results match @{text b0_t2} (Src at @{text c0}
      reduces to @{text b0_t2} on a wellformed history per WF-H2);
    \<^item> clean prefix = @{text "[Refresh 10 (Some 100) c0,
      Refresh 20 (Some 200) c0]"};
    \<^item> @{const Apply} on the clean prefix yields
      @{text "(10 \<mapsto> Some 100, 20 \<mapsto> Some 200)"}.

  This shape is minimal for the multi-chunk partition obligation:
  empty history avoids any source-event ordering reasoning; the two
  chunks each own one in-scope key with disjoint domains and union
  equal to scope; wellformedness reduces to per-chunk axiomatized
  values without any non-trivial @{const latest_src_event} cases.
\<close>

subsection \<open>Topic 2 base state and source history\<close>

definition b0_t2 :: "nat \<rightharpoonup> nat" where
  "b0_t2 = (\<lambda>k. if k = 10 then Some 100
                else if k = 20 then Some 200 else None)"

definition H_t2 :: "(nat, nat) src_history" where
  "H_t2 = []"

lemma length_H_t2: "length H_t2 = 0" by (simp add: H_t2_def)

lemma set_H_t2: "set H_t2 = {}" by (simp add: H_t2_def)

subsection \<open>Topic 2 run, chunks, and accessor values\<close>

text \<open>
  Single concrete run constant @{text t2_R} together with two
  concrete chunk constants @{text t2_chA} / @{text t2_chB}; all
  Layer 1 accessor values are fixed by axiom. The two chunks
  partition the scope @{text "{10, 20}"} with disjoint domains
  @{text "{10}"} and @{text "{20}"}.
\<close>

axiomatization
  t2_R   :: "(nat, nat) run" and
  t2_chA :: "(nat, nat) chunk" and
  t2_chB :: "(nat, nat) chunk"
where
  t2_chunks_distinct: "t2_chA \<noteq> t2_chB"
  and t2_scope:       "scope_of t2_R = {10, 20}"
  and t2_frontier:    "frontier_of t2_R = c0"
  and t2_chunks_set:  "chunks t2_R = {t2_chA, t2_chB}"
  and t2_dom_A:       "chunk_domain t2_R t2_chA = {10}"
  and t2_dom_B:       "chunk_domain t2_R t2_chB = {20}"
  \<comment> \<open>No separate ownership axioms are needed: @{const owns} is an
       @{command abbreviation} over @{text chunk_domain}, so each
       ownership statement is a set-membership fact already implied
       by @{text t2_dom_A} or @{text t2_dom_B}; the WF1 (a) + (d)
       discharge proofs cite the @{text "t2_dom_*"} axioms via
       @{text simp} / @{text auto}.\<close>
  and t2_resp_10:     "responsible_chunk t2_R 10 = Some t2_chA"
  and t2_resp_20:     "responsible_chunk t2_R 20 = Some t2_chB"
  and t2_resp_else:   "k \<noteq> 10 \<Longrightarrow> k \<noteq> 20
                          \<Longrightarrow> responsible_chunk t2_R k = None"
  and t2_read_coord_A: "chunk_read_coordinate t2_R t2_chA = c0"
  and t2_read_coord_B: "chunk_read_coordinate t2_R t2_chB = c0"
  and t2_lwm_A:       "chunk_lower_watermark t2_R t2_chA = c0"
  and t2_uwm_A:       "chunk_upper_watermark t2_R t2_chA = c0"
  and t2_lwm_B:       "chunk_lower_watermark t2_R t2_chB = c0"
  and t2_uwm_B:       "chunk_upper_watermark t2_R t2_chB = c0"
  and t2_src_history: "src_history_of t2_R = H_t2"
  and t2_chunk_read_result_A_10:
    "chunk_read_result t2_R t2_chA 10 = Some (Some 100)"
  and t2_chunk_read_result_B_20:
    "chunk_read_result t2_R t2_chB 20 = Some (Some 200)"
  and t2_cdc_events:  "cdc_events_of t2_R = []"
  and t2_chunks_list: "chunks_list t2_R = [t2_chA, t2_chB]"

text \<open>
  @{const clean_prefix_of} is a run-derived @{command definition}
  (@{thm clean_prefix_of_def}); for @{text t2_R} it is derived rather
  than axiomatized. The two chunks are read at the same coordinate
  @{text c0}, so the chunk enumeration order is the only thing that
  fixes the order of the two @{const Refresh} events; the
  @{text t2_chunks_list} axiom above pins @{term "chunks_list t2_R"}
  (an abstract accessor, constrained by @{thm chunks_list_set} /
  @{thm chunks_list_distinct} to a permutation of @{term "{t2_chA, t2_chB}"})
  to one enumeration, making the derived clean prefix determinate.
\<close>

lemma t2_clean_prefix:
  "clean_prefix_of t2_R
     = [ Refresh (10::nat) (Some (100::nat)) c0,
         Refresh 20 (Some 200) c0 ]"
proof -
  have dA: "sorted_list_of_set {10::nat} = [10]" by eval
  have dB: "sorted_list_of_set {20::nat} = [20]" by eval
  show ?thesis
    unfolding clean_prefix_of_def canonical_clean_prefix_def
              cdc_event_replays_def chunk_read_refreshes_def
    by (simp add: t2_chunks_list t2_dom_A t2_dom_B
                  t2_read_coord_A t2_read_coord_B
                  t2_chunk_read_result_A_10 t2_chunk_read_result_B_20
                  t2_cdc_events t2_scope t2_frontier dA dB
                  List.map_filter_simps sort_key_def)
qed

lemma chunks_t2_R_eq:
  "(ch \<in> chunks t2_R) \<longleftrightarrow> (ch = t2_chA \<or> ch = t2_chB)"
  using t2_chunks_set by simp

subsection \<open>Source-state computations on the Topic 2 instance\<close>

text \<open>
  @{const Src} reductions at @{text c0} on the empty history. Since
  @{text "H_t2 = []"}, @{const latest_src_event} returns @{term None}
  for every key, and @{const Src} therefore returns @{text b0_t2} on
  every key.
\<close>

lemma latest_src_event_H_t2_c0_any:
  "latest_src_event H_t2 c0 (k :: nat) = None"
  unfolding latest_src_event_def by (simp add: H_t2_def)

lemma Src_b0_t2_H_t2_c0_10: "Src b0_t2 H_t2 c0 (10::nat) = Some 100"
  unfolding Src_def using latest_src_event_H_t2_c0_any
  by (simp add: b0_t2_def)

lemma Src_b0_t2_H_t2_c0_20: "Src b0_t2 H_t2 c0 (20::nat) = Some 200"
  unfolding Src_def using latest_src_event_H_t2_c0_any
  by (simp add: b0_t2_def)

subsection \<open>Wellformedness of the Topic 2 source history\<close>

lemma wf_h_t2: "wellformed_src_history H_t2"
  unfolding wellformed_src_history_def by (simp add: H_t2_def)

subsection \<open>Apply on the Topic 2 clean prefix\<close>

text \<open>
  Two-event clean prefix; both events are @{text Refresh}; left-fold
  reduces by sequential @{text fun_upd}.
\<close>

lemma apply_clean_prefix_t2:
  "Apply (clean_prefix_of t2_R)
     = (\<lambda>k. if k = (10::nat) then Some (100::nat)
            else if k = 20 then Some 200 else None)"
proof -
  have "Apply (clean_prefix_of t2_R)
          = foldl apply_step (\<lambda>_. None)
              [ Refresh (10::nat) (Some (100::nat)) c0,
                Refresh 20 (Some 200) c0 ]"
    unfolding Apply_def t2_clean_prefix by (rule refl)
  also have "\<dots> = (\<lambda>k. if k = (10::nat) then Some (100::nat)
                       else if k = 20 then Some 200 else None)"
    by (auto simp: fun_eq_iff fun_upd_def)
  finally show ?thesis .
qed

subsection \<open>Wellformedness of the Topic 2 run\<close>

text \<open>
  Discharge the wellformed-run body on the @{text "(b0_t2, t2_R,
  H_t2)"} instance. WF1 (a)..(g) exercise the multi-chunk partition
  bookkeeping; WF2 coverage and faithfulness reduce to vacuity over
  the empty source history; WF4 + WF5 + WF6 reduce to the chunk-read
  axiom equations + the @{thm Src_b0_t2_H_t2_c0_10} / @{thm
  Src_b0_t2_H_t2_c0_20} computations.
\<close>

lemma t2_wellformed_dblog_run:
  "wellformed_dblog_run b0_t2 t2_R H_t2"
  unfolding wellformed_dblog_run_def
proof (intro conjI)
  \<comment> \<open>WF0 part 1.\<close>
  show "src_history_of t2_R = H_t2" by (rule t2_src_history)
next
  \<comment> \<open>WF0 part 2.\<close>
  show "wellformed_src_history H_t2" by (rule wf_h_t2)
next
  \<comment> \<open>WF1 (a): unique responsible chunk per in-scope key.
       @{const owns} expands to set membership in @{const chunk_domain};
       @{text t2_dom_A} / @{text t2_dom_B} discharge both halves.\<close>
  show "\<forall>k\<in>scope_of t2_R. \<exists>!ch. ch \<in> chunks t2_R \<and> owns t2_R ch k"
  proof
    fix k :: nat assume "k \<in> scope_of t2_R"
    hence k_cases: "k = 10 \<or> k = 20" using t2_scope by simp
    show "\<exists>!ch. ch \<in> chunks t2_R \<and> owns t2_R ch k"
    proof (cases "k = 10")
      case True
      have "t2_chA \<in> chunks t2_R \<and> owns t2_R t2_chA k"
        using t2_chunks_set t2_dom_A True by simp
      moreover have "\<And>ch. ch \<in> chunks t2_R \<and> owns t2_R ch k \<Longrightarrow> ch = t2_chA"
        using chunks_t2_R_eq t2_dom_A t2_dom_B True by auto
      ultimately show ?thesis by blast
    next
      case False
      hence k20: "k = 20" using k_cases by simp
      have "t2_chB \<in> chunks t2_R \<and> owns t2_R t2_chB k"
        using t2_chunks_set t2_dom_B k20 by simp
      moreover have "\<And>ch. ch \<in> chunks t2_R \<and> owns t2_R ch k \<Longrightarrow> ch = t2_chB"
        using chunks_t2_R_eq t2_dom_A t2_dom_B k20 by auto
      ultimately show ?thesis by blast
    qed
  qed
next
  \<comment> \<open>WF1 (b): chunk domains pairwise disjoint.\<close>
  show "\<forall>ch1\<in>chunks t2_R. \<forall>ch2\<in>chunks t2_R.
          ch1 \<noteq> ch2 \<longrightarrow> chunk_domain t2_R ch1 \<inter> chunk_domain t2_R ch2 = {}"
    using chunks_t2_R_eq t2_dom_A t2_dom_B by auto
next
  \<comment> \<open>WF1 (c): canonical chunk-ownership domain equals scope.\<close>
  show "canonical_chunk_ownership_domain t2_R = scope_of t2_R"
    unfolding canonical_chunk_ownership_domain_def
    using t2_chunks_set t2_dom_A t2_dom_B t2_scope by auto
next
  \<comment> \<open>WF1 (d): responsible_chunk \<longleftrightarrow> ownership predicate.\<close>
  show "\<forall>k\<in>scope_of t2_R. \<forall>ch.
          responsible_chunk t2_R k = Some ch
            \<longleftrightarrow> ch \<in> chunks t2_R \<and> owns t2_R ch k"
  proof (intro ballI allI)
    fix k :: nat and ch :: "(nat, nat) chunk"
    assume "k \<in> scope_of t2_R"
    hence k_cases: "k = 10 \<or> k = 20" using t2_scope by simp
    show "responsible_chunk t2_R k = Some ch
            \<longleftrightarrow> ch \<in> chunks t2_R \<and> owns t2_R ch k"
    proof (cases "k = 10")
      case True
      then have rc: "responsible_chunk t2_R k = Some t2_chA"
        using t2_resp_10 by simp
      show ?thesis
      proof
        assume "responsible_chunk t2_R k = Some ch"
        with rc have "ch = t2_chA" by simp
        thus "ch \<in> chunks t2_R \<and> owns t2_R ch k"
          using t2_chunks_set t2_dom_A True by simp
      next
        assume A: "ch \<in> chunks t2_R \<and> owns t2_R ch k"
        have "ch = t2_chA"
          using A chunks_t2_R_eq t2_dom_A t2_dom_B True by auto
        with rc show "responsible_chunk t2_R k = Some ch" by simp
      qed
    next
      case False
      hence k20: "k = 20" using k_cases by simp
      then have rc: "responsible_chunk t2_R k = Some t2_chB"
        using t2_resp_20 by simp
      show ?thesis
      proof
        assume "responsible_chunk t2_R k = Some ch"
        with rc have "ch = t2_chB" by simp
        thus "ch \<in> chunks t2_R \<and> owns t2_R ch k"
          using t2_chunks_set t2_dom_B k20 by simp
      next
        assume A: "ch \<in> chunks t2_R \<and> owns t2_R ch k"
        have "ch = t2_chB"
          using A chunks_t2_R_eq t2_dom_A t2_dom_B k20 by auto
        with rc show "responsible_chunk t2_R k = Some ch" by simp
      qed
    qed
  qed
next
  \<comment> \<open>WF1 (e): out-of-scope keys have no responsible chunk.\<close>
  show "\<forall>k. k \<notin> scope_of t2_R \<longrightarrow> responsible_chunk t2_R k = None"
    using t2_scope t2_resp_else by auto
next
  \<comment> \<open>WF1 (f) part 1.\<close>
  show "finite (scope_of t2_R)" using t2_scope by simp
next
  \<comment> \<open>WF1 (f) part 2.\<close>
  show "\<forall>ch\<in>chunks t2_R. finite (chunk_domain t2_R ch)"
    using chunks_t2_R_eq t2_dom_A t2_dom_B by auto
next
  \<comment> \<open>WF1 (g): every chunk has a non-empty domain.\<close>
  show "\<forall>ch\<in>chunks t2_R. chunk_domain t2_R ch \<noteq> {}"
    using chunks_t2_R_eq t2_dom_A t2_dom_B by auto
next
  \<comment> \<open>WF2 coverage: vacuous on empty source history.\<close>
  show "\<forall>k\<in>scope_of t2_R. covers_ordinary_cdc t2_R k (frontier_of t2_R)"
  proof
    fix k :: nat assume "k \<in> scope_of t2_R"
    hence k_cases: "k = 10 \<or> k = 20" using t2_scope by simp
    show "covers_ordinary_cdc t2_R k (frontier_of t2_R)"
    proof (cases "k = 10")
      case True
      show ?thesis
        unfolding covers_ordinary_cdc_def
      proof (intro exI[where x = t2_chA] conjI allI impI)
        show "responsible_chunk t2_R k = Some t2_chA"
          using t2_resp_10 True by simp
      next
        fix i assume "i < length (src_history_of t2_R)"
        with t2_src_history length_H_t2 have False by simp
        thus "src_history_of t2_R ! i \<in> set (cdc_events_of t2_R)" ..
      qed
    next
      case False
      hence k20: "k = 20" using k_cases by simp
      show ?thesis
        unfolding covers_ordinary_cdc_def
      proof (intro exI[where x = t2_chB] conjI allI impI)
        show "responsible_chunk t2_R k = Some t2_chB"
          using t2_resp_20 k20 by simp
      next
        fix i assume "i < length (src_history_of t2_R)"
        with t2_src_history length_H_t2 have False by simp
        thus "src_history_of t2_R ! i \<in> set (cdc_events_of t2_R)" ..
      qed
    qed
  qed
next
  \<comment> \<open>WF2 faithfulness: vacuous on empty @{text cdc_events_of}.\<close>
  show "\<forall>p\<in>set (cdc_events_of t2_R).
          key_of (hist_event p) \<in> scope_of t2_R
          \<and> src_le (hist_coord p) (frontier_of t2_R)
          \<longrightarrow> p \<in> set (src_history_of t2_R)"
    using t2_cdc_events by simp
next
  \<comment> \<open>WF2 order-preserving sublist: for Topic 2,
      @{text cdc_events_of} t2_R = @{text "[]"} (empty source
      history; no observed events), so the in-scope
      @{text cdc_in_slice} filter produces an empty list and the
      universal quantifier over @{text "i < length cdc_in_slice"}
      is vacuously true. The identity function discharges the
      @{text strict_mono} \<iota> obligation trivially.\<close>
  show "\<exists>\<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
          \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of t2_R
                                   \<and> src_le (hist_coord p) (frontier_of t2_R));
                 cdc_in_slice  = filter in_slice (cdc_events_of t2_R);
                 hist_in_slice = filter in_slice (src_history_of t2_R)
             in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                    \<iota> i < length hist_in_slice
                  \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
  proof (intro exI[where x="\<lambda>n :: nat. n"] conjI)
    show "strict_mono (\<lambda>n :: nat. n)" by (simp add: strict_mono_def)
  next
    show "let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of t2_R
                                \<and> src_le (hist_coord p) (frontier_of t2_R));
              cdc_in_slice  = filter in_slice (cdc_events_of t2_R);
              hist_in_slice = filter in_slice (src_history_of t2_R)
          in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                 (\<lambda>n :: nat. n) i < length hist_in_slice
               \<and> cdc_in_slice ! i = hist_in_slice ! (\<lambda>n :: nat. n) i"
      using t2_cdc_events by (simp add: Let_def)
  qed
next
  \<comment> \<open>WF2 post-read same-key/same-coordinate multiplicity:
      Topic 2 has empty source history and empty observed CDC list,
      so every filtered slice is empty on both sides.\<close>
  show "\<forall>k\<in>scope_of t2_R. \<forall>ch c.
          responsible_chunk t2_R k = Some ch
          \<and> src_lt (chunk_read_coordinate t2_R ch) c
          \<and> src_le c (frontier_of t2_R)
          \<longrightarrow>
            mset (source_key_coord_slice k c (cdc_events_of t2_R))
            = mset (source_key_coord_slice k c (src_history_of t2_R))"
    using t2_cdc_events t2_src_history H_t2_def
    by (simp add: source_key_coord_slice_def)
next
  \<comment> \<open>WF4: chunk-read evidence (per chunk).\<close>
  show "\<forall>ch\<in>chunks t2_R.
          src_le (chunk_lower_watermark t2_R ch) (chunk_read_coordinate t2_R ch)
        \<and> src_le (chunk_read_coordinate t2_R ch) (chunk_upper_watermark t2_R ch)
        \<and> (\<forall>k\<in>chunk_domain t2_R ch. \<exists>m. chunk_read_result t2_R ch k = Some m)
        \<and> (\<forall>k\<in>chunk_domain t2_R ch. \<forall>m.
             chunk_read_result t2_R ch k = Some m
               \<longleftrightarrow> Refresh k m (chunk_read_coordinate t2_R ch)
                    \<in> set (clean_prefix_of t2_R))"
  proof
    fix ch :: "(nat, nat) chunk" assume "ch \<in> chunks t2_R"
    hence ch_cases: "ch = t2_chA \<or> ch = t2_chB"
      using chunks_t2_R_eq by simp
    show "src_le (chunk_lower_watermark t2_R ch) (chunk_read_coordinate t2_R ch)
        \<and> src_le (chunk_read_coordinate t2_R ch) (chunk_upper_watermark t2_R ch)
        \<and> (\<forall>k\<in>chunk_domain t2_R ch. \<exists>m. chunk_read_result t2_R ch k = Some m)
        \<and> (\<forall>k\<in>chunk_domain t2_R ch. \<forall>m.
             chunk_read_result t2_R ch k = Some m
               \<longleftrightarrow> Refresh k m (chunk_read_coordinate t2_R ch)
                    \<in> set (clean_prefix_of t2_R))"
    proof (cases "ch = t2_chA")
      case True
      show ?thesis
        using True t2_lwm_A t2_uwm_A t2_read_coord_A src_le_refl
              t2_dom_A t2_chunk_read_result_A_10 t2_clean_prefix
        by auto
    next
      case False
      hence "ch = t2_chB" using ch_cases by simp
      show ?thesis
        using \<open>ch = t2_chB\<close> t2_lwm_B t2_uwm_B t2_read_coord_B src_le_refl
              t2_dom_B t2_chunk_read_result_B_20 t2_clean_prefix
        by auto
    qed
  qed
next
  \<comment> \<open>WF5: chunk-read coordinate at-or-before frontier.\<close>
  show "\<forall>ch\<in>chunks t2_R.
          src_le (chunk_read_coordinate t2_R ch) (frontier_of t2_R)"
    using chunks_t2_R_eq t2_read_coord_A t2_read_coord_B
          t2_frontier src_le_refl
    by auto
next
  \<comment> \<open>WF6 main: refresh correctness against Src.\<close>
  show "\<forall>ch\<in>chunks t2_R. \<forall>k\<in>chunk_domain t2_R ch. \<forall>m.
          chunk_read_result t2_R ch k = Some m
            \<longrightarrow> m = Src b0_t2 H_t2 (chunk_read_coordinate t2_R ch) k"
  proof
    fix ch :: "(nat, nat) chunk" assume "ch \<in> chunks t2_R"
    hence ch_cases: "ch = t2_chA \<or> ch = t2_chB"
      using chunks_t2_R_eq by simp
    show "\<forall>k\<in>chunk_domain t2_R ch. \<forall>m.
            chunk_read_result t2_R ch k = Some m
              \<longrightarrow> m = Src b0_t2 H_t2 (chunk_read_coordinate t2_R ch) k"
    proof (cases "ch = t2_chA")
      case True
      show ?thesis
        using True t2_dom_A t2_chunk_read_result_A_10
              t2_read_coord_A Src_b0_t2_H_t2_c0_10
        by auto
    next
      case False
      hence "ch = t2_chB" using ch_cases by simp
      show ?thesis
        using \<open>ch = t2_chB\<close> t2_dom_B t2_chunk_read_result_B_20
              t2_read_coord_B Src_b0_t2_H_t2_c0_20
        by auto
    qed
  qed
next
  \<comment> \<open>WF6 row-absence: vacuously true on t2_R -- the in-domain
       keys (10 of t2_chA, 20 of t2_chB) have @{text chunk_read_result}
       = @{text "Some (Some 100)"} and @{text "Some (Some 200)"}
       respectively.\<close>
  show "\<forall>ch\<in>chunks t2_R. \<forall>k\<in>chunk_domain t2_R ch.
          chunk_read_result t2_R ch k = Some None
            \<longrightarrow> row_absence_meaningful b0_t2 H_t2 t2_R ch k"
  proof (intro ballI impI)
    fix ch :: "(nat, nat) chunk" and k :: nat
    assume ch_in: "ch \<in> chunks t2_R"
       and k_in: "k \<in> chunk_domain t2_R ch"
       and crr: "chunk_read_result t2_R ch k = Some None"
    from ch_in chunks_t2_R_eq
      have ch_cases: "ch = t2_chA \<or> ch = t2_chB" by simp
    have False
    proof (cases "ch = t2_chA")
      case True
      with k_in t2_dom_A have "k = 10" by simp
      with True crr t2_chunk_read_result_A_10 show False by simp
    next
      case False
      with ch_cases have ch_B: "ch = t2_chB" by simp
      with k_in t2_dom_B have "k = 20" by simp
      with ch_B crr t2_chunk_read_result_B_20 show False by simp
    qed
    thus "row_absence_meaningful b0_t2 H_t2 t2_R ch k" ..
  qed
next
  \<comment> \<open>WF7 forward: @{text cdc_events_of} t2_R = @{text "[]"};
       vacuous over the empty set.\<close>
  show "\<forall>p \<in> set (cdc_events_of t2_R).
          key_of (hist_event p) \<in> scope_of t2_R
          \<and> src_le (hist_coord p) (frontier_of t2_R)
          \<longrightarrow> Cdc (hist_coord p) (hist_event p)
                \<in> set (clean_prefix_of t2_R)"
  proof (intro ballI impI)
    fix p :: "src_coord \<times> (nat, nat) source_event"
    assume "p \<in> set (cdc_events_of t2_R)"
    with t2_cdc_events have False by simp
    thus "Cdc (hist_coord p) (hist_event p)
            \<in> set (clean_prefix_of t2_R)" ..
  qed
next
  \<comment> \<open>WF7 reverse: @{text clean_prefix_of} t2_R contains only
       @{text Refresh} events; vacuous antecedent.\<close>
  show "\<forall>e c. Cdc c e \<in> set (clean_prefix_of t2_R)
                 \<and> key_of e \<in> scope_of t2_R
                 \<and> src_le c (frontier_of t2_R)
                 \<longrightarrow> (c, e) \<in> set (cdc_events_of t2_R)"
  proof (intro allI impI)
    fix e :: "(nat, nat) source_event" and c :: src_coord
    assume "Cdc c e \<in> set (clean_prefix_of t2_R)
              \<and> key_of e \<in> scope_of t2_R
              \<and> src_le c (frontier_of t2_R)"
    hence cdc_in: "Cdc c e \<in> set (clean_prefix_of t2_R)" by simp
    have "Cdc c e \<in> set [Refresh (10::nat) (Some (100::nat)) c0,
                          Refresh 20 (Some 200) c0]"
      using cdc_in t2_clean_prefix by simp
    hence False by simp
    thus "(c, e) \<in> set (cdc_events_of t2_R)" ..
  qed
qed

subsection \<open>Topic 2 multi-chunk partition properties\<close>

text \<open>
  The Topic 2 obligation requires "at least two chunks partitioning a
  non-empty scope". The lemmas below name the multi-chunk partition
  properties explicitly (non-empty scope; @{text "\<ge> 2"} chunks;
  pairwise-disjoint chunk domains; canonical-chunk-ownership-domain
  equals scope) so the existential theorem can carry them as
  conjuncts. WF1 (b) + WF1 (c) already cover disjointness and union
  inside the WF body; the lemmas here re-expose them at the top
  level for clarity.
\<close>

lemma t2_card_chunks: "card (chunks t2_R) = 2"
  using t2_chunks_set t2_chunks_distinct by simp

lemma t2_card_chunks_ge: "2 \<le> card (chunks t2_R)"
  using t2_card_chunks by simp

lemma t2_scope_nonempty: "scope_of t2_R \<noteq> {}"
  using t2_scope by simp

lemma t2_chunk_domains_disjoint:
  "\<forall>ch1 \<in> chunks t2_R. \<forall>ch2 \<in> chunks t2_R.
     ch1 \<noteq> ch2 \<longrightarrow> chunk_domain t2_R ch1 \<inter> chunk_domain t2_R ch2 = {}"
  using chunks_t2_R_eq t2_dom_A t2_dom_B by auto

lemma t2_canonical_partition_eq_scope:
  "canonical_chunk_ownership_domain t2_R = scope_of t2_R"
  unfolding canonical_chunk_ownership_domain_def
  using t2_chunks_set t2_dom_A t2_dom_B t2_scope by auto

subsection \<open>Topic 2 existential witness theorem\<close>

text \<open>
  Existential package: there exists a Layer 1 instance @{text "(b0,
  R, H)"} such that @{const wellformed_dblog_run} holds, the run has
  at least two chunks, the scope is non-empty, the chunk domains are
  pairwise disjoint, and the canonical-chunk-ownership domain equals
  the scope.
\<close>

theorem topic2_positive_witness:
  "\<exists> (b0 :: nat \<rightharpoonup> nat) (R :: (nat, nat) run)
      (H :: (nat, nat) src_history).
        wellformed_dblog_run b0 R H
      \<and> scope_of R \<noteq> {}
      \<and> 2 \<le> card (chunks R)
      \<and> (\<forall> ch1 \<in> chunks R. \<forall> ch2 \<in> chunks R.
            ch1 \<noteq> ch2 \<longrightarrow> chunk_domain R ch1 \<inter> chunk_domain R ch2 = {})
      \<and> canonical_chunk_ownership_domain R = scope_of R"
proof (intro exI[where x = b0_t2] exI[where x = t2_R] exI[where x = H_t2]
             conjI)
  show "wellformed_dblog_run b0_t2 t2_R H_t2"
    by (rule t2_wellformed_dblog_run)
next
  show "scope_of t2_R \<noteq> {}" by (rule t2_scope_nonempty)
next
  show "2 \<le> card (chunks t2_R)" by (rule t2_card_chunks_ge)
next
  show "\<forall> ch1 \<in> chunks t2_R. \<forall> ch2 \<in> chunks t2_R.
          ch1 \<noteq> ch2 \<longrightarrow> chunk_domain t2_R ch1 \<inter> chunk_domain t2_R ch2 = {}"
    by (rule t2_chunk_domains_disjoint)
next
  show "canonical_chunk_ownership_domain t2_R = scope_of t2_R"
    by (rule t2_canonical_partition_eq_scope)
qed

end
