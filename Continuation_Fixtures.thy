theory Continuation_Fixtures
  imports Continuation Layer01_Virtual_Cut_Example
begin

text \<open>
  Fixture bundle for the continuation extension.

  This theory exercises the continuation-extension theorems of
  @{theory DBLog_Virtual_Cuts.Continuation} on concrete data.
  It opens with the \<^emph>\<open>positive continuation witness\<close>: a nonempty
  continuation that pre-empts the empty-scope vacuity --- on a
  nonempty key scope, with nonempty continuation segments, the
  continuation theorem reaches the source state at a later frontier.
  The witness reuses the running example's source history
  @{const H_ex} and its source coordinates @{text "ec1 \<dots> ec4"}, so
  no new source-history-carrier axioms are introduced here.

  The continuation is built bottom-up through the proved theorems,
  not by recomputing @{const Src}: the empty replay is a virtual cut
  at the base coordinate @{const c0} (@{text l7_vc0}); the first
  segment continues it to @{text ec2} (@{text virtual_cut_state_continuation});
  the second segment continues that to @{text ec4}; and
  @{text cdc_segment_between_concat} certifies the concatenated
  segment as the single continuation segment for @{text "(c0, ec4]"}.

  Every conclusion is a source-side @{const Apply}-against-@{const Src}
  equality; nothing here is a destination, delivery, or sink claim.
\<close>

section \<open>Source state at the base coordinate\<close>

text \<open>
  On a wellformed source history the source state at the base
  coordinate @{const c0} is the base state itself. WF-H2 forbids any
  event at @{const c0}, and @{const c0} is the least source
  coordinate (@{thm c0_least}), so no event lies at or before
  @{const c0}: @{const latest_src_event} is @{const None} for every
  key. This is the base case the positive witness continues from ---
  it lets the witness avoid recomputing @{const Src} at a non-base
  frontier.
\<close>

lemma Src_at_base:
  assumes wfH: "wellformed_src_history H"
  shows "Src b0 H c0 = b0"
proof (rule ext)
  fix k
  have no_event_at_c0:
    "\<not> src_le (hist_coord (H ! i)) c0" if i_lt: "i < length H" for i
  proof
    assume "src_le (hist_coord (H ! i)) c0"
    moreover have "src_le c0 (hist_coord (H ! i))" by (rule c0_least)
    ultimately have "hist_coord (H ! i) = c0" by (rule src_le_antisym)
    moreover have "hist_coord (H ! i) \<noteq> c0"
      using wfH i_lt unfolding wellformed_src_history_def by blast
    ultimately show False by simp
  qed
  have "filter (\<lambda>i. src_le (hist_coord (H ! i)) c0
                     \<and> key_of (hist_event (H ! i)) = k) [0..<length H] = []"
    by (auto simp: filter_empty_conv no_event_at_c0)
  hence "latest_src_event H c0 k = None"
    unfolding latest_src_event_def by (simp add: Let_def)
  thus "Src b0 H c0 k = b0 k"
    unfolding Src_def by simp
qed

section \<open>Source coordinate order facts (reader-facing \<open>\<le>\<close> / \<open><\<close> form)\<close>

text \<open>
  The continuation-segment filter compares source coordinates with
  the @{class linorder} operators @{text \<open>\<le>\<close>} / @{text \<open><\<close>}; the
  running example states its chain with @{const src_lt}. These
  lemmas re-express the chain @{text "c0 < ec1 < ec2 < ec3 < ec4"}
  in @{text \<open>\<le>\<close>} / @{text \<open><\<close>} form, with the few derived and
  negated facts the segment computations of @{text l7_seg1} /
  @{text l7_seg2} need.
\<close>

lemma l7_c0_lt_ec1: "c0 < ec1" using c0_lt_ec1 by (simp add: src_lt_eq_less)
lemma l7_ec1_lt_ec2: "ec1 < ec2" using ec1_lt_ec2 by (simp add: src_lt_eq_less)
lemma l7_ec2_lt_ec3: "ec2 < ec3" using ec2_lt_ec3 by (simp add: src_lt_eq_less)
lemma l7_ec3_lt_ec4: "ec3 < ec4" using ec3_lt_ec4 by (simp add: src_lt_eq_less)

lemma l7_c0_lt_ec2: "c0 < ec2" using l7_c0_lt_ec1 l7_ec1_lt_ec2 by (rule less_trans)
lemma l7_c0_lt_ec3: "c0 < ec3" using l7_c0_lt_ec2 l7_ec2_lt_ec3 by (rule less_trans)
lemma l7_c0_lt_ec4: "c0 < ec4" using l7_c0_lt_ec3 l7_ec3_lt_ec4 by (rule less_trans)
lemma l7_ec2_lt_ec4: "ec2 < ec4" using l7_ec2_lt_ec3 l7_ec3_lt_ec4 by (rule less_trans)

lemma l7_c0_le_ec2: "c0 \<le> ec2" using l7_c0_lt_ec2 by (rule less_imp_le)
lemma l7_ec1_le_ec2: "ec1 \<le> ec2" using l7_ec1_lt_ec2 by (rule less_imp_le)
lemma l7_ec2_le_ec4: "ec2 \<le> ec4" using l7_ec2_lt_ec4 by (rule less_imp_le)
lemma l7_ec3_le_ec4: "ec3 \<le> ec4" using l7_ec3_lt_ec4 by (rule less_imp_le)

lemma l7_not_ec3_le_ec2: "\<not> ec3 \<le> ec2" using l7_ec2_lt_ec3 by (simp add: not_le)
lemma l7_not_ec4_le_ec2: "\<not> ec4 \<le> ec2" using l7_ec2_lt_ec4 by (simp add: not_le)
lemma l7_not_ec2_lt_ec1: "\<not> ec2 < ec1" using l7_ec1_le_ec2 by (simp add: not_less)

section \<open>The positive continuation witness\<close>

text \<open>
  The witness key scope: the three in-scope keys of the running
  example. Nonempty, so the continuation conclusion is not the
  empty-scope vacuity.
\<close>

abbreviation l7_scope :: "nat set" where
  "l7_scope \<equiv> {100, 200, 300}"

text \<open>
  The two continuation segments. @{text l7_seg1} is the in-scope
  CDC segment for @{text "(c0, ec2]"} --- the running example's two
  events at @{text ec1} / @{text ec2}, lifted to CDC events;
  @{text l7_seg2} is the in-scope segment for @{text "(ec2, ec4]"}
  --- the events at @{text ec3} / @{text ec4}.
\<close>

definition l7_seg1 :: "(nat, nat) replay_event list" where
  "l7_seg1 = [Cdc ec1 (Update 100 3000), Cdc ec2 (Insert 300 2500)]"

definition l7_seg2 :: "(nat, nat) replay_event list" where
  "l7_seg2 = [Cdc ec3 (Update 200 12000), Cdc ec4 (Update 300 3500)]"

text \<open>
  Each segment satisfies @{const cdc_segment_between}: it is exactly
  the source history @{const H_ex} filtered to its half-open
  coordinate interval and key scope, then CDC-lifted.
\<close>

lemma l7_seg1_segment:
  "cdc_segment_between H_ex l7_scope c0 ec2 l7_seg1"
  unfolding cdc_segment_between_def l7_seg1_def H_ex_def cdc_lift_def
  by (simp add: l7_c0_le_ec2 l7_c0_lt_ec1 l7_c0_lt_ec2 l7_c0_lt_ec3
                l7_c0_lt_ec4 l7_ec1_le_ec2 l7_not_ec3_le_ec2
                l7_not_ec4_le_ec2)

lemma l7_seg2_segment:
  "cdc_segment_between H_ex l7_scope ec2 ec4 l7_seg2"
  unfolding cdc_segment_between_def l7_seg2_def H_ex_def cdc_lift_def
  by (simp add: l7_ec2_le_ec4 l7_ec2_lt_ec3 l7_ec2_lt_ec4 l7_ec3_le_ec4
                l7_not_ec2_lt_ec1)

text \<open>
  The base case: the empty replay is a virtual cut on @{const l7_scope}
  at the base coordinate. @{const Apply} of the empty sequence is the
  empty per-key state, and so is @{term "Src (\<lambda>_. None) H_ex c0"}
  by @{thm Src_at_base}.
\<close>

lemma l7_vc0: "virtual_cut_state (\<lambda>_. None) [] l7_scope c0 H_ex"
  unfolding virtual_cut_state_def
  using Src_at_base[OF wf_h_ex, of "\<lambda>_. None"]
  by (simp add: Apply_def)

text \<open>
  Continuing the base cut by @{const l7_seg1} reaches a virtual cut
  at @{text ec2}, by the continuation theorem.
\<close>

lemma l7_vc_ec2: "virtual_cut_state (\<lambda>_. None) l7_seg1 l7_scope ec2 H_ex"
  using virtual_cut_state_continuation[OF wf_h_ex l7_vc0 l7_seg1_segment]
  by simp

text \<open>
  The positive continuation witness. Continuing the @{text ec2} cut
  by @{const l7_seg2} reaches a virtual cut at @{text ec4}: replaying
  @{term "l7_seg1 @ l7_seg2"} agrees with the source state at
  @{text ec4} on the three in-scope keys. Both segments are nonempty
  and the scope is nonempty (@{text continuation_witness_nonvacuous}
  below), so the conclusion is not vacuous.
\<close>

theorem continuation_positive_witness:
  "virtual_cut_state (\<lambda>_. None) (l7_seg1 @ l7_seg2) l7_scope ec4 H_ex"
  by (rule virtual_cut_state_continuation[OF wf_h_ex l7_vc_ec2 l7_seg2_segment])

text \<open>
  The concatenated segment is itself the single continuation segment
  for the combined interval @{text "(c0, ec4]"}, by the chaining
  lemma --- the reader-facing "a finite prefix of ongoing CDC is a
  fold of continuation segments" statement, on the example.
\<close>

theorem continuation_witness_chained_segment:
  "cdc_segment_between H_ex l7_scope c0 ec4 (l7_seg1 @ l7_seg2)"
  by (rule cdc_segment_between_concat[OF wf_h_ex l7_seg1_segment l7_seg2_segment])

text \<open>
  Non-vacuity: the scope and both continuation segments are
  nonempty, so @{thm continuation_positive_witness} is a
  genuine continuation, not the empty-scope vacuity.
\<close>

theorem continuation_witness_nonvacuous:
  "l7_scope \<noteq> {} \<and> l7_seg1 \<noteq> [] \<and> l7_seg2 \<noteq> []"
  by (simp add: l7_seg1_def l7_seg2_def)

section \<open>Shared infrastructure for the negative and boundary fixtures\<close>

text \<open>
  The fixtures below exercise the clauses of @{const cdc_segment_between}.
  For the in-scope coverage, value, ordering, multiplicity, and
  frontier-interval clauses they are load-bearing in the strong sense: a
  continuation segment that violates the clause is rejected by the
  predicate \<^emph>\<open>and\<close> --- the substantive part --- drives
  @{thm [source] virtual_cut_state_continuation} to a wrong conclusion,
  so the clause cannot be dropped from the theorem's premise. The exact
  in-scope-projection aspect (no out-of-scope padding) is instead an
  evidence-faithfulness discipline: an out-of-scope-padded segment is
  rejected by the predicate, yet @{const virtual_cut_state} restricted to
  the key scope still holds, so that aspect is not load-bearing for the
  scoped conclusion. A dedicated fixture,
  @{text fix_l7_out_of_scope_padding_rejected_not_loadbearing} below,
  exhibits exactly that. The empty-scope vacuity is pre-empted by the
  positive witness above.

  Uniform setup. Every load-bearing fixture starts from the empty
  replay as a virtual cut at the base coordinate @{const c0} on a
  small tailored source history --- @{text l7_base_cut} discharges that
  base cut from @{thm [source] Src_at_base}. The \<^emph>\<open>canonical\<close>
  continuation segment for @{text "(c0, f']"} then continues it to a
  genuine virtual cut at @{text f'} (@{text l7_canon_continuation});
  since the base sequence is empty, that cut is @{term "virtual_cut_state
  (\<lambda>_. None) \<delta> K f' H"} for the canonical @{text \<delta>}. A
  \<^emph>\<open>tampered\<close> segment @{text \<delta>'} that violates one clause then
  replays, on some in-scope key, to a value the canonical segment does
  not --- so @{term "virtual_cut_state (\<lambda>_. None) \<delta>' K f' H"} fails
  (@{text l7_breaks_continuation}).

  The tailored histories use only the running example's source
  coordinates @{text "ec1 \<dots> ec4"}; no new source-coordinate or
  history-carrier axioms are introduced.
\<close>

text \<open>
  Two source-coordinate order facts in the @{class linorder}
  @{text \<open>\<le>\<close>} / @{text \<open><\<close>} form, beyond those stated for the
  positive witness above.
\<close>

lemma l7_c0_le_ec1: "c0 \<le> ec1" using l7_c0_lt_ec1 by (rule less_imp_le)
lemma l7_not_ec2_le_ec1: "\<not> ec2 \<le> ec1" using l7_ec1_lt_ec2 by (simp add: not_le)

text \<open>
  Wellformedness of one- and two-event tailored histories. WF-H1 is
  the single coordinate comparison (or vacuous); WF-H2 is the
  @{text "\<noteq> c0"} clauses; WF-H3 holds by @{type src_coord} linear-order
  totality on the two valid indices.
\<close>

lemma l7_wf_one:
  fixes ca :: src_coord and ea :: "(nat, nat) source_event"
  assumes "c0 \<noteq> ca"
  shows "wellformed_src_history [(ca, ea)]"
  unfolding wellformed_src_history_def
  using assms by auto

lemma l7_wf_two:
  fixes ca cb :: src_coord
    and ea eb :: "(nat, nat) source_event"
  assumes le:  "src_le ca cb"
      and a0c: "c0 \<noteq> ca"
      and b0c: "c0 \<noteq> cb"
  shows "wellformed_src_history [(ca, ea), (cb, eb)]"
proof -
  let ?H = "[(ca, ea), (cb, eb)]"
  have spo01: "source_pos_order ?H 0 1"
  proof -
    from le have "src_lt ca cb \<or> ca = cb"
      unfolding src_lt_def by blast
    thus ?thesis unfolding source_pos_order_def by auto
  qed
  show ?thesis
    unfolding wellformed_src_history_def
  proof (intro conjI allI impI)
    fix i assume "Suc i < length ?H"
    hence "i = 0" by simp
    thus "src_le (hist_coord (?H ! i)) (hist_coord (?H ! Suc i))"
      using le by simp
  next
    fix i assume "i < length ?H"
    hence "i = 0 \<or> i = 1" by auto
    thus "hist_coord (?H ! i) \<noteq> c0" using a0c b0c by auto
  next
    fix i j assume "i < length ?H \<and> j < length ?H \<and> i \<noteq> j"
    hence "(i = 0 \<and> j = 1) \<or> (i = 1 \<and> j = 0)" by auto
    thus "source_pos_order ?H i j \<or> source_pos_order ?H j i"
      using spo01 by blast
  qed
qed

text \<open>
  The empty replay is a virtual cut at the base coordinate on any
  wellformed history, under the empty base state --- the generalised
  form of @{thm [source] l7_vc0}.
\<close>

lemma l7_base_cut:
  assumes "wellformed_src_history H"
  shows "virtual_cut_state (\<lambda>_. None) [] K c0 H"
  unfolding virtual_cut_state_def
  using Src_at_base[OF assms, of "\<lambda>_. None"]
  by (simp add: Apply_def)

text \<open>
  The canonical continuation segment for @{text "(c0, f']"} continues
  the base cut to a genuine virtual cut at @{text f'} --- the positive
  control against which the tampered segments are compared.
\<close>

lemma l7_canon_continuation:
  assumes wf:  "wellformed_src_history H"
      and seg: "cdc_segment_between H K c0 f' \<delta>"
  shows "virtual_cut_state (\<lambda>_. None) \<delta> K f' H"
proof -
  have "virtual_cut_state (\<lambda>_. None) ([] @ \<delta>) K f' H"
    by (rule virtual_cut_state_continuation[OF wf l7_base_cut[OF wf] seg])
  thus ?thesis by simp
qed

text \<open>
  A tampered continuation segment breaks the cut. If the canonical
  segment @{text dc} is a virtual cut at @{text f'} and a candidate
  @{text dx} replays, at some in-scope key @{text k}, to a value
  @{text dc} does not, then @{text dx} is not a virtual cut at
  @{text f'}: the continuation conclusion is genuinely lost, not
  merely the predicate.
\<close>

lemma l7_breaks_continuation:
  fixes b0 :: "'k \<rightharpoonup> 'v"
  assumes canon: "virtual_cut_state b0 dc K f' H"
      and kK:    "k \<in> K"
      and diff:  "Apply dx k \<noteq> Apply dc k"
  shows "\<not> virtual_cut_state b0 dx K f' H"
proof
  assume "virtual_cut_state b0 dx K f' H"
  with canon
  have "restrict (Apply dx) K = restrict (Apply dc) K"
    unfolding virtual_cut_state_def by simp
  hence "restrict (Apply dx) K k = restrict (Apply dc) K k" by simp
  with kK have "Apply dx k = Apply dc k"
    unfolding restrict_def by simp
  with diff show False by simp
qed

section \<open>Load-bearing fixtures: the in-scope \<open>cdc_segment_between\<close> clauses are necessary\<close>

subsection \<open>CDC coverage and continuation faithfulness\<close>

text \<open>
  Source history @{text l7_H_cov}: one in-scope update of key
  @{text 100} at @{text ec1}. The canonical continuation segment for
  @{text "(c0, ec1]"} on @{text "{100}"} is @{text "[Cdc ec1 (Update
  100 3000)]"}; @{text l7_cov_canon} is the genuine virtual cut.
\<close>

definition l7_H_cov :: "(nat, nat) src_history" where
  "l7_H_cov = [(ec1, Update 100 3000)]"

lemma l7_wf_cov: "wellformed_src_history l7_H_cov"
  unfolding l7_H_cov_def by (rule l7_wf_one[OF c0_neq_ec1])

lemma l7_cov_canon_seg:
  "cdc_segment_between l7_H_cov {100} c0 ec1 [Cdc ec1 (Update 100 3000)]"
  unfolding cdc_segment_between_def l7_H_cov_def cdc_lift_def
  by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1)

lemma l7_cov_canon:
  "virtual_cut_state (\<lambda>_. None) [Cdc ec1 (Update 100 3000)] {100} ec1 l7_H_cov"
  by (rule l7_canon_continuation[OF l7_wf_cov l7_cov_canon_seg])

text \<open>
  Fixture --- \<^emph>\<open>missing in-scope event\<close>. Key
  @{text 100} is updated in @{text "(c0, ec1]"} but the candidate
  segment omits it. The empty segment is not a continuation segment,
  and replaying it leaves key @{text 100} at the base @{term None}
  rather than the source value: CDC coverage is load-bearing.
\<close>

theorem fix_l7_missing_event:
  "\<not> cdc_segment_between l7_H_cov {100} c0 ec1 []
   \<and> \<not> virtual_cut_state (\<lambda>_. None) [] {100} ec1 l7_H_cov"
proof
  show "\<not> cdc_segment_between l7_H_cov {100} c0 ec1 []"
    unfolding cdc_segment_between_def l7_H_cov_def cdc_lift_def
    by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1)
next
  show "\<not> virtual_cut_state (\<lambda>_. None) [] {100} ec1 l7_H_cov"
    by (rule l7_breaks_continuation[OF l7_cov_canon, where k = 100])
       (simp_all add: Apply_def)
qed

text \<open>
  Fixture --- \<^emph>\<open>segment event not in the source
  history\<close>. The candidate segment carries an update of key @{text 100}
  at @{text ec1} to a fabricated value never present in @{const
  l7_H_cov}. It is not a continuation segment, and replaying it
  reaches the fabricated value: continuation-segment faithfulness to
  @{text H} is a premise --- an External observation assumption ---
  not a fact the algebra establishes.
\<close>

theorem fix_l7_event_not_in_history:
  "\<not> cdc_segment_between l7_H_cov {100} c0 ec1 [Cdc ec1 (Update 100 7777)]
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 7777)] {100} ec1 l7_H_cov"
proof
  show "\<not> cdc_segment_between l7_H_cov {100} c0 ec1 [Cdc ec1 (Update 100 7777)]"
    unfolding cdc_segment_between_def l7_H_cov_def cdc_lift_def
    by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1)
next
  show "\<not> virtual_cut_state (\<lambda>_. None)
           [Cdc ec1 (Update 100 7777)] {100} ec1 l7_H_cov"
    by (rule l7_breaks_continuation[OF l7_cov_canon, where k = 100])
       (simp_all add: Apply_def)
qed

subsection \<open>The interval upper bound \<open>c \<le> f'\<close>\<close>

text \<open>
  Source history @{text l7_H_future}: key @{text 100} is updated at
  @{text ec1} and again at the later @{text ec2}. The canonical
  segment for @{text "(c0, ec1]"} excludes the @{text ec2} update;
  @{text l7_future_canon} is the genuine virtual cut at @{text ec1}.
\<close>

definition l7_H_future :: "(nat, nat) src_history" where
  "l7_H_future = [(ec1, Update 100 3000), (ec2, Update 100 9000)]"

lemma l7_wf_future: "wellformed_src_history l7_H_future"
  unfolding l7_H_future_def
  by (rule l7_wf_two[OF ec1_le_ec2 c0_neq_ec1 c0_neq_ec2])

lemma l7_future_canon_seg:
  "cdc_segment_between l7_H_future {100} c0 ec1 [Cdc ec1 (Update 100 3000)]"
  unfolding cdc_segment_between_def l7_H_future_def cdc_lift_def
  by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1 l7_c0_lt_ec2 l7_not_ec2_le_ec1)

lemma l7_future_canon:
  "virtual_cut_state (\<lambda>_. None) [Cdc ec1 (Update 100 3000)] {100} ec1 l7_H_future"
  by (rule l7_canon_continuation[OF l7_wf_future l7_future_canon_seg])

text \<open>
  Fixture --- \<^emph>\<open>extra event past the frontier\<close>.
  The candidate segment for @{text "(c0, ec1]"} also carries the
  @{text ec2} update, whose coordinate exceeds @{text ec1}. It is not
  a continuation segment, and replaying it reaches the future value
  @{text 9000} rather than @{const Src} at @{text ec1}: the @{text
  "c \<le> f'"} interval bound is load-bearing.
\<close>

theorem fix_l7_future_event:
  "\<not> cdc_segment_between l7_H_future {100} c0 ec1
        [Cdc ec1 (Update 100 3000), Cdc ec2 (Update 100 9000)]
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 3000), Cdc ec2 (Update 100 9000)]
         {100} ec1 l7_H_future"
proof
  show "\<not> cdc_segment_between l7_H_future {100} c0 ec1
          [Cdc ec1 (Update 100 3000), Cdc ec2 (Update 100 9000)]"
    unfolding cdc_segment_between_def l7_H_future_def cdc_lift_def
    by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1 l7_c0_lt_ec2 l7_not_ec2_le_ec1)
next
  show "\<not> virtual_cut_state (\<lambda>_. None)
           [Cdc ec1 (Update 100 3000), Cdc ec2 (Update 100 9000)]
           {100} ec1 l7_H_future"
    by (rule l7_breaks_continuation[OF l7_future_canon, where k = 100])
       (simp_all add: Apply_def)
qed

subsection \<open>Same-coordinate source-position order and multiplicity\<close>

text \<open>
  Source history @{text l7_H_dup}: two updates of key @{text 100} at
  the \<^emph>\<open>same\<close> source coordinate @{text ec1}, to @{text 1} then
  @{text 2}. WF-H1 admits same-coordinate events. The canonical
  segment keeps both, in source-position order; the
  @{text "\<preceq>\<^sub>H"}-latest one (value @{text 2}) wins, so
  @{text l7_dup_canon} is the genuine virtual cut.
\<close>

definition l7_H_dup :: "(nat, nat) src_history" where
  "l7_H_dup = [(ec1, Update 100 1), (ec1, Update 100 2)]"

lemma l7_wf_dup: "wellformed_src_history l7_H_dup"
  unfolding l7_H_dup_def
  by (rule l7_wf_two[OF src_le_refl c0_neq_ec1 c0_neq_ec1])

lemma l7_dup_canon_seg:
  "cdc_segment_between l7_H_dup {100} c0 ec1
     [Cdc ec1 (Update 100 1), Cdc ec1 (Update 100 2)]"
  unfolding cdc_segment_between_def l7_H_dup_def cdc_lift_def
  by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1)

lemma l7_dup_canon:
  "virtual_cut_state (\<lambda>_. None)
     [Cdc ec1 (Update 100 1), Cdc ec1 (Update 100 2)] {100} ec1 l7_H_dup"
  by (rule l7_canon_continuation[OF l7_wf_dup l7_dup_canon_seg])

text \<open>
  Fixture --- \<^emph>\<open>same-coordinate events reordered\<close>.
  The candidate segment carries the two @{text ec1} updates in the
  reverse of their source-position order. It is not a continuation
  segment, and replaying it makes the stale value @{text 1} win
  instead of @{text 2}: same-coordinate source-position order is
  load-bearing.
\<close>

theorem fix_l7_same_coordinate_order:
  "\<not> cdc_segment_between l7_H_dup {100} c0 ec1
        [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)]
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup"
proof
  show "\<not> cdc_segment_between l7_H_dup {100} c0 ec1
          [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)]"
    unfolding cdc_segment_between_def l7_H_dup_def cdc_lift_def
    by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1)
next
  show "\<not> virtual_cut_state (\<lambda>_. None)
           [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup"
    by (rule l7_breaks_continuation[OF l7_dup_canon, where k = 100])
       (simp_all add: Apply_def)
qed

text \<open>
  Fixture --- \<^emph>\<open>multiplicity not preserved\<close>. The
  candidate segment drops one of the two same-coordinate @{text ec1}
  occurrences, keeping only the earlier @{text "Update 100 1"}. It is
  not a continuation segment, and replaying it leaves the stale value
  @{text 1}: the segment is a \<^emph>\<open>filter\<close> of the source history, not a
  deduplicated set --- multiplicity is load-bearing.
\<close>

theorem fix_l7_multiplicity:
  "\<not> cdc_segment_between l7_H_dup {100} c0 ec1 [Cdc ec1 (Update 100 1)]
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup"
proof
  show "\<not> cdc_segment_between l7_H_dup {100} c0 ec1 [Cdc ec1 (Update 100 1)]"
    unfolding cdc_segment_between_def l7_H_dup_def cdc_lift_def
    by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1)
next
  show "\<not> virtual_cut_state (\<lambda>_. None)
           [Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup"
    by (rule l7_breaks_continuation[OF l7_dup_canon, where k = 100])
       (simp_all add: Apply_def)
qed

text \<open>
  Fixture --- \<^emph>\<open>coordinate-sorted is not enough\<close>.
  The reversed same-coordinate segment of
  @{thm [source] fix_l7_same_coordinate_order} is still
  \<^emph>\<open>sorted by coordinate\<close>
  (both events sit at @{text ec1}). A predicate requiring only
  coordinate-sortedness would wrongly accept it; yet it is not a
  continuation segment and breaks the cut. The predicate must pin
  source-\<^emph>\<open>position\<close> order, not merely coordinate order.
\<close>

theorem fix_l7_coordinate_sorted_insufficient:
  "sorted (map cdc_coord [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)])
   \<and> \<not> cdc_segment_between l7_H_dup {100} c0 ec1
         [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)]
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup"
proof (intro conjI)
  show "sorted (map cdc_coord [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)])"
    by simp
next
  show "\<not> cdc_segment_between l7_H_dup {100} c0 ec1
          [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)]"
    unfolding cdc_segment_between_def l7_H_dup_def cdc_lift_def
    by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1)
next
  show "\<not> virtual_cut_state (\<lambda>_. None)
           [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup"
    by (rule l7_breaks_continuation[OF l7_dup_canon, where k = 100])
       (simp_all add: Apply_def)
qed

subsection \<open>The frontier order \<open>f \<le> f'\<close>\<close>

text \<open>
  Source history @{text l7_H_back}: a single update of key @{text 100}
  at @{text ec2}. The segment @{text "[Cdc ec2 (Update 100 5000)]"} is
  the canonical continuation segment for @{text "(c0, ec2]"}.
\<close>

definition l7_H_back :: "(nat, nat) src_history" where
  "l7_H_back = [(ec2, Update 100 5000)]"

lemma l7_wf_back: "wellformed_src_history l7_H_back"
  unfolding l7_H_back_def by (rule l7_wf_one[OF c0_neq_ec2])

lemma l7_back_canon_seg:
  "cdc_segment_between l7_H_back {100} c0 ec2 [Cdc ec2 (Update 100 5000)]"
  unfolding cdc_segment_between_def l7_H_back_def cdc_lift_def
  by (simp add: l7_c0_le_ec2 l7_c0_lt_ec2)

lemma l7_back_canon:
  "virtual_cut_state (\<lambda>_. None) [Cdc ec2 (Update 100 5000)] {100} ec2 l7_H_back"
  by (rule l7_canon_continuation[OF l7_wf_back l7_back_canon_seg])

text \<open>
  The source state at @{text ec1} is the empty base state: the only
  source event sits at @{text ec2}, which is strictly after
  @{text ec1}, so no event lies in @{text "(c0, ec1]"} and
  @{thm [source] Src_interval_decomposition} carries @{const Src} from
  @{const c0} unchanged.
\<close>

lemma l7_back_src_ec1: "Src (\<lambda>_. None) l7_H_back ec1 = (\<lambda>_. None)"
proof (rule ext)
  fix k :: nat
  have seg_empty:
    "filter (\<lambda>(c, e). c0 < c \<and> c \<le> ec1 \<and> key_of e = k) l7_H_back = []"
    unfolding l7_H_back_def using l7_not_ec2_le_ec1 by simp
  have "Src (\<lambda>_. None) l7_H_back ec1 k = Src (\<lambda>_. None) l7_H_back c0 k"
    using Src_interval_decomposition[OF l7_wf_back l7_c0_le_ec1,
            of "\<lambda>_. None" k] seg_empty
    by (simp add: Let_def)
  also have "\<dots> = None"
    using Src_at_base[OF l7_wf_back, of "\<lambda>_. None"] by simp
  finally show "Src (\<lambda>_. None) l7_H_back ec1 k = (\<lambda>_. None) k" by simp
qed

text \<open>
  Fixture --- \<^emph>\<open>backwards frontiers\<close>. With
  @{text "f = ec2"} and @{text "f' = ec1"} (so @{text "f' < f"}) no
  list is a continuation segment: @{const cdc_segment_between} carries
  the @{text "f \<le> f'"} guard. And the guard is load-bearing for the
  theorem: the canonical segment @{text "[Cdc ec2 (Update 100 5000)]"}
  is a virtual cut at @{text ec2}, but not at the earlier @{text ec1}
  --- replay holds @{text 5000} there while @{const Src} at
  @{text ec1} is still the base @{term None}.
\<close>

theorem fix_l7_frontier_order:
  "(\<forall>\<delta>. \<not> cdc_segment_between l7_H_back {100} ec2 ec1 \<delta>)
   \<and> virtual_cut_state (\<lambda>_. None) [Cdc ec2 (Update 100 5000)] {100} ec2 l7_H_back
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec2 (Update 100 5000)] {100} ec1 l7_H_back"
proof (intro conjI)
  show "\<forall>\<delta>. \<not> cdc_segment_between l7_H_back {100} ec2 ec1 \<delta>"
    unfolding cdc_segment_between_def using l7_not_ec2_le_ec1 by simp
next
  show "virtual_cut_state (\<lambda>_. None) [Cdc ec2 (Update 100 5000)] {100} ec2 l7_H_back"
    by (rule l7_back_canon)
next
  show "\<not> virtual_cut_state (\<lambda>_. None)
           [Cdc ec2 (Update 100 5000)] {100} ec1 l7_H_back"
  proof
    assume "virtual_cut_state (\<lambda>_. None)
              [Cdc ec2 (Update 100 5000)] {100} ec1 l7_H_back"
    hence "restrict (Apply [Cdc ec2 (Update 100 5000)]) {100} (100::nat)
             = restrict (Src (\<lambda>_. None) l7_H_back ec1) {100} 100"
      unfolding virtual_cut_state_def by simp
    thus False
      by (simp add: restrict_def l7_back_src_ec1 Apply_def)
  qed
qed

subsection \<open>Deletes are state facts\<close>

text \<open>
  Source history @{text l7_H_del}: key @{text 100} is updated at
  @{text ec1} and deleted at @{text ec2}. The canonical segment for
  @{text "(c0, ec2]"} carries both events, so @{text l7_del_canon}
  --- the genuine virtual cut at @{text ec2} --- has key @{text 100}
  absent.
\<close>

definition l7_H_del :: "(nat, nat) src_history" where
  "l7_H_del = [(ec1, Update 100 3000), (ec2, Delete 100)]"

lemma l7_wf_del: "wellformed_src_history l7_H_del"
  unfolding l7_H_del_def
  by (rule l7_wf_two[OF ec1_le_ec2 c0_neq_ec1 c0_neq_ec2])

lemma l7_del_canon_seg:
  "cdc_segment_between l7_H_del {100} c0 ec2
     [Cdc ec1 (Update 100 3000), Cdc ec2 (Delete 100)]"
  unfolding cdc_segment_between_def l7_H_del_def cdc_lift_def
  by (simp add: l7_c0_le_ec2 l7_c0_lt_ec1 l7_c0_lt_ec2 l7_ec1_le_ec2)

lemma l7_del_canon:
  "virtual_cut_state (\<lambda>_. None)
     [Cdc ec1 (Update 100 3000), Cdc ec2 (Delete 100)] {100} ec2 l7_H_del"
  by (rule l7_canon_continuation[OF l7_wf_del l7_del_canon_seg])

text \<open>
  Fixture --- \<^emph>\<open>delete omitted\<close>. The candidate
  segment carries the @{text ec1} update but omits the @{text ec2}
  delete. It is not a continuation segment, and replaying it leaves
  key @{text 100} at the stale value @{text 3000} while @{const Src}
  at @{text ec2} has it absent: a delete is a state fact and the
  segment must include it.
\<close>

theorem fix_l7_delete_omitted:
  "\<not> cdc_segment_between l7_H_del {100} c0 ec2 [Cdc ec1 (Update 100 3000)]
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 3000)] {100} ec2 l7_H_del"
proof
  show "\<not> cdc_segment_between l7_H_del {100} c0 ec2 [Cdc ec1 (Update 100 3000)]"
    unfolding cdc_segment_between_def l7_H_del_def cdc_lift_def
    by (simp add: l7_c0_le_ec2 l7_c0_lt_ec1 l7_c0_lt_ec2 l7_ec1_le_ec2)
next
  show "\<not> virtual_cut_state (\<lambda>_. None)
           [Cdc ec1 (Update 100 3000)] {100} ec2 l7_H_del"
    by (rule l7_breaks_continuation[OF l7_del_canon, where k = 100])
       (simp_all add: Apply_def)
qed

section \<open>Boundary fixtures: scope, certificate acceptance, and the sink boundary\<close>

text \<open>
  The three boundary fixtures mark what the continuation fragment does
  \<^emph>\<open>not\<close> claim. They are not negative
  counterexamples to a theorem; they delimit it.
\<close>

subsection \<open>A scoped continuation is not a whole-table claim\<close>

text \<open>
  Source history @{text l7_H_oos}: an in-scope update of key
  @{text 100} at @{text ec1} and an \<^emph>\<open>out-of-scope\<close> insert of key
  @{text 999} at @{text ec2}. The continuation segment for
  @{text "(c0, ec2]"} on @{text "{100}"} drops the key-@{text 999}
  event, since @{const cdc_segment_between} is an exact in-scope
  projection.
\<close>

definition l7_H_oos :: "(nat, nat) src_history" where
  "l7_H_oos = [(ec1, Update 100 3000), (ec2, Insert 999 5)]"

lemma l7_wf_oos: "wellformed_src_history l7_H_oos"
  unfolding l7_H_oos_def
  by (rule l7_wf_two[OF ec1_le_ec2 c0_neq_ec1 c0_neq_ec2])

lemma l7_oos_scoped_seg:
  "cdc_segment_between l7_H_oos {100} c0 ec2 [Cdc ec1 (Update 100 3000)]"
  unfolding cdc_segment_between_def l7_H_oos_def cdc_lift_def
  by (simp add: l7_c0_le_ec2 l7_c0_lt_ec1 l7_c0_lt_ec2 l7_ec1_le_ec2)

lemma l7_oos_scoped_canon:
  "virtual_cut_state (\<lambda>_. None) [Cdc ec1 (Update 100 3000)] {100} ec2 l7_H_oos"
  by (rule l7_canon_continuation[OF l7_wf_oos l7_oos_scoped_seg])

lemma l7_oos_full_seg:
  "cdc_segment_between l7_H_oos UNIV c0 ec2
     [Cdc ec1 (Update 100 3000), Cdc ec2 (Insert 999 5)]"
  unfolding cdc_segment_between_def l7_H_oos_def cdc_lift_def
  by (simp add: l7_c0_le_ec2 l7_c0_lt_ec1 l7_c0_lt_ec2 l7_ec1_le_ec2)

text \<open>
  The source state at @{text ec2}: the @{text "K = UNIV"} continuation
  carries \<^emph>\<open>every\<close> event of @{text "(c0, ec2]"}, so the source state
  there is the replay of the full segment --- key @{text 999} is
  present, value @{text 5}.
\<close>

lemma l7_oos_src_ec2:
  "Src (\<lambda>_. None) l7_H_oos ec2
     = Apply [Cdc ec1 (Update 100 3000), Cdc ec2 (Insert 999 5)]"
proof -
  have base: "Apply [] = Src (\<lambda>_. None) l7_H_oos c0"
    using Src_at_base[OF l7_wf_oos, of "\<lambda>_. None"] by (simp add: Apply_def)
  have "Apply ([] @ [Cdc ec1 (Update 100 3000), Cdc ec2 (Insert 999 5)])
          = Src (\<lambda>_. None) l7_H_oos ec2"
    by (rule whole_table_state_continuation[OF l7_wf_oos base l7_oos_full_seg])
  thus ?thesis by simp
qed

text \<open>
  Fixture --- \<^emph>\<open>scoped continuation is not
  whole-table\<close>. The scoped continuation reaches a genuine virtual cut
  on @{text "{100}"} at @{text ec2}; yet replaying that scoped segment
  does \<^emph>\<open>not\<close> reach the whole source state at @{text ec2}, because
  key @{text 999} was inserted outside the scope. Whole-table equality
  needs the Layer 4 side conditions (or an all-key continuation
  segment); a scoped cut does not become whole-table for free.
\<close>

theorem fix_l7_scoped_not_whole_table:
  "virtual_cut_state (\<lambda>_. None) [Cdc ec1 (Update 100 3000)] {100} ec2 l7_H_oos
   \<and> Apply [Cdc ec1 (Update 100 3000)] \<noteq> Src (\<lambda>_. None) l7_H_oos ec2"
proof
  show "virtual_cut_state (\<lambda>_. None) [Cdc ec1 (Update 100 3000)] {100} ec2 l7_H_oos"
    by (rule l7_oos_scoped_canon)
next
  show "Apply [Cdc ec1 (Update 100 3000)] \<noteq> Src (\<lambda>_. None) l7_H_oos ec2"
  proof
    assume eq: "Apply [Cdc ec1 (Update 100 3000)] = Src (\<lambda>_. None) l7_H_oos ec2"
    hence "Apply [Cdc ec1 (Update 100 3000)] (999::nat)
             = Src (\<lambda>_. None) l7_H_oos ec2 999"
      by simp
    thus False by (simp add: l7_oos_src_ec2 Apply_def)
  qed
qed

text \<open>
  Fixture --- \<^emph>\<open>out-of-scope padding is rejected but not
  load-bearing\<close>. The same source history @{text l7_H_oos} shows what
  the exact in-scope-projection aspect of @{const cdc_segment_between}
  does \<^emph>\<open>not\<close> buy. The padded candidate segment carries the
  in-scope @{text 100}-update \<^emph>\<open>and\<close> the out-of-scope
  @{text 999}-insert. @{const cdc_segment_between} on @{text "{100}"}
  rejects it: the predicate is an exact in-scope projection, so for
  @{text "(c0, ec2]"} it admits only
  @{term "[Cdc ec1 (Update 100 3000)]"}. Yet
  @{const virtual_cut_state} on @{text "{100}"} at @{text ec2} still
  holds for the padded segment --- the extra @{text 999}-event lies
  outside the scope, so the scope-restricted replay is unchanged.
  The no-padding aspect is therefore an evidence-faithfulness
  discipline, not load-bearing for the scoped continuation conclusion
  (contrast the in-scope clauses, load-bearing in the strong sense
  exercised in the load-bearing fixtures above).
\<close>

theorem fix_l7_out_of_scope_padding_rejected_not_loadbearing:
  "\<not> cdc_segment_between l7_H_oos {100} c0 ec2
        [Cdc ec1 (Update 100 3000), Cdc ec2 (Insert 999 5)]
   \<and> virtual_cut_state (\<lambda>_. None)
        [Cdc ec1 (Update 100 3000), Cdc ec2 (Insert 999 5)] {100} ec2 l7_H_oos"
proof
  show "\<not> cdc_segment_between l7_H_oos {100} c0 ec2
          [Cdc ec1 (Update 100 3000), Cdc ec2 (Insert 999 5)]"
    unfolding cdc_segment_between_def l7_H_oos_def cdc_lift_def
    by (simp add: l7_c0_le_ec2 l7_c0_lt_ec1 l7_c0_lt_ec2 l7_ec1_le_ec2)
next
  show "virtual_cut_state (\<lambda>_. None)
          [Cdc ec1 (Update 100 3000), Cdc ec2 (Insert 999 5)] {100} ec2 l7_H_oos"
    unfolding virtual_cut_state_def
    by (simp add: l7_oos_src_ec2)
qed

subsection \<open>Accessor equality of an extended certificate is not verifier acceptance\<close>

text \<open>
  The certificate carrier @{typ "('k, 'v) cert"} is abstract, so an
  ``extended certificate'' is exhibited by an @{command axiomatization}
  pinning its accessors --- the same device the Layer 3 fixtures use
  for abstract certificates. @{text l7_ext_C} is given the
  \<^emph>\<open>extended accessors\<close> of the running coverage example (scope
  @{text "{100}"}, frontier @{text ec1}, clean prefix the canonical
  continuation segment), but its verifier result is pinned to
  @{const Reject}.
\<close>

axiomatization
    l7_ext_C :: "(nat, nat) cert"
  and l7_ext_E :: "(nat, nat) evidence"
where
    l7_ext_scope:         "scope l7_ext_C = {100}"
  and l7_ext_frontier:      "frontier l7_ext_C = ec1"
  and l7_ext_clean_prefix:  "clean_prefix l7_ext_C = [Cdc ec1 (Update 100 3000)]"
  and l7_ext_verify_reject: "verify l7_ext_C l7_ext_E = Reject"

text \<open>
  Fixture --- \<^emph>\<open>accessor equality is not verifier
  acceptance\<close>. Read through its accessors, @{text l7_ext_C} satisfies
  the accessor-level @{const virtual_cut} predicate: its clean prefix
  replays to the source state on its scope at its frontier. Yet the
  verifier rejects it. The accessor-level algebra
  (@{const virtual_cut_state} on @{text "clean_prefix C @ \<delta>"}) is
  strictly weaker than verifier acceptance; an extended certificate's
  acceptance is a separate evidence and verifier obligation.
\<close>

theorem fix_l7_extended_cert_not_accepted:
  "virtual_cut (\<lambda>_. None) l7_ext_C l7_H_cov
   \<and> verify l7_ext_C l7_ext_E \<noteq> Accept"
proof
  have "virtual_cut_state (\<lambda>_. None) (clean_prefix l7_ext_C)
          (scope l7_ext_C) (frontier l7_ext_C) l7_H_cov"
  proof (rule l7_canon_continuation[OF l7_wf_cov])
    show "cdc_segment_between l7_H_cov (scope l7_ext_C) c0
            (frontier l7_ext_C) (clean_prefix l7_ext_C)"
      unfolding l7_ext_scope l7_ext_frontier l7_ext_clean_prefix
      by (rule l7_cov_canon_seg)
  qed
  thus "virtual_cut (\<lambda>_. None) l7_ext_C l7_H_cov"
    unfolding virtual_cut_def .
next
  show "verify l7_ext_C l7_ext_E \<noteq> Accept"
    by (simp add: l7_ext_verify_reject)
qed

subsection \<open>Re-chunk regeneration is not a sink-repair claim\<close>

text \<open>
  A virtual cut at @{text "(K, f)"} is determined by the source state
  @{term "Src b0 H f"} alone: any two replay sequences that are
  virtual cuts there agree on @{text K}. So a fresh \<^emph>\<open>wellformed\<close>
  DBLog run --- or a fresh accepted certificate --- which yields a
  virtual cut at @{text "(K, f)"} under the existing Layer 2/3
  theorems, regenerates the \<^emph>\<open>same\<close> absolute source-side cut on
  the scope.
\<close>

lemma l7_virtual_cut_source_determined:
  fixes b0 :: "'k \<rightharpoonup> 'v"
  assumes "virtual_cut_state b0 \<sigma>1 K f H"
      and "virtual_cut_state b0 \<sigma>2 K f H"
  shows "restrict (Apply \<sigma>1) K = restrict (Apply \<sigma>2) K"
  using assms unfolding virtual_cut_state_def by simp

text \<open>
  Fixture --- \<^emph>\<open>re-chunk regeneration is not sink
  repair\<close>. The positive witness is a virtual cut at @{text ec4} on
  @{const l7_scope}; and \<^emph>\<open>every\<close> replay sequence that is a virtual
  cut there replays to the same per-key state on @{const l7_scope}.
  A re-chunked run that is itself a virtual cut there --- which a fresh
  wellformed run or accepted certificate yields under the existing
  Layer 2/3 theorems --- therefore regenerates the same absolute
  source-side cut. Every term here is an
  @{const Apply}-against-@{const Src} equality: the model carries no
  destination, replica, or delivery state, and whether a destination
  applies the regenerated prefix is a sink-apply concern. Sink-state
  convergence stays a Non-claim.
\<close>

theorem fix_l7_rechunk_not_sink_repair:
  "virtual_cut_state (\<lambda>_. None) (l7_seg1 @ l7_seg2) l7_scope ec4 H_ex
   \<and> (\<forall>\<sigma>'. virtual_cut_state (\<lambda>_. None) \<sigma>' l7_scope ec4 H_ex
            \<longrightarrow> restrict (Apply \<sigma>') l7_scope
              = restrict (Apply (l7_seg1 @ l7_seg2)) l7_scope)"
proof
  show "virtual_cut_state (\<lambda>_. None) (l7_seg1 @ l7_seg2) l7_scope ec4 H_ex"
    by (rule continuation_positive_witness)
next
  show "\<forall>\<sigma>'. virtual_cut_state (\<lambda>_. None) \<sigma>' l7_scope ec4 H_ex
              \<longrightarrow> restrict (Apply \<sigma>') l7_scope
                = restrict (Apply (l7_seg1 @ l7_seg2)) l7_scope"
  proof (intro allI impI)
    fix \<sigma>' assume "virtual_cut_state (\<lambda>_. None) \<sigma>' l7_scope ec4 H_ex"
    from l7_virtual_cut_source_determined[OF this continuation_positive_witness]
    show "restrict (Apply \<sigma>') l7_scope
            = restrict (Apply (l7_seg1 @ l7_seg2)) l7_scope" .
  qed
qed

section \<open>Negative and boundary fixture bundle marker\<close>

text \<open>
  A single theorem conjoining a sharp fact --- for the
  coordinate-sorted and re-chunk fixtures, both of their sharp
  facts --- from each of the eleven negative and boundary fixtures:
  it fails to build if any fixture regresses.
\<close>

theorem continuation_negative_fixture_bundle_landed:
  "\<not> virtual_cut_state (\<lambda>_. None) [] {100} ec1 l7_H_cov
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 7777)] {100} ec1 l7_H_cov
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 3000), Cdc ec2 (Update 100 9000)]
         {100} ec1 l7_H_future
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup
   \<and> sorted (map cdc_coord [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)])
   \<and> \<not> cdc_segment_between l7_H_dup {100} c0 ec1
         [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)]
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup
   \<and> (\<forall>\<delta>. \<not> cdc_segment_between l7_H_back {100} ec2 ec1 \<delta>)
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 3000)] {100} ec2 l7_H_del
   \<and> Apply [Cdc ec1 (Update 100 3000)] \<noteq> Src (\<lambda>_. None) l7_H_oos ec2
   \<and> virtual_cut (\<lambda>_. None) l7_ext_C l7_H_cov
   \<and> verify l7_ext_C l7_ext_E \<noteq> Accept
   \<and> virtual_cut_state (\<lambda>_. None) (l7_seg1 @ l7_seg2) l7_scope ec4 H_ex
   \<and> (\<forall>\<sigma>'. virtual_cut_state (\<lambda>_. None) \<sigma>' l7_scope ec4 H_ex
            \<longrightarrow> restrict (Apply \<sigma>') l7_scope
              = restrict (Apply (l7_seg1 @ l7_seg2)) l7_scope)"
  using fix_l7_missing_event fix_l7_event_not_in_history fix_l7_future_event
        fix_l7_same_coordinate_order fix_l7_multiplicity
        fix_l7_coordinate_sorted_insufficient fix_l7_frontier_order
        fix_l7_delete_omitted fix_l7_scoped_not_whole_table
        fix_l7_extended_cert_not_accepted fix_l7_rechunk_not_sink_repair
  by blast

end
