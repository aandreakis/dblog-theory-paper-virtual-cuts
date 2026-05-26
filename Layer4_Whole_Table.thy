theory Layer4_Whole_Table
  imports Virtual_Cut
begin

text \<open>
  Layer 4 whole-table anchor-domain specialization.

  The reader-facing paper keeps the compact notation
  @{text "whole-table-claim-scope(C,H,b)"}.  The formal surface threads the
  deployment base state @{text b0} explicitly, because @{const Src} and
  faithful source observation are both fixed-base-state objects.
\<close>

subsection \<open>Anchor and table-scope definitions\<close>

definition anchor_domain
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) src_history \<Rightarrow> frontier \<Rightarrow> 'k set"
where
  "anchor_domain b0 H b = {k. \<exists>v. Src b0 H b k = Some v}"

definition touched_between
  :: "('k, 'v) src_history \<Rightarrow> frontier \<Rightarrow> frontier \<Rightarrow> 'k set"
where
  "touched_between H b f =
     {k. \<exists>c e. (c, e) \<in> set H \<and> b < c \<and> c \<le> f \<and> key_of e = k}"

definition table_scope_between
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) src_history \<Rightarrow> frontier \<Rightarrow> frontier
      \<Rightarrow> 'k set"
where
  "table_scope_between b0 H b f =
     anchor_domain b0 H b \<union> touched_between H b f"

definition anchor_complete_at_boundary
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) src_history \<Rightarrow> frontier \<Rightarrow> 'k set
      \<Rightarrow> bool"
where
  "anchor_complete_at_boundary b0 H b K \<longleftrightarrow>
     anchor_domain b0 H b \<subseteq> K"

definition all_post_anchor_changes_covered
  :: "('k, 'v) src_history \<Rightarrow> frontier \<Rightarrow> frontier \<Rightarrow> 'k set \<Rightarrow> bool"
where
  "all_post_anchor_changes_covered H b f K \<longleftrightarrow>
     touched_between H b f \<subseteq> K"

subsection \<open>Replay-side no-unclaimed-key condition\<close>

definition replay_keys :: "('k, 'v) replay_event list \<Rightarrow> 'k set"
where
  "replay_keys \<sigma> = event_key ` set \<sigma>"

definition no_unclaimed_replay_keys
  :: "('k, 'v) replay_event list \<Rightarrow> 'k set \<Rightarrow> bool"
where
  "no_unclaimed_replay_keys \<sigma> K \<longleftrightarrow> replay_keys \<sigma> \<subseteq> K"

subsection \<open>Whole-table claim scope\<close>

definition whole_table_claim_scope
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) cert \<Rightarrow> ('k, 'v) src_history
      \<Rightarrow> frontier \<Rightarrow> bool"
where
  "whole_table_claim_scope b0 C H b \<longleftrightarrow>
     b \<le> frontier C
   \<and> anchor_complete_at_boundary b0 H b (scope C)
   \<and> all_post_anchor_changes_covered H b (frontier C) (scope C)
   \<and> no_unclaimed_replay_keys (clean_prefix C) (scope C)"

lemma whole_table_claim_scope_imp_table_scope_contained:
  assumes "whole_table_claim_scope b0 C H b"
  shows "table_scope_between b0 H b (frontier C) \<subseteq> scope C"
  using assms
  unfolding whole_table_claim_scope_def
            table_scope_between_def
            anchor_complete_at_boundary_def
            all_post_anchor_changes_covered_def
  by blast

subsection \<open>Outside-scope bridge lemmas\<close>

lemma source_outside_table_scope_absent:
  assumes b_le_f: "b \<le> f"
      and outside: "k \<notin> table_scope_between b0 H b f"
  shows "Src b0 H f k = None"
proof -
  have anchor_none: "Src b0 H b k = None"
    using outside
    unfolding table_scope_between_def anchor_domain_def
    by (cases "Src b0 H b k") auto

  have no_later:
    "\<forall>i<length H.
       src_lt b (hist_coord (H ! i))
       \<and> src_le (hist_coord (H ! i)) f
       \<longrightarrow> key_of (hist_event (H ! i)) \<noteq> k"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < length H"
    assume between:
      "src_lt b (hist_coord (H ! i))
       \<and> src_le (hist_coord (H ! i)) f"
    show "key_of (hist_event (H ! i)) \<noteq> k"
    proof
      assume key_eq: "key_of (hist_event (H ! i)) = k"
      have pair_in:
        "(hist_coord (H ! i), hist_event (H ! i)) \<in> set H"
        using nth_mem[OF i_lt] by (metis surjective_pairing)
      have "k \<in> touched_between H b f"
      proof -
        have "(hist_coord (H ! i), hist_event (H ! i)) \<in> set H
          \<and> b < hist_coord (H ! i)
          \<and> hist_coord (H ! i) \<le> f
          \<and> key_of (hist_event (H ! i)) = k"
          using pair_in between key_eq
          by (auto simp: src_lt_eq_less src_le_eq_less_eq)
        thus ?thesis
          unfolding touched_between_def
          by blast
      qed
      hence "k \<in> table_scope_between b0 H b f"
        unfolding table_scope_between_def by simp
      with outside show False by contradiction
    qed
  qed

  have "Src b0 H f k = Src b0 H b k"
    by (rule src_eq_when_no_later_src_event_for_k)
       (use b_le_f no_later in \<open>auto simp: src_le_eq_less_eq\<close>)
  thus ?thesis
    using anchor_none by simp
qed

lemma apply_outside_replay_keys_none:
  assumes contained: "replay_keys \<sigma> \<subseteq> K"
      and outside: "k \<notin> K"
  shows "Apply \<sigma> k = None"
proof -
  have no_key_events: "filter (\<lambda>e. event_key e = k) \<sigma> = []"
  proof -
    have "\<forall>e\<in>set \<sigma>. event_key e \<noteq> k"
      using contained outside
      unfolding replay_keys_def
      by blast
    thus ?thesis by simp
  qed
  show ?thesis
    using apply_latest_event_wins[of \<sigma> k] no_key_events
    by simp
qed

lemma unrestricted_equality_from_scoped_equality:
  fixes lhs rhs :: "'k \<rightharpoonup> 'v"
  assumes scoped: "restrict lhs K = restrict rhs K"
      and lhs_outside: "\<And>k. k \<notin> K \<Longrightarrow> lhs k = None"
      and rhs_outside: "\<And>k. k \<notin> K \<Longrightarrow> rhs k = None"
  shows "lhs = rhs"
proof (rule ext)
  fix k
  show "lhs k = rhs k"
  proof (cases "k \<in> K")
    case True
    with scoped show ?thesis
      by (metis restrict_def)
  next
    case False
    thus ?thesis
      by (simp add: lhs_outside rhs_outside)
  qed
qed

lemma whole_table_equality_from_scoped_equality:
  assumes scoped:
    "virtual_cut_state b0 \<sigma> K f H"
  and table_contained:
    "table_scope_between b0 H b f \<subseteq> K"
  and no_unclaimed:
    "no_unclaimed_replay_keys \<sigma> K"
  and b_le_f:
    "b \<le> f"
  shows "Apply \<sigma> = Src b0 H f"
proof (rule unrestricted_equality_from_scoped_equality)
  show "restrict (Apply \<sigma>) K = restrict (Src b0 H f) K"
    using scoped
    unfolding virtual_cut_state_def .
next
  fix k
  assume outside: "k \<notin> K"
  show "Apply \<sigma> k = None"
    by (rule apply_outside_replay_keys_none[OF _ outside])
       (use no_unclaimed in \<open>simp add: no_unclaimed_replay_keys_def\<close>)
next
  fix k
  assume outside: "k \<notin> K"
  hence "k \<notin> table_scope_between b0 H b f"
    using table_contained by blast
  thus "Src b0 H f k = None"
    by (rule source_outside_table_scope_absent[OF b_le_f])
qed

lemma whole_table_equality_from_claim_scope:
  assumes vc: "virtual_cut b0 C H"
      and whole: "whole_table_claim_scope b0 C H b"
  shows "Apply (clean_prefix C) = Src b0 H (frontier C)"
proof -
  have scoped:
    "virtual_cut_state b0 (clean_prefix C) (scope C) (frontier C) H"
    using vc unfolding virtual_cut_def by simp
  have contained:
    "table_scope_between b0 H b (frontier C) \<subseteq> scope C"
    by (rule whole_table_claim_scope_imp_table_scope_contained[OF whole])
  have no_unclaimed:
    "no_unclaimed_replay_keys (clean_prefix C) (scope C)"
    using whole unfolding whole_table_claim_scope_def by blast
  have b_le_frontier: "b \<le> frontier C"
    using whole unfolding whole_table_claim_scope_def by blast
  show ?thesis
    by (rule whole_table_equality_from_scoped_equality
          [OF scoped contained no_unclaimed b_le_frontier])
qed

subsection \<open>Layer 4 theorem surface over accepted certificates\<close>

context layer3_checker_substrate
begin

theorem accepted_whole_table_anchor_domain_specialization:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and Raw :: raw_observation
    and b :: frontier
  assumes accept: "verify C E = Accept"
      and faithful: "faithful_source_observation E b0 H Raw"
      and whole: "whole_table_claim_scope b0 C H b"
  shows "Apply (clean_prefix C) = Src b0 H (frontier C)"
proof -
  have vc: "virtual_cut b0 C H"
    by (rule accepted_virtual_cut_sound[OF accept faithful])
  show ?thesis
    by (rule whole_table_equality_from_claim_scope[OF vc whole])
qed

end

end
