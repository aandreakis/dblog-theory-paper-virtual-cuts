theory Layer4_Witnesses
  imports Layer4_Whole_Table Layer3_Witnesses
begin

text \<open>
  Layer 4 positive whole-table witness.

  The witness reuses the running-example accepted certificate from
  Layer3_Witnesses.  The anchor boundary is @{const ec1} and the
  certified frontier is @{const ec4}.  At the anchor, keys 100 and 200 are
  present.  After the anchor, keys 200 and 300 are touched.  The certified
  scope is exactly @{term "{100, 200, 300}"}, and the clean prefix has no
  replay writes outside that scope.  The resulting whole-table side condition
  is non-vacuous and upgrades the existing scoped virtual cut to unrestricted
  table equality.
\<close>

definition l4_anchor :: frontier where
  "l4_anchor = ec1"

subsection \<open>Anchor and post-anchor source facts\<close>

lemma l4_anchor_before_frontier:
  "l4_anchor < frontier l3_C"
  using ec1_le_ec4 ec1_neq_ec4
  by (simp add: l4_anchor_def l3_frontier ex_frontier less_src_coord_def
                src_lt_def)

lemma l4_anchor_le_frontier:
  "l4_anchor \<le> frontier l3_C"
  using ec1_le_ec4
  by (simp add: l4_anchor_def l3_frontier ex_frontier less_eq_src_coord_def)

lemma latest_src_event_H_ex_ec1_other:
  assumes "k \<noteq> (100::nat)" and "k \<noteq> 200"
  shows "latest_src_event H_ex ec1 k = None"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_ex ! i)) ec1
                \<and> key_of (hist_event (H_ex ! i)) = k"
  have "filter ?P [0, 1, 2, 3] = []"
    using assms src_le_refl[where c=ec1] not_src_le_ec2_ec1
          not_src_le_ec3_ec1 not_src_le_ec4_ec1
          H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
    by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_ex by simp
qed

lemma Src_b0_ex_H_ex_ec1:
  "Src b0_ex H_ex ec1 =
     (\<lambda>k. if k = (100::nat) then Some (3000::nat)
          else if k = 200 then Some 10000
          else None)"
proof
  fix k :: nat
  show "Src b0_ex H_ex ec1 k =
        (if k = (100::nat) then Some (3000::nat)
         else if k = 200 then Some 10000
         else None)"
  proof (cases "k = 100")
    case True
    thus ?thesis using Src_b0_ex_H_ex_ec1_100 by simp
  next
    case not100: False
    show ?thesis
    proof (cases "k = 200")
      case True
      thus ?thesis using Src_b0_ex_H_ex_ec1_200 by simp
    next
      case not200: False
      hence latest_none: "latest_src_event H_ex ec1 k = None"
        using not100 latest_src_event_H_ex_ec1_other by blast
      show ?thesis
        unfolding Src_def b0_ex_def
        using not100 not200 latest_none by simp
    qed
  qed
qed

lemma l4_anchor_domain:
  "anchor_domain b0_ex H_ex l4_anchor = {100, 200}"
  unfolding anchor_domain_def l4_anchor_def Src_b0_ex_H_ex_ec1
  by auto

lemma ec1_lt_ec3: "src_lt ec1 ec3"
  using ec1_le_ec3 ec1_neq_ec3 by (simp add: src_lt_def)

lemma ec1_lt_ec4: "src_lt ec1 ec4"
  using ec1_le_ec4 ec1_neq_ec4 by (simp add: src_lt_def)

lemma ec1_less_ec2: "ec1 < ec2"
  using ec1_lt_ec2 by (simp add: less_src_coord_def)

lemma ec1_less_ec3: "ec1 < ec3"
  using ec1_lt_ec3 by (simp add: less_src_coord_def)

lemma ec1_less_ec4: "ec1 < ec4"
  using ec1_lt_ec4 by (simp add: less_src_coord_def)

lemma ec2_less_eq_ec4: "ec2 \<le> ec4"
  using ec2_le_ec4 by (simp add: less_eq_src_coord_def)

lemma ec3_less_eq_ec4: "ec3 \<le> ec4"
  using ec3_le_ec4 by (simp add: less_eq_src_coord_def)

lemma l4_touched_between:
  "touched_between H_ex l4_anchor (frontier l3_C) = {200, 300}"
proof (rule subset_antisym)
  show "touched_between H_ex l4_anchor (frontier l3_C) \<subseteq> {200, 300}"
    unfolding touched_between_def l4_anchor_def l3_frontier ex_frontier H_ex_def
    by auto
next
  show "{200, 300} \<subseteq> touched_between H_ex l4_anchor (frontier l3_C)"
  proof
    fix k :: nat
    assume "k \<in> {200, 300}"
    hence "k = 200 \<or> k = 300" by simp
    thus "k \<in> touched_between H_ex l4_anchor (frontier l3_C)"
    proof
      assume k200: "k = 200"
      have in_H: "(ec3, Update 200 12000) \<in> set H_ex"
        by (simp add: H_ex_def)
      have witness:
        "\<exists>c e. (c, e) \<in> set H_ex \<and> ec1 < c \<and> c \<le> ec4 \<and> key_of e = k"
        using in_H k200 ec1_less_ec3 ec3_less_eq_ec4
        by (intro exI[where x=ec3]
                  exI[where x="Update (200::nat) (12000::nat)"]) auto
      show ?thesis
        unfolding touched_between_def l4_anchor_def l3_frontier ex_frontier
        using witness by blast
    next
      assume k300: "k = 300"
      have in_H: "(ec2, Insert 300 2500) \<in> set H_ex"
        by (simp add: H_ex_def)
      have witness:
        "\<exists>c e. (c, e) \<in> set H_ex \<and> ec1 < c \<and> c \<le> ec4 \<and> key_of e = k"
        using in_H k300 ec1_less_ec2 ec2_less_eq_ec4
        by (intro exI[where x=ec2]
                  exI[where x="Insert (300::nat) (2500::nat)"]) auto
      show ?thesis
        unfolding touched_between_def l4_anchor_def l3_frontier ex_frontier
        using witness by blast
    qed
  qed
qed

lemma l4_table_scope_between:
  "table_scope_between b0_ex H_ex l4_anchor (frontier l3_C)
     = scope l3_C"
  unfolding table_scope_between_def
  using l4_anchor_domain l4_touched_between l3_scope ex_scope
  by auto

subsection \<open>Replay-side scope facts\<close>

lemma l4_replay_keys:
  "replay_keys (clean_prefix l3_C) = {100, 200, 300}"
  unfolding replay_keys_def
  using l3_clean_prefix ex_clean_prefix
  by auto

lemma l4_no_unclaimed_replay_keys:
  "no_unclaimed_replay_keys (clean_prefix l3_C) (scope l3_C)"
  unfolding no_unclaimed_replay_keys_def
  using l4_replay_keys l3_scope ex_scope
  by simp

lemma l4_whole_table_claim_scope:
  "whole_table_claim_scope b0_ex l3_C H_ex l4_anchor"
  unfolding whole_table_claim_scope_def
proof (intro conjI)
  show "l4_anchor \<le> frontier l3_C"
    by (rule l4_anchor_le_frontier)
next
  show "anchor_complete_at_boundary b0_ex H_ex l4_anchor (scope l3_C)"
    unfolding anchor_complete_at_boundary_def
    using l4_anchor_domain l3_scope ex_scope by simp
next
  show "all_post_anchor_changes_covered H_ex l4_anchor (frontier l3_C)
          (scope l3_C)"
    unfolding all_post_anchor_changes_covered_def
    using l4_touched_between l3_scope ex_scope by simp
next
  show "no_unclaimed_replay_keys (clean_prefix l3_C) (scope l3_C)"
    by (rule l4_no_unclaimed_replay_keys)
qed

subsection \<open>Unrestricted equality and non-vacuity\<close>

theorem l4_positive_whole_table_equality:
  "Apply (clean_prefix l3_C) = Src b0_ex H_ex (frontier l3_C)"
  using whole_table_equality_from_claim_scope
          [OF l3_witness_accepted_virtual_cut_sound l4_whole_table_claim_scope] .

lemma l4_apply_frontier_value_200:
  "Apply (clean_prefix l3_C) 200 = Some 12000"
  using l3_clean_prefix apply_clean_prefix_ex by simp

lemma l4_source_frontier_value_200:
  "Src b0_ex H_ex (frontier l3_C) 200 = Some 12000"
  using l3_frontier ex_frontier Src_b0_ex_H_ex_ec4_200 by simp

lemma latest_src_event_H_ex_ec4_999:
  "latest_src_event H_ex ec4 (999::nat) = None"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_ex ! i)) ec4
                \<and> key_of (hist_event (H_ex ! i)) = (999::nat)"
  have "filter ?P [0, 1, 2, 3] = []"
    using H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3 by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_ex by simp
qed

lemma l4_outside_key_not_in_scope:
  "(999::nat) \<notin> scope l3_C"
  using l3_scope ex_scope by simp

lemma l4_outside_apply_absent:
  "Apply (clean_prefix l3_C) (999::nat) = None"
  using l3_clean_prefix apply_clean_prefix_ex by simp

lemma l4_outside_source_absent:
  "Src b0_ex H_ex (frontier l3_C) (999::nat) = None"
  unfolding Src_def b0_ex_def
  using l3_frontier ex_frontier latest_src_event_H_ex_ec4_999
  by simp

theorem layer4_positive_whole_table_witness:
  "\<exists>(C :: (nat, nat) cert) (E :: (nat, nat) evidence)
      (Raw :: raw_observation) (b0 :: nat \<rightharpoonup> nat)
      (H :: (nat, nat) src_history) (b :: frontier).
      verify C E = Accept
    \<and> faithful_source_observation E b0 H Raw
    \<and> virtual_cut b0 C H
    \<and> whole_table_claim_scope b0 C H b
    \<and> anchor_domain b0 H b \<noteq> {}
    \<and> b < frontier C
    \<and> touched_between H b (frontier C) \<noteq> {}
    \<and> no_unclaimed_replay_keys (clean_prefix C) (scope C)
    \<and> table_scope_between b0 H b (frontier C) = scope C
    \<and> Apply (clean_prefix C) = Src b0 H (frontier C)
    \<and> Apply (clean_prefix C) 200 = Some 12000
    \<and> Src b0 H (frontier C) 200 = Some 12000
    \<and> (999::nat) \<notin> scope C
    \<and> Apply (clean_prefix C) 999 = None
    \<and> Src b0 H (frontier C) 999 = None"
proof -
  have anchor_nonempty: "anchor_domain b0_ex H_ex l4_anchor \<noteq> {}"
    using l4_anchor_domain by simp
  have touched_nonempty: "touched_between H_ex l4_anchor (frontier l3_C) \<noteq> {}"
    using l4_touched_between by simp
  show ?thesis
  proof (intro exI[where x=l3_C] exI[where x=l3_E]
               exI[where x=l3_Raw] exI[where x=b0_ex]
               exI[where x=H_ex] exI[where x=l4_anchor] conjI)
    show "verify l3_C l3_E = Accept" by (rule l3_verify_accept)
  next
    show "faithful_source_observation l3_E b0_ex H_ex l3_Raw"
      by (rule l3_faithful_positive)
  next
    show "virtual_cut b0_ex l3_C H_ex"
      by (rule l3_witness_accepted_virtual_cut_sound)
  next
    show "whole_table_claim_scope b0_ex l3_C H_ex l4_anchor"
      by (rule l4_whole_table_claim_scope)
  next
    show "anchor_domain b0_ex H_ex l4_anchor \<noteq> {}"
      by (rule anchor_nonempty)
  next
    show "l4_anchor < frontier l3_C"
      by (rule l4_anchor_before_frontier)
  next
    show "touched_between H_ex l4_anchor (frontier l3_C) \<noteq> {}"
      by (rule touched_nonempty)
  next
    show "no_unclaimed_replay_keys (clean_prefix l3_C) (scope l3_C)"
      by (rule l4_no_unclaimed_replay_keys)
  next
    show "table_scope_between b0_ex H_ex l4_anchor (frontier l3_C) = scope l3_C"
      by (rule l4_table_scope_between)
  next
    show "Apply (clean_prefix l3_C) = Src b0_ex H_ex (frontier l3_C)"
      by (rule l4_positive_whole_table_equality)
  next
    show "Apply (clean_prefix l3_C) 200 = Some 12000"
      by (rule l4_apply_frontier_value_200)
  next
    show "Src b0_ex H_ex (frontier l3_C) 200 = Some 12000"
      by (rule l4_source_frontier_value_200)
  next
    show "(999::nat) \<notin> scope l3_C"
      by (rule l4_outside_key_not_in_scope)
  next
    show "Apply (clean_prefix l3_C) 999 = None"
      by (rule l4_outside_apply_absent)
  next
    show "Src b0_ex H_ex (frontier l3_C) 999 = None"
      by (rule l4_outside_source_absent)
  qed
qed

end
