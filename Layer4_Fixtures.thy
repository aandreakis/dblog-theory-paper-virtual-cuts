theory Layer4_Fixtures
  imports Layer4_Witnesses
begin

text \<open>
  Layer 4 negative / boundary fixtures.

  Post-anchor insert not covered:
  The fixture keeps the accepted running-example source history and anchor
  boundary, but uses a certificate shape whose claim scope omits key 300.
  The source history inserts key 300 strictly after the anchor and before the
  certified frontier.  Scoped equality can still hold on the smaller claim
  scope @{text "{100,200}"}, but the whole-table side condition must reject
  the setup and unrestricted equality is false at key 300.

  Post-anchor delete not covered:
  A post-anchor delete of an already-absent key is still included in the
  conservative touched set.  This protects the scope-closure interpretation
  without pretending that every omitted delete is the cleanest independent
  equality-breaking counterexample.

  Empty anchor-domain:
  The empty anchor-domain case is a valid trivial boundary.  It may satisfy
  whole-table claim scope and unrestricted equality, but it is vacuous and
  cannot replace the nonempty positive whole-table witness.

  Claim/refresh-scope mismatch:
  A certificate can claim a key broader than the replay prefix actually
  materializes.  In the current formal model this is caught by failure of the
  underlying virtual-cut equality, rather than by inventing a separate
  refresh-scope object at Layer 4.

  Anchor after frontier:
  If the anchor boundary is after the certified frontier, an empty anchor
  domain can hide a key that was present at the frontier.  The
  @{text "b \<le> frontier(C)"} conjunct rejects exactly this boundary-order
  error.

  Post-anchor update before read:
  A post-anchor source update may be materialized by a later refresh rather
  than by carrying the ordinary CDC update in the certified prefix.  Layer 4
  records this conservatively as a touched key that must be in scope; it does
  not require a minimal ordinary-CDC explanation.

  No-unclaimed-key determinacy:
  The certified prefix may be replay-equivalent on the claim scope while still
  writing an out-of-scope key.  The replay-side no-unclaimed-key condition is
  therefore load-bearing for unrestricted table equality.

  Base-state anchor domain:
  A key present only in the base state is still in the anchor domain.  This
  protects the b0-explicit Layer 4 definitions from silently treating the
  source history alone as the anchor state.

  Same-coordinate boundary:
  A source event exactly at the anchor boundary is part of the anchor state,
  while a source event exactly at the certified frontier is part of the
  post-anchor touched interval.  This pins the intended interval convention:
  anchor state is at @{text b}; post-anchor coverage is @{text "(b, f]"}.

  Materialized-run ambiguity:
  Layer 4's set-only side condition must not be read as responsible-chunk or
  watermark evidence.  The fixture exhibits one certificate and evidence
  materialized by two distinct runs --- the same certificate surface
  (scope, frontier, clean prefix), but different run-side chunk sets and
  responsible chunks.  It is materialization-relational only: the runs are
  tied to the certificate through @{const materializes_run}, not through
  @{const cert_accessors_agree}.
\<close>

definition l4_missing_insert_prefix :: "(nat, nat) replay_event list" where
  "l4_missing_insert_prefix =
     [ Cdc ec1 (Update 100 3000),
       Refresh (100::nat) (Some (3000::nat)) ec1,
       Refresh 200 (Some 10000) ec1,
       Cdc ec3 (Update 200 12000) ]"

axiomatization l4_missing_insert_C :: "(nat, nat) cert"
where
  l4_missing_insert_scope:
    "scope l4_missing_insert_C = {100, 200}"
and
  l4_missing_insert_frontier:
    "frontier l4_missing_insert_C = ec4"
and
  l4_missing_insert_clean_prefix:
    "clean_prefix l4_missing_insert_C = l4_missing_insert_prefix"


section \<open>Scoped virtual cut still holds on the smaller claim scope\<close>

lemma l4_missing_insert_apply_100:
  "Apply l4_missing_insert_prefix (100::nat) = Some (3000::nat)"
  unfolding l4_missing_insert_prefix_def Apply_def by simp

lemma l4_missing_insert_apply_200:
  "Apply l4_missing_insert_prefix (200::nat) = Some (12000::nat)"
  unfolding l4_missing_insert_prefix_def Apply_def by simp

lemma l4_missing_insert_apply_300:
  "Apply l4_missing_insert_prefix (300::nat) = None"
  unfolding l4_missing_insert_prefix_def Apply_def by simp

lemma l4_missing_insert_replay_keys:
  "replay_keys l4_missing_insert_prefix = {100, 200}"
  unfolding replay_keys_def l4_missing_insert_prefix_def
  by auto

lemma l4_missing_insert_no_unclaimed_replay_keys:
  "no_unclaimed_replay_keys
     (clean_prefix l4_missing_insert_C) (scope l4_missing_insert_C)"
  unfolding no_unclaimed_replay_keys_def
  using l4_missing_insert_replay_keys
  by (simp add: l4_missing_insert_clean_prefix l4_missing_insert_scope)

lemma l4_missing_insert_scoped_virtual_cut_state:
  "virtual_cut_state b0_ex l4_missing_insert_prefix {100, 200} ec4 H_ex"
  unfolding virtual_cut_state_def restrict_def
proof (rule ext)
  fix k :: nat
  show "(if k \<in> {100, 200} then Apply l4_missing_insert_prefix k else None)
      = (if k \<in> {100, 200} then Src b0_ex H_ex ec4 k else None)"
  proof (cases "k = 100")
    case True
    thus ?thesis
      using l4_missing_insert_apply_100 Src_b0_ex_H_ex_ec4_100 by simp
  next
    case not100: False
    show ?thesis
    proof (cases "k = 200")
      case True
      thus ?thesis
        using l4_missing_insert_apply_200 Src_b0_ex_H_ex_ec4_200 by simp
    next
      case False
      with not100 show ?thesis by simp
    qed
  qed
qed

lemma l4_missing_insert_virtual_cut:
  "virtual_cut b0_ex l4_missing_insert_C H_ex"
  unfolding virtual_cut_def
  using l4_missing_insert_scoped_virtual_cut_state
  by (simp add: l4_missing_insert_clean_prefix
                l4_missing_insert_scope
                l4_missing_insert_frontier)


section \<open>The post-anchor insert is outside the claim scope\<close>

lemma l4_missing_insert_key_touched:
  "(300::nat) \<in> touched_between H_ex l4_anchor (frontier l4_missing_insert_C)"
proof -
  have in_H: "(ec2, Insert (300::nat) (2500::nat)) \<in> set H_ex"
    by (simp add: H_ex_def)
  have after_anchor: "l4_anchor < ec2"
    using ec1_less_ec2 by (simp add: l4_anchor_def)
  have before_frontier: "ec2 \<le> frontier l4_missing_insert_C"
    using ec2_less_eq_ec4 by (simp add: l4_missing_insert_frontier)
  show ?thesis
    unfolding touched_between_def
    using in_H after_anchor before_frontier
    by (intro CollectI exI[where x=ec2]
              exI[where x="Insert (300::nat) (2500::nat)"]) auto
qed

lemma l4_missing_insert_key_not_in_scope:
  "(300::nat) \<notin> scope l4_missing_insert_C"
  by (simp add: l4_missing_insert_scope)

theorem l4_post_anchor_insert_not_covered:
  "\<not> all_post_anchor_changes_covered
        H_ex l4_anchor (frontier l4_missing_insert_C)
        (scope l4_missing_insert_C)"
  using l4_missing_insert_key_touched l4_missing_insert_key_not_in_scope
  unfolding all_post_anchor_changes_covered_def
  by blast

theorem l4_post_anchor_insert_not_whole_table_claim_scope:
  "\<not> whole_table_claim_scope b0_ex l4_missing_insert_C H_ex l4_anchor"
  using l4_post_anchor_insert_not_covered
  unfolding whole_table_claim_scope_def
  by blast


section \<open>Unrestricted equality is false at the omitted inserted key\<close>

lemma l4_missing_insert_replay_absent_300:
  "Apply (clean_prefix l4_missing_insert_C) (300::nat) = None"
  using l4_missing_insert_apply_300
  by (simp add: l4_missing_insert_clean_prefix)

lemma l4_missing_insert_source_present_300:
  "Src b0_ex H_ex (frontier l4_missing_insert_C) (300::nat) = Some 3500"
  using Src_b0_ex_H_ex_ec4_300
  by (simp add: l4_missing_insert_frontier)

theorem l4_post_anchor_insert_unrestricted_equality_fails:
  "Apply (clean_prefix l4_missing_insert_C)
   \<noteq> Src b0_ex H_ex (frontier l4_missing_insert_C)"
proof
  assume eq:
    "Apply (clean_prefix l4_missing_insert_C)
     = Src b0_ex H_ex (frontier l4_missing_insert_C)"
  hence "Apply (clean_prefix l4_missing_insert_C) (300::nat)
       = Src b0_ex H_ex (frontier l4_missing_insert_C) 300"
    by simp
  thus False
    using l4_missing_insert_replay_absent_300
          l4_missing_insert_source_present_300
    by simp
qed

theorem layer4_post_anchor_insert_not_covered_fixture:
  "virtual_cut b0_ex l4_missing_insert_C H_ex
   \<and> no_unclaimed_replay_keys
        (clean_prefix l4_missing_insert_C) (scope l4_missing_insert_C)
   \<and> (300::nat) \<in> touched_between H_ex l4_anchor
        (frontier l4_missing_insert_C)
   \<and> 300 \<notin> scope l4_missing_insert_C
   \<and> 300 \<notin> replay_keys (clean_prefix l4_missing_insert_C)
   \<and> \<not> all_post_anchor_changes_covered
        H_ex l4_anchor (frontier l4_missing_insert_C)
        (scope l4_missing_insert_C)
   \<and> \<not> whole_table_claim_scope b0_ex l4_missing_insert_C H_ex l4_anchor
   \<and> Apply (clean_prefix l4_missing_insert_C) 300 = None
   \<and> Src b0_ex H_ex (frontier l4_missing_insert_C) 300 = Some 3500
   \<and> Apply (clean_prefix l4_missing_insert_C)
      \<noteq> Src b0_ex H_ex (frontier l4_missing_insert_C)"
  using l4_missing_insert_virtual_cut
        l4_missing_insert_no_unclaimed_replay_keys
        l4_missing_insert_key_touched
        l4_missing_insert_key_not_in_scope
        l4_missing_insert_replay_keys
        l4_post_anchor_insert_not_covered
        l4_post_anchor_insert_not_whole_table_claim_scope
        l4_missing_insert_replay_absent_300
        l4_missing_insert_source_present_300
        l4_post_anchor_insert_unrestricted_equality_fails
  by (simp add: l4_missing_insert_clean_prefix)


section \<open>Post-anchor delete as conservative touch coverage\<close>

definition l4_delete_touch_H :: "(nat, nat) src_history" where
  "l4_delete_touch_H =
     [ (ec1, Update 100 3000),
       (ec2, Delete (400::nat)),
       (ec3, Update 200 12000),
       (ec4, Update 300 3500) ]"

axiomatization l4_delete_touch_C :: "(nat, nat) cert"
where
  l4_delete_touch_scope:
    "scope l4_delete_touch_C = {100, 200, 300}"
and
  l4_delete_touch_frontier:
    "frontier l4_delete_touch_C = ec4"
and
  l4_delete_touch_clean_prefix:
    "clean_prefix l4_delete_touch_C = clean_prefix l3_C"

lemma l4_delete_touch_apply_frontier:
  "Apply (clean_prefix l4_delete_touch_C) =
     (\<lambda>k. if k = (100::nat) then Some (3000::nat)
          else if k = 200 then Some 12000
          else if k = 300 then Some 3500
          else None)"
  by (simp add: l4_delete_touch_clean_prefix l3_clean_prefix
                apply_clean_prefix_ex)

lemma l4_delete_touch_apply_400:
  "Apply (clean_prefix l4_delete_touch_C) (400::nat) = None"
  by (simp add: l4_delete_touch_apply_frontier)

lemma l4_delete_touch_anchor_le_frontier:
  "l4_anchor \<le> frontier l4_delete_touch_C"
  using ec1_le_ec4
  by (simp add: l4_anchor_def l4_delete_touch_frontier
                less_eq_src_coord_def)

lemma latest_src_event_l4_delete_touch_ec4_100:
  "latest_src_event l4_delete_touch_H ec4 (100::nat) = Some 0"
  unfolding latest_src_event_def l4_delete_touch_H_def
  using ec1_le_ec4 ec2_le_ec4 ec3_le_ec4 src_le_refl[where c=ec4]
  by simp

lemma latest_src_event_l4_delete_touch_ec4_200:
  "latest_src_event l4_delete_touch_H ec4 (200::nat) = Some 2"
  unfolding latest_src_event_def l4_delete_touch_H_def
  using ec1_le_ec4 ec2_le_ec4 ec3_le_ec4 src_le_refl[where c=ec4]
  by simp

lemma latest_src_event_l4_delete_touch_ec4_300:
  "latest_src_event l4_delete_touch_H ec4 (300::nat) = Some 3"
  unfolding latest_src_event_def l4_delete_touch_H_def
  using ec1_le_ec4 ec2_le_ec4 ec3_le_ec4 src_le_refl[where c=ec4]
  by simp

lemma latest_src_event_l4_delete_touch_ec4_400:
  "latest_src_event l4_delete_touch_H ec4 (400::nat) = Some 1"
  unfolding latest_src_event_def l4_delete_touch_H_def
  using ec1_le_ec4 ec2_le_ec4 ec3_le_ec4 src_le_refl[where c=ec4]
  by simp

lemma latest_src_event_l4_delete_touch_ec4_other:
  assumes "k \<noteq> (100::nat)" and "k \<noteq> 200" and "k \<noteq> 300" and "k \<noteq> 400"
  shows "latest_src_event l4_delete_touch_H ec4 k = None"
  unfolding latest_src_event_def l4_delete_touch_H_def
  using assms ec1_le_ec4 ec2_le_ec4 ec3_le_ec4 src_le_refl[where c=ec4]
  by simp

lemma Src_b0_ex_l4_delete_touch_ec4_100:
  "Src b0_ex l4_delete_touch_H ec4 (100::nat) = Some 3000"
  unfolding Src_def using latest_src_event_l4_delete_touch_ec4_100
  by (simp add: l4_delete_touch_H_def)

lemma Src_b0_ex_l4_delete_touch_ec4_200:
  "Src b0_ex l4_delete_touch_H ec4 (200::nat) = Some 12000"
  unfolding Src_def using latest_src_event_l4_delete_touch_ec4_200
  by (simp add: l4_delete_touch_H_def)

lemma Src_b0_ex_l4_delete_touch_ec4_300:
  "Src b0_ex l4_delete_touch_H ec4 (300::nat) = Some 3500"
  unfolding Src_def using latest_src_event_l4_delete_touch_ec4_300
  by (simp add: l4_delete_touch_H_def)

lemma Src_b0_ex_l4_delete_touch_ec4_400:
  "Src b0_ex l4_delete_touch_H ec4 (400::nat) = None"
  unfolding Src_def using latest_src_event_l4_delete_touch_ec4_400
  by (simp add: l4_delete_touch_H_def)

lemma Src_b0_ex_l4_delete_touch_ec4_other:
  assumes "k \<noteq> (100::nat)" and "k \<noteq> 200" and "k \<noteq> 300" and "k \<noteq> 400"
  shows "Src b0_ex l4_delete_touch_H ec4 k = None"
  unfolding Src_def b0_ex_def
  using latest_src_event_l4_delete_touch_ec4_other[OF assms] assms
  by simp

lemma Src_b0_ex_l4_delete_touch_ec4:
  "Src b0_ex l4_delete_touch_H ec4 =
     (\<lambda>k. if k = (100::nat) then Some (3000::nat)
          else if k = 200 then Some 12000
          else if k = 300 then Some 3500
          else None)"
proof
  fix k :: nat
  show "Src b0_ex l4_delete_touch_H ec4 k =
        (if k = (100::nat) then Some (3000::nat)
         else if k = 200 then Some 12000
         else if k = 300 then Some 3500
         else None)"
  proof (cases "k = 100")
    case True
    thus ?thesis using Src_b0_ex_l4_delete_touch_ec4_100 by simp
  next
    case not100: False
    show ?thesis
    proof (cases "k = 200")
      case True
      thus ?thesis using Src_b0_ex_l4_delete_touch_ec4_200 by simp
    next
      case not200: False
      show ?thesis
      proof (cases "k = 300")
        case True
        thus ?thesis using Src_b0_ex_l4_delete_touch_ec4_300 by simp
      next
        case not300: False
        show ?thesis
        proof (cases "k = 400")
          case True
          thus ?thesis
            using not100 not200 not300 Src_b0_ex_l4_delete_touch_ec4_400
            by simp
        next
          case False
          with not100 not200 not300 show ?thesis
            using Src_b0_ex_l4_delete_touch_ec4_other by simp
        qed
      qed
    qed
  qed
qed

lemma l4_delete_touch_unrestricted_equality:
  "Apply (clean_prefix l4_delete_touch_C)
   = Src b0_ex l4_delete_touch_H (frontier l4_delete_touch_C)"
  using l4_delete_touch_apply_frontier Src_b0_ex_l4_delete_touch_ec4
  by (simp add: l4_delete_touch_frontier)

lemma l4_delete_touch_virtual_cut:
  "virtual_cut b0_ex l4_delete_touch_C l4_delete_touch_H"
  unfolding virtual_cut_def virtual_cut_state_def
  using l4_delete_touch_unrestricted_equality
  by simp

lemma l4_delete_touch_replay_keys:
  "replay_keys (clean_prefix l4_delete_touch_C) = {100, 200, 300}"
  using l4_replay_keys
  by (simp add: l4_delete_touch_clean_prefix)

lemma l4_delete_touch_no_unclaimed_replay_keys:
  "no_unclaimed_replay_keys
     (clean_prefix l4_delete_touch_C) (scope l4_delete_touch_C)"
  unfolding no_unclaimed_replay_keys_def
  using l4_delete_touch_replay_keys
  by (simp add: l4_delete_touch_scope)

lemma l4_delete_touch_anchor_domain:
  "anchor_domain b0_ex l4_delete_touch_H l4_anchor = {100, 200}"
  unfolding anchor_domain_def l4_anchor_def Src_def latest_src_event_def
            l4_delete_touch_H_def b0_ex_def
  using src_le_refl[where c=ec1] not_src_le_ec2_ec1
        not_src_le_ec3_ec1 not_src_le_ec4_ec1
  by auto

lemma l4_delete_touch_anchor_complete:
  "anchor_complete_at_boundary
     b0_ex l4_delete_touch_H l4_anchor (scope l4_delete_touch_C)"
  unfolding anchor_complete_at_boundary_def
  using l4_delete_touch_anchor_domain
  by (simp add: l4_delete_touch_scope)

lemma l4_delete_touch_key_touched:
  "(400::nat) \<in> touched_between
       l4_delete_touch_H l4_anchor (frontier l4_delete_touch_C)"
proof -
  have in_H: "(ec2, Delete (400::nat)) \<in> set l4_delete_touch_H"
    by (simp add: l4_delete_touch_H_def)
  have after_anchor: "l4_anchor < ec2"
    using ec1_less_ec2 by (simp add: l4_anchor_def)
  have before_frontier: "ec2 \<le> frontier l4_delete_touch_C"
    using ec2_less_eq_ec4 by (simp add: l4_delete_touch_frontier)
  show ?thesis
    unfolding touched_between_def
    using in_H after_anchor before_frontier
    by (intro CollectI exI[where x=ec2]
              exI[where x="Delete (400::nat)"]) auto
qed

lemma l4_delete_touch_key_not_in_scope:
  "(400::nat) \<notin> scope l4_delete_touch_C"
  by (simp add: l4_delete_touch_scope)

lemma l4_delete_touch_key_not_in_replay_keys:
  "(400::nat) \<notin> replay_keys (clean_prefix l4_delete_touch_C)"
  by (simp add: l4_delete_touch_replay_keys)

lemma l4_delete_touch_source_absent_400:
  "Src b0_ex l4_delete_touch_H
      (frontier l4_delete_touch_C) (400::nat) = None"
  using Src_b0_ex_l4_delete_touch_ec4_400
  by (simp add: l4_delete_touch_frontier)

theorem l4_post_anchor_delete_not_covered:
  "\<not> all_post_anchor_changes_covered
        l4_delete_touch_H l4_anchor (frontier l4_delete_touch_C)
        (scope l4_delete_touch_C)"
  using l4_delete_touch_key_touched l4_delete_touch_key_not_in_scope
  unfolding all_post_anchor_changes_covered_def
  by blast

theorem l4_post_anchor_delete_not_whole_table_claim_scope:
  "\<not> whole_table_claim_scope b0_ex l4_delete_touch_C
        l4_delete_touch_H l4_anchor"
  using l4_post_anchor_delete_not_covered
  unfolding whole_table_claim_scope_def
  by blast

theorem layer4_post_anchor_delete_not_covered_fixture:
  "virtual_cut b0_ex l4_delete_touch_C l4_delete_touch_H
   \<and> l4_anchor \<le> frontier l4_delete_touch_C
   \<and> anchor_complete_at_boundary
        b0_ex l4_delete_touch_H l4_anchor (scope l4_delete_touch_C)
   \<and> no_unclaimed_replay_keys
        (clean_prefix l4_delete_touch_C) (scope l4_delete_touch_C)
   \<and> (400::nat) \<in> touched_between l4_delete_touch_H l4_anchor
        (frontier l4_delete_touch_C)
   \<and> 400 \<notin> scope l4_delete_touch_C
   \<and> 400 \<notin> replay_keys (clean_prefix l4_delete_touch_C)
   \<and> Apply (clean_prefix l4_delete_touch_C) 400 = None
   \<and> Src b0_ex l4_delete_touch_H
        (frontier l4_delete_touch_C) 400 = None
   \<and> Apply (clean_prefix l4_delete_touch_C)
      = Src b0_ex l4_delete_touch_H (frontier l4_delete_touch_C)
   \<and> \<not> all_post_anchor_changes_covered
        l4_delete_touch_H l4_anchor (frontier l4_delete_touch_C)
        (scope l4_delete_touch_C)
   \<and> \<not> whole_table_claim_scope b0_ex l4_delete_touch_C
        l4_delete_touch_H l4_anchor"
  using l4_delete_touch_virtual_cut
        l4_delete_touch_anchor_le_frontier
        l4_delete_touch_anchor_complete
        l4_delete_touch_no_unclaimed_replay_keys
        l4_delete_touch_key_touched
        l4_delete_touch_key_not_in_scope
        l4_delete_touch_key_not_in_replay_keys
        l4_delete_touch_apply_400
        l4_delete_touch_source_absent_400
        l4_delete_touch_unrestricted_equality
        l4_post_anchor_delete_not_covered
        l4_post_anchor_delete_not_whole_table_claim_scope
  by (simp add: l4_delete_touch_frontier)


section \<open>Empty anchor-domain boundary\<close>

definition l4_empty_b0 :: "nat \<rightharpoonup> nat" where
  "l4_empty_b0 = (\<lambda>_. None)"

definition l4_empty_H :: "(nat, nat) src_history" where
  "l4_empty_H = []"

axiomatization l4_empty_C :: "(nat, nat) cert"
where
  l4_empty_scope:
    "scope l4_empty_C = {}"
and
  l4_empty_frontier:
    "frontier l4_empty_C = ec1"
and
  l4_empty_clean_prefix:
    "clean_prefix l4_empty_C = []"

lemma l4_empty_apply:
  "Apply (clean_prefix l4_empty_C) = (\<lambda>_. None)"
  by (simp add: l4_empty_clean_prefix Apply_def)

lemma l4_empty_source_at_frontier:
  "Src l4_empty_b0 l4_empty_H (frontier l4_empty_C) = (\<lambda>_. None)"
  by (simp add: Src_def latest_src_event_def l4_empty_b0_def
                l4_empty_H_def l4_empty_frontier)

lemma l4_empty_anchor_domain:
  "anchor_domain l4_empty_b0 l4_empty_H l4_anchor = {}"
  by (simp add: anchor_domain_def Src_def latest_src_event_def
                l4_empty_b0_def l4_empty_H_def)

lemma l4_empty_touched_between:
  "touched_between l4_empty_H l4_anchor (frontier l4_empty_C) = {}"
  by (simp add: touched_between_def l4_empty_H_def)

lemma l4_empty_table_scope_between:
  "table_scope_between l4_empty_b0 l4_empty_H l4_anchor
      (frontier l4_empty_C) = {}"
  by (simp add: table_scope_between_def l4_empty_anchor_domain
                l4_empty_touched_between)

lemma l4_empty_replay_keys:
  "replay_keys (clean_prefix l4_empty_C) = {}"
  by (simp add: replay_keys_def l4_empty_clean_prefix)

lemma l4_empty_no_unclaimed_replay_keys:
  "no_unclaimed_replay_keys (clean_prefix l4_empty_C) (scope l4_empty_C)"
  by (simp add: no_unclaimed_replay_keys_def l4_empty_replay_keys
                l4_empty_scope)

lemma l4_empty_anchor_complete:
  "anchor_complete_at_boundary
     l4_empty_b0 l4_empty_H l4_anchor (scope l4_empty_C)"
  by (simp add: anchor_complete_at_boundary_def l4_empty_anchor_domain)

lemma l4_empty_all_post_anchor_changes_covered:
  "all_post_anchor_changes_covered
     l4_empty_H l4_anchor (frontier l4_empty_C) (scope l4_empty_C)"
  by (simp add: all_post_anchor_changes_covered_def
                l4_empty_touched_between)

lemma l4_empty_anchor_le_frontier:
  "l4_anchor \<le> frontier l4_empty_C"
  by (simp add: l4_anchor_def l4_empty_frontier)

lemma l4_empty_unrestricted_equality:
  "Apply (clean_prefix l4_empty_C)
   = Src l4_empty_b0 l4_empty_H (frontier l4_empty_C)"
  using l4_empty_apply l4_empty_source_at_frontier by simp

lemma l4_empty_virtual_cut:
  "virtual_cut l4_empty_b0 l4_empty_C l4_empty_H"
  unfolding virtual_cut_def virtual_cut_state_def
  using l4_empty_unrestricted_equality
  by (simp add: l4_empty_clean_prefix l4_empty_scope l4_empty_frontier)

lemma l4_empty_whole_table_claim_scope:
  "whole_table_claim_scope l4_empty_b0 l4_empty_C l4_empty_H l4_anchor"
  unfolding whole_table_claim_scope_def
  using l4_empty_anchor_le_frontier
        l4_empty_anchor_complete
        l4_empty_all_post_anchor_changes_covered
        l4_empty_no_unclaimed_replay_keys
  by blast

theorem layer4_empty_anchor_domain_boundary_fixture:
  "anchor_domain l4_empty_b0 l4_empty_H l4_anchor = {}
   \<and> touched_between l4_empty_H l4_anchor
        (frontier l4_empty_C) = {}
   \<and> table_scope_between l4_empty_b0 l4_empty_H l4_anchor
        (frontier l4_empty_C) = {}
   \<and> scope l4_empty_C = {}
   \<and> clean_prefix l4_empty_C = []
   \<and> virtual_cut l4_empty_b0 l4_empty_C l4_empty_H
   \<and> whole_table_claim_scope l4_empty_b0 l4_empty_C l4_empty_H l4_anchor
   \<and> Apply (clean_prefix l4_empty_C)
      = Src l4_empty_b0 l4_empty_H (frontier l4_empty_C)"
  using l4_empty_anchor_domain
        l4_empty_touched_between
        l4_empty_table_scope_between
        l4_empty_scope
        l4_empty_clean_prefix
        l4_empty_virtual_cut
        l4_empty_whole_table_claim_scope
        l4_empty_unrestricted_equality
  by simp


section \<open>Claim scope broader than materialized replay coverage\<close>

axiomatization l4_claim_refresh_mismatch_C :: "(nat, nat) cert"
where
  l4_claim_refresh_mismatch_scope:
    "scope l4_claim_refresh_mismatch_C = {100, 200, 300}"
and
  l4_claim_refresh_mismatch_frontier:
    "frontier l4_claim_refresh_mismatch_C = ec4"
and
  l4_claim_refresh_mismatch_clean_prefix:
    "clean_prefix l4_claim_refresh_mismatch_C = l4_missing_insert_prefix"

lemma l4_claim_refresh_mismatch_replay_keys:
  "replay_keys (clean_prefix l4_claim_refresh_mismatch_C) = {100, 200}"
  using l4_missing_insert_replay_keys
  by (simp add: l4_claim_refresh_mismatch_clean_prefix)

lemma l4_claim_refresh_mismatch_claimed_key_not_replayed:
  "(300::nat) \<in> scope l4_claim_refresh_mismatch_C
   \<and> 300 \<notin> replay_keys (clean_prefix l4_claim_refresh_mismatch_C)"
  by (simp add: l4_claim_refresh_mismatch_scope
                l4_claim_refresh_mismatch_replay_keys)

lemma l4_claim_refresh_mismatch_no_unclaimed_replay_keys:
  "no_unclaimed_replay_keys
     (clean_prefix l4_claim_refresh_mismatch_C)
     (scope l4_claim_refresh_mismatch_C)"
  unfolding no_unclaimed_replay_keys_def
  by (simp add: l4_claim_refresh_mismatch_replay_keys
                l4_claim_refresh_mismatch_scope)

lemma l4_claim_refresh_mismatch_anchor_domain:
  "anchor_domain b0_ex H_ex l4_anchor = {100, 200}"
  by (rule l4_anchor_domain)

lemma l4_claim_refresh_mismatch_anchor_complete:
  "anchor_complete_at_boundary b0_ex H_ex l4_anchor
     (scope l4_claim_refresh_mismatch_C)"
  unfolding anchor_complete_at_boundary_def
  using l4_claim_refresh_mismatch_anchor_domain
  by (simp add: l4_claim_refresh_mismatch_scope)

lemma l4_claim_refresh_mismatch_touched_between:
  "touched_between H_ex l4_anchor
     (frontier l4_claim_refresh_mismatch_C) = {200, 300}"
  using l4_touched_between
  by (simp add: l4_claim_refresh_mismatch_frontier
                l3_frontier ex_frontier)

lemma l4_claim_refresh_mismatch_all_post_anchor_changes_covered:
  "all_post_anchor_changes_covered
     H_ex l4_anchor (frontier l4_claim_refresh_mismatch_C)
     (scope l4_claim_refresh_mismatch_C)"
  unfolding all_post_anchor_changes_covered_def
  using l4_claim_refresh_mismatch_touched_between
  by (simp add: l4_claim_refresh_mismatch_scope)

lemma l4_claim_refresh_mismatch_anchor_le_frontier:
  "l4_anchor \<le> frontier l4_claim_refresh_mismatch_C"
  using ec1_le_ec4
  by (simp add: l4_anchor_def l4_claim_refresh_mismatch_frontier
                less_eq_src_coord_def)

lemma l4_claim_refresh_mismatch_whole_table_claim_scope:
  "whole_table_claim_scope b0_ex l4_claim_refresh_mismatch_C H_ex l4_anchor"
  unfolding whole_table_claim_scope_def
  using l4_claim_refresh_mismatch_anchor_le_frontier
        l4_claim_refresh_mismatch_anchor_complete
        l4_claim_refresh_mismatch_all_post_anchor_changes_covered
        l4_claim_refresh_mismatch_no_unclaimed_replay_keys
  by blast

lemma l4_claim_refresh_mismatch_replay_absent_300:
  "Apply (clean_prefix l4_claim_refresh_mismatch_C) (300::nat) = None"
  using l4_missing_insert_apply_300
  by (simp add: l4_claim_refresh_mismatch_clean_prefix)

lemma l4_claim_refresh_mismatch_source_present_300:
  "Src b0_ex H_ex (frontier l4_claim_refresh_mismatch_C) (300::nat)
     = Some 3500"
  using Src_b0_ex_H_ex_ec4_300
  by (simp add: l4_claim_refresh_mismatch_frontier)

theorem l4_claim_refresh_mismatch_not_virtual_cut:
  "\<not> virtual_cut b0_ex l4_claim_refresh_mismatch_C H_ex"
proof
  assume vc: "virtual_cut b0_ex l4_claim_refresh_mismatch_C H_ex"
  hence restricted_eq:
    "restrict (Apply (clean_prefix l4_claim_refresh_mismatch_C))
       (scope l4_claim_refresh_mismatch_C)
     = restrict (Src b0_ex H_ex (frontier l4_claim_refresh_mismatch_C))
       (scope l4_claim_refresh_mismatch_C)"
    unfolding virtual_cut_def virtual_cut_state_def restrict_def
    by simp
  hence "restrict (Apply (clean_prefix l4_claim_refresh_mismatch_C))
          (scope l4_claim_refresh_mismatch_C) (300::nat)
       = restrict (Src b0_ex H_ex (frontier l4_claim_refresh_mismatch_C))
          (scope l4_claim_refresh_mismatch_C) 300"
    by simp
  hence "Apply (clean_prefix l4_claim_refresh_mismatch_C) (300::nat)
       = Src b0_ex H_ex (frontier l4_claim_refresh_mismatch_C) 300"
    by (simp add: restrict_def l4_claim_refresh_mismatch_scope)
  thus False
    using l4_claim_refresh_mismatch_replay_absent_300
          l4_claim_refresh_mismatch_source_present_300
    by simp
qed

theorem l4_claim_refresh_mismatch_unrestricted_equality_fails:
  "Apply (clean_prefix l4_claim_refresh_mismatch_C)
   \<noteq> Src b0_ex H_ex (frontier l4_claim_refresh_mismatch_C)"
proof
  assume eq:
    "Apply (clean_prefix l4_claim_refresh_mismatch_C)
     = Src b0_ex H_ex (frontier l4_claim_refresh_mismatch_C)"
  hence "Apply (clean_prefix l4_claim_refresh_mismatch_C) (300::nat)
       = Src b0_ex H_ex (frontier l4_claim_refresh_mismatch_C) 300"
    by simp
  thus False
    using l4_claim_refresh_mismatch_replay_absent_300
          l4_claim_refresh_mismatch_source_present_300
    by simp
qed

theorem layer4_claim_refresh_scope_mismatch_fixture:
  "scope l4_claim_refresh_mismatch_C = {100, 200, 300}
   \<and> replay_keys (clean_prefix l4_claim_refresh_mismatch_C) = {100, 200}
   \<and> (300::nat) \<in> scope l4_claim_refresh_mismatch_C
   \<and> 300 \<notin> replay_keys (clean_prefix l4_claim_refresh_mismatch_C)
   \<and> anchor_complete_at_boundary b0_ex H_ex l4_anchor
        (scope l4_claim_refresh_mismatch_C)
   \<and> all_post_anchor_changes_covered H_ex l4_anchor
        (frontier l4_claim_refresh_mismatch_C)
        (scope l4_claim_refresh_mismatch_C)
   \<and> no_unclaimed_replay_keys
        (clean_prefix l4_claim_refresh_mismatch_C)
        (scope l4_claim_refresh_mismatch_C)
   \<and> whole_table_claim_scope b0_ex l4_claim_refresh_mismatch_C
        H_ex l4_anchor
   \<and> \<not> virtual_cut b0_ex l4_claim_refresh_mismatch_C H_ex
   \<and> Apply (clean_prefix l4_claim_refresh_mismatch_C) 300 = None
   \<and> Src b0_ex H_ex (frontier l4_claim_refresh_mismatch_C) 300 = Some 3500
   \<and> Apply (clean_prefix l4_claim_refresh_mismatch_C)
      \<noteq> Src b0_ex H_ex (frontier l4_claim_refresh_mismatch_C)"
  using l4_claim_refresh_mismatch_scope
        l4_claim_refresh_mismatch_replay_keys
        l4_claim_refresh_mismatch_claimed_key_not_replayed
        l4_claim_refresh_mismatch_anchor_complete
        l4_claim_refresh_mismatch_all_post_anchor_changes_covered
        l4_claim_refresh_mismatch_no_unclaimed_replay_keys
        l4_claim_refresh_mismatch_whole_table_claim_scope
        l4_claim_refresh_mismatch_not_virtual_cut
        l4_claim_refresh_mismatch_replay_absent_300
        l4_claim_refresh_mismatch_source_present_300
        l4_claim_refresh_mismatch_unrestricted_equality_fails
  by simp


section \<open>Anchor boundary after certified frontier\<close>

definition l4_after_frontier_b0 :: "nat \<rightharpoonup> nat" where
  "l4_after_frontier_b0 = (\<lambda>_. None)"

definition l4_after_frontier_H :: "(nat, nat) src_history" where
  "l4_after_frontier_H =
     [ (ec1, Insert (500::nat) (9000::nat)),
       (ec2, Delete (500::nat)) ]"

definition l4_after_frontier_anchor :: frontier where
  "l4_after_frontier_anchor = ec2"

axiomatization l4_after_frontier_C :: "(nat, nat) cert"
where
  l4_after_frontier_scope:
    "scope l4_after_frontier_C = {}"
and
  l4_after_frontier_frontier:
    "frontier l4_after_frontier_C = ec1"
and
  l4_after_frontier_clean_prefix:
    "clean_prefix l4_after_frontier_C = []"

lemma latest_src_event_l4_after_frontier_ec1_500:
  "latest_src_event l4_after_frontier_H ec1 (500::nat) = Some 0"
  unfolding latest_src_event_def l4_after_frontier_H_def
  using src_le_refl[where c=ec1] not_src_le_ec2_ec1
  by simp

lemma latest_src_event_l4_after_frontier_ec2_500:
  "latest_src_event l4_after_frontier_H ec2 (500::nat) = Some 1"
  unfolding latest_src_event_def l4_after_frontier_H_def
  using ec1_le_ec2 src_le_refl[where c=ec2]
  by simp

lemma latest_src_event_l4_after_frontier_ec2_other:
  assumes "k \<noteq> (500::nat)"
  shows "latest_src_event l4_after_frontier_H ec2 k = None"
  unfolding latest_src_event_def l4_after_frontier_H_def
  using assms
  by simp

lemma l4_after_frontier_source_present_at_frontier:
  "Src l4_after_frontier_b0 l4_after_frontier_H
      (frontier l4_after_frontier_C) (500::nat) = Some 9000"
  unfolding Src_def
  using latest_src_event_l4_after_frontier_ec1_500
  by (simp add: l4_after_frontier_H_def l4_after_frontier_frontier)

lemma l4_after_frontier_source_absent_at_anchor_500:
  "Src l4_after_frontier_b0 l4_after_frontier_H
      l4_after_frontier_anchor (500::nat) = None"
  unfolding Src_def
  using latest_src_event_l4_after_frontier_ec2_500
  by (simp add: l4_after_frontier_H_def l4_after_frontier_anchor_def)

lemma l4_after_frontier_source_absent_at_anchor_other:
  assumes "k \<noteq> (500::nat)"
  shows "Src l4_after_frontier_b0 l4_after_frontier_H
      l4_after_frontier_anchor k = None"
  unfolding Src_def l4_after_frontier_b0_def
  using latest_src_event_l4_after_frontier_ec2_other[OF assms]
  by (simp add: l4_after_frontier_anchor_def)

lemma l4_after_frontier_source_at_anchor_empty:
  "Src l4_after_frontier_b0 l4_after_frontier_H
      l4_after_frontier_anchor = (\<lambda>_. None)"
proof
  fix k :: nat
  show "Src l4_after_frontier_b0 l4_after_frontier_H
          l4_after_frontier_anchor k = None"
  proof (cases "k = 500")
    case True
    thus ?thesis using l4_after_frontier_source_absent_at_anchor_500
      by simp
  next
    case False
    thus ?thesis using l4_after_frontier_source_absent_at_anchor_other
      by simp
  qed
qed

lemma l4_after_frontier_anchor_domain_empty:
  "anchor_domain l4_after_frontier_b0 l4_after_frontier_H
     l4_after_frontier_anchor = {}"
  by (simp add: anchor_domain_def l4_after_frontier_source_at_anchor_empty)

lemma l4_after_frontier_touched_between_empty:
  "touched_between l4_after_frontier_H l4_after_frontier_anchor
      (frontier l4_after_frontier_C) = {}"
  unfolding touched_between_def l4_after_frontier_H_def
            l4_after_frontier_anchor_def l4_after_frontier_frontier
  using not_src_le_ec2_ec1
  by (auto simp: less_src_coord_def src_lt_def less_eq_src_coord_def)

lemma l4_after_frontier_table_scope_between_empty:
  "table_scope_between l4_after_frontier_b0 l4_after_frontier_H
      l4_after_frontier_anchor (frontier l4_after_frontier_C) = {}"
  by (simp add: table_scope_between_def
                l4_after_frontier_anchor_domain_empty
                l4_after_frontier_touched_between_empty)

lemma l4_after_frontier_key_not_in_table_scope:
  "(500::nat) \<notin> table_scope_between l4_after_frontier_b0
      l4_after_frontier_H l4_after_frontier_anchor
      (frontier l4_after_frontier_C)"
  by (simp add: l4_after_frontier_table_scope_between_empty)

lemma l4_after_frontier_anchor_not_le_frontier:
  "\<not> l4_after_frontier_anchor \<le> frontier l4_after_frontier_C"
  using not_src_le_ec2_ec1
  by (simp add: l4_after_frontier_anchor_def
                l4_after_frontier_frontier
                less_eq_src_coord_def)

lemma l4_after_frontier_anchor_complete:
  "anchor_complete_at_boundary
     l4_after_frontier_b0 l4_after_frontier_H l4_after_frontier_anchor
     (scope l4_after_frontier_C)"
  by (simp add: anchor_complete_at_boundary_def
                l4_after_frontier_anchor_domain_empty
                l4_after_frontier_scope)

lemma l4_after_frontier_all_post_anchor_changes_covered:
  "all_post_anchor_changes_covered l4_after_frontier_H
     l4_after_frontier_anchor (frontier l4_after_frontier_C)
     (scope l4_after_frontier_C)"
  by (simp add: all_post_anchor_changes_covered_def
                l4_after_frontier_touched_between_empty
                l4_after_frontier_scope)

lemma l4_after_frontier_no_unclaimed_replay_keys:
  "no_unclaimed_replay_keys
     (clean_prefix l4_after_frontier_C) (scope l4_after_frontier_C)"
  by (simp add: no_unclaimed_replay_keys_def replay_keys_def
                l4_after_frontier_clean_prefix l4_after_frontier_scope)

lemma l4_after_frontier_apply:
  "Apply (clean_prefix l4_after_frontier_C) = (\<lambda>_. None)"
  by (simp add: Apply_def l4_after_frontier_clean_prefix)

lemma l4_after_frontier_virtual_cut:
  "virtual_cut l4_after_frontier_b0 l4_after_frontier_C
     l4_after_frontier_H"
  unfolding virtual_cut_def virtual_cut_state_def restrict_def
  by (simp add: l4_after_frontier_clean_prefix
                l4_after_frontier_scope
                l4_after_frontier_frontier)

theorem l4_after_frontier_not_whole_table_claim_scope:
  "\<not> whole_table_claim_scope l4_after_frontier_b0 l4_after_frontier_C
        l4_after_frontier_H l4_after_frontier_anchor"
  using l4_after_frontier_anchor_not_le_frontier
  unfolding whole_table_claim_scope_def
  by blast

theorem l4_after_frontier_unrestricted_equality_fails:
  "Apply (clean_prefix l4_after_frontier_C)
   \<noteq> Src l4_after_frontier_b0 l4_after_frontier_H
        (frontier l4_after_frontier_C)"
proof
  assume eq:
    "Apply (clean_prefix l4_after_frontier_C)
     = Src l4_after_frontier_b0 l4_after_frontier_H
        (frontier l4_after_frontier_C)"
  hence "Apply (clean_prefix l4_after_frontier_C) (500::nat)
       = Src l4_after_frontier_b0 l4_after_frontier_H
          (frontier l4_after_frontier_C) 500"
    by simp
  thus False
    using l4_after_frontier_apply
          l4_after_frontier_source_present_at_frontier
    by simp
qed

theorem layer4_anchor_after_frontier_fixture:
  "scope l4_after_frontier_C = {}
   \<and> clean_prefix l4_after_frontier_C = []
   \<and> frontier l4_after_frontier_C = ec1
   \<and> l4_after_frontier_anchor = ec2
   \<and> \<not> l4_after_frontier_anchor \<le> frontier l4_after_frontier_C
   \<and> anchor_domain l4_after_frontier_b0 l4_after_frontier_H
        l4_after_frontier_anchor = {}
   \<and> touched_between l4_after_frontier_H l4_after_frontier_anchor
        (frontier l4_after_frontier_C) = {}
   \<and> table_scope_between l4_after_frontier_b0 l4_after_frontier_H
        l4_after_frontier_anchor (frontier l4_after_frontier_C) = {}
   \<and> (500::nat) \<notin> table_scope_between l4_after_frontier_b0
        l4_after_frontier_H l4_after_frontier_anchor
        (frontier l4_after_frontier_C)
   \<and> anchor_complete_at_boundary l4_after_frontier_b0 l4_after_frontier_H
        l4_after_frontier_anchor (scope l4_after_frontier_C)
   \<and> all_post_anchor_changes_covered l4_after_frontier_H
        l4_after_frontier_anchor (frontier l4_after_frontier_C)
        (scope l4_after_frontier_C)
   \<and> no_unclaimed_replay_keys
        (clean_prefix l4_after_frontier_C) (scope l4_after_frontier_C)
   \<and> virtual_cut l4_after_frontier_b0 l4_after_frontier_C
        l4_after_frontier_H
   \<and> \<not> whole_table_claim_scope l4_after_frontier_b0 l4_after_frontier_C
        l4_after_frontier_H l4_after_frontier_anchor
   \<and> Apply (clean_prefix l4_after_frontier_C) 500 = None
   \<and> Src l4_after_frontier_b0 l4_after_frontier_H
        (frontier l4_after_frontier_C) 500 = Some 9000
   \<and> Src l4_after_frontier_b0 l4_after_frontier_H
        l4_after_frontier_anchor 500 = None
   \<and> Apply (clean_prefix l4_after_frontier_C)
      \<noteq> Src l4_after_frontier_b0 l4_after_frontier_H
           (frontier l4_after_frontier_C)"
  using l4_after_frontier_scope
        l4_after_frontier_clean_prefix
        l4_after_frontier_frontier
        l4_after_frontier_anchor_def
        l4_after_frontier_anchor_not_le_frontier
        l4_after_frontier_anchor_domain_empty
        l4_after_frontier_touched_between_empty
        l4_after_frontier_table_scope_between_empty
        l4_after_frontier_key_not_in_table_scope
        l4_after_frontier_anchor_complete
        l4_after_frontier_all_post_anchor_changes_covered
        l4_after_frontier_no_unclaimed_replay_keys
        l4_after_frontier_virtual_cut
        l4_after_frontier_not_whole_table_claim_scope
        l4_after_frontier_apply
        l4_after_frontier_source_present_at_frontier
        l4_after_frontier_source_absent_at_anchor_500
        l4_after_frontier_unrestricted_equality_fails
  by simp


section \<open>Post-anchor update materialized by a later refresh\<close>

definition l4_update_refresh_prefix :: "(nat, nat) replay_event list" where
  "l4_update_refresh_prefix =
     [ Cdc ec1 (Update (100::nat) (3000::nat)),
       Refresh 100 (Some 3000) ec1,
       Refresh 200 (Some 12000) ec4,
       Cdc ec2 (Insert 300 2500),
       Cdc ec4 (Update 300 3500) ]"

axiomatization l4_update_refresh_C :: "(nat, nat) cert"
where
  l4_update_refresh_scope:
    "scope l4_update_refresh_C = {100, 200, 300}"
and
  l4_update_refresh_frontier:
    "frontier l4_update_refresh_C = ec4"
and
  l4_update_refresh_clean_prefix:
    "clean_prefix l4_update_refresh_C = l4_update_refresh_prefix"

lemma l4_update_refresh_apply_100:
  "Apply l4_update_refresh_prefix (100::nat) = Some 3000"
  unfolding l4_update_refresh_prefix_def Apply_def by simp

lemma l4_update_refresh_apply_200:
  "Apply l4_update_refresh_prefix (200::nat) = Some 12000"
  unfolding l4_update_refresh_prefix_def Apply_def by simp

lemma l4_update_refresh_apply_300:
  "Apply l4_update_refresh_prefix (300::nat) = Some 3500"
  unfolding l4_update_refresh_prefix_def Apply_def by simp

lemma l4_update_refresh_replay_keys:
  "replay_keys (clean_prefix l4_update_refresh_C) = {100, 200, 300}"
  unfolding replay_keys_def
  by (auto simp: l4_update_refresh_clean_prefix
                 l4_update_refresh_prefix_def)

lemma l4_update_refresh_no_unclaimed_replay_keys:
  "no_unclaimed_replay_keys
     (clean_prefix l4_update_refresh_C) (scope l4_update_refresh_C)"
  unfolding no_unclaimed_replay_keys_def
  using l4_update_refresh_replay_keys
  by (simp add: l4_update_refresh_scope)

lemma l4_update_refresh_scoped_virtual_cut_state:
  "virtual_cut_state b0_ex l4_update_refresh_prefix {100, 200, 300} ec4 H_ex"
  unfolding virtual_cut_state_def restrict_def
proof (rule ext)
  fix k :: nat
  show "(if k \<in> {100, 200, 300} then Apply l4_update_refresh_prefix k else None)
      = (if k \<in> {100, 200, 300} then Src b0_ex H_ex ec4 k else None)"
  proof (cases "k = 100")
    case True
    thus ?thesis
      using l4_update_refresh_apply_100 Src_b0_ex_H_ex_ec4_100 by simp
  next
    case not100: False
    show ?thesis
    proof (cases "k = 200")
      case True
      thus ?thesis
        using l4_update_refresh_apply_200 Src_b0_ex_H_ex_ec4_200 by simp
    next
      case not200: False
      show ?thesis
      proof (cases "k = 300")
        case True
        thus ?thesis
          using l4_update_refresh_apply_300 Src_b0_ex_H_ex_ec4_300 by simp
      next
        case False
        with not100 not200 show ?thesis by simp
      qed
    qed
  qed
qed

lemma l4_update_refresh_virtual_cut:
  "virtual_cut b0_ex l4_update_refresh_C H_ex"
  unfolding virtual_cut_def
  using l4_update_refresh_scoped_virtual_cut_state
  by (simp add: l4_update_refresh_clean_prefix
                l4_update_refresh_scope
                l4_update_refresh_frontier)

lemma l4_update_refresh_anchor_complete:
  "anchor_complete_at_boundary b0_ex H_ex l4_anchor
     (scope l4_update_refresh_C)"
  unfolding anchor_complete_at_boundary_def
  using l4_anchor_domain
  by (simp add: l4_update_refresh_scope)

lemma l4_update_refresh_all_post_anchor_changes_covered:
  "all_post_anchor_changes_covered H_ex l4_anchor
     (frontier l4_update_refresh_C) (scope l4_update_refresh_C)"
  unfolding all_post_anchor_changes_covered_def
  using l4_touched_between
  by (simp add: l4_update_refresh_frontier l3_frontier ex_frontier
                l4_update_refresh_scope)

lemma l4_update_refresh_anchor_le_frontier:
  "l4_anchor \<le> frontier l4_update_refresh_C"
  using ec1_le_ec4
  by (simp add: l4_anchor_def l4_update_refresh_frontier
                less_eq_src_coord_def)

lemma l4_update_refresh_whole_table_claim_scope:
  "whole_table_claim_scope b0_ex l4_update_refresh_C H_ex l4_anchor"
  unfolding whole_table_claim_scope_def
  using l4_update_refresh_anchor_le_frontier
        l4_update_refresh_anchor_complete
        l4_update_refresh_all_post_anchor_changes_covered
        l4_update_refresh_no_unclaimed_replay_keys
  by blast

lemma l4_update_refresh_key_200_anchor_domain:
  "(200::nat) \<in> anchor_domain b0_ex H_ex l4_anchor"
  using l4_anchor_domain by simp

lemma l4_update_refresh_key_200_touched:
  "(200::nat) \<in> touched_between H_ex l4_anchor
     (frontier l4_update_refresh_C)"
  using l4_touched_between
  by (simp add: l4_update_refresh_frontier l3_frontier ex_frontier)

lemma l4_update_refresh_key_200_in_scope:
  "(200::nat) \<in> scope l4_update_refresh_C"
  by (simp add: l4_update_refresh_scope)

lemma l4_update_refresh_refresh_for_200:
  "Refresh (200::nat) (Some (12000::nat)) ec4
     \<in> set (clean_prefix l4_update_refresh_C)"
  by (simp add: l4_update_refresh_clean_prefix
                l4_update_refresh_prefix_def)

lemma l4_update_refresh_no_cdc_update_for_200:
  "Cdc ec3 (Update (200::nat) (12000::nat))
     \<notin> set (clean_prefix l4_update_refresh_C)"
  by (simp add: l4_update_refresh_clean_prefix
                l4_update_refresh_prefix_def)

lemma l4_update_refresh_source_update_before_refresh:
  "(ec3, Update (200::nat) (12000::nat)) \<in> set H_ex
   \<and> ec3 < ec4"
  using ec3_lt_ec4
  by (simp add: H_ex_def less_src_coord_def)

theorem l4_update_refresh_unrestricted_equality:
  "Apply (clean_prefix l4_update_refresh_C)
   = Src b0_ex H_ex (frontier l4_update_refresh_C)"
  by (rule whole_table_equality_from_claim_scope
      [OF l4_update_refresh_virtual_cut
          l4_update_refresh_whole_table_claim_scope])

theorem layer4_post_anchor_update_before_read_fixture:
  "virtual_cut b0_ex l4_update_refresh_C H_ex
   \<and> whole_table_claim_scope b0_ex l4_update_refresh_C H_ex l4_anchor
   \<and> no_unclaimed_replay_keys
        (clean_prefix l4_update_refresh_C) (scope l4_update_refresh_C)
   \<and> anchor_complete_at_boundary b0_ex H_ex l4_anchor
        (scope l4_update_refresh_C)
   \<and> all_post_anchor_changes_covered H_ex l4_anchor
        (frontier l4_update_refresh_C) (scope l4_update_refresh_C)
   \<and> (200::nat) \<in> anchor_domain b0_ex H_ex l4_anchor
   \<and> 200 \<in> touched_between H_ex l4_anchor (frontier l4_update_refresh_C)
   \<and> 200 \<in> scope l4_update_refresh_C
   \<and> Refresh 200 (Some 12000) ec4
        \<in> set (clean_prefix l4_update_refresh_C)
   \<and> Cdc ec3 (Update 200 12000)
        \<notin> set (clean_prefix l4_update_refresh_C)
   \<and> (ec3, Update 200 12000) \<in> set H_ex
   \<and> ec3 < ec4
   \<and> Apply (clean_prefix l4_update_refresh_C) 200 = Some 12000
   \<and> Src b0_ex H_ex (frontier l4_update_refresh_C) 200 = Some 12000
   \<and> Apply (clean_prefix l4_update_refresh_C)
      = Src b0_ex H_ex (frontier l4_update_refresh_C)"
  using l4_update_refresh_virtual_cut
        l4_update_refresh_whole_table_claim_scope
        l4_update_refresh_no_unclaimed_replay_keys
        l4_update_refresh_anchor_complete
        l4_update_refresh_all_post_anchor_changes_covered
        l4_update_refresh_key_200_anchor_domain
        l4_update_refresh_key_200_touched
        l4_update_refresh_key_200_in_scope
        l4_update_refresh_refresh_for_200
        l4_update_refresh_no_cdc_update_for_200
        l4_update_refresh_source_update_before_refresh
        l4_update_refresh_apply_200
        Src_b0_ex_H_ex_ec4_200
        l4_update_refresh_unrestricted_equality
  by (simp add: l4_update_refresh_clean_prefix
                l4_update_refresh_frontier)


section \<open>No-unclaimed replay-key failure\<close>

definition l4_unclaimed_prefix :: "(nat, nat) replay_event list" where
  "l4_unclaimed_prefix =
     [ Cdc ec1 (Update (100::nat) (3000::nat)),
       Refresh 100 (Some 3000) ec1,
       Refresh 200 (Some 10000) ec1,
       Cdc ec2 (Insert 300 2500),
       Cdc ec3 (Update 200 12000),
       Refresh 300 (Some 2500) ec3,
       Cdc ec4 (Update 300 3500),
       Refresh 999 (Some 4242) ec4 ]"

axiomatization l4_unclaimed_C :: "(nat, nat) cert"
where
  l4_unclaimed_scope:
    "scope l4_unclaimed_C = {100, 200, 300}"
and
  l4_unclaimed_frontier:
    "frontier l4_unclaimed_C = ec4"
and
  l4_unclaimed_clean_prefix:
    "clean_prefix l4_unclaimed_C = l4_unclaimed_prefix"

lemma l4_unclaimed_apply_100:
  "Apply l4_unclaimed_prefix (100::nat) = Some 3000"
  unfolding l4_unclaimed_prefix_def Apply_def by simp

lemma l4_unclaimed_apply_200:
  "Apply l4_unclaimed_prefix (200::nat) = Some 12000"
  unfolding l4_unclaimed_prefix_def Apply_def by simp

lemma l4_unclaimed_apply_300:
  "Apply l4_unclaimed_prefix (300::nat) = Some 3500"
  unfolding l4_unclaimed_prefix_def Apply_def by simp

lemma l4_unclaimed_apply_999:
  "Apply l4_unclaimed_prefix (999::nat) = Some 4242"
  unfolding l4_unclaimed_prefix_def Apply_def by simp

lemma l4_unclaimed_replay_keys:
  "replay_keys (clean_prefix l4_unclaimed_C) = {100, 200, 300, 999}"
  unfolding replay_keys_def
  by (auto simp: l4_unclaimed_clean_prefix l4_unclaimed_prefix_def)

theorem l4_unclaimed_no_unclaimed_replay_keys_fails:
  "\<not> no_unclaimed_replay_keys
        (clean_prefix l4_unclaimed_C) (scope l4_unclaimed_C)"
  unfolding no_unclaimed_replay_keys_def
  using l4_unclaimed_replay_keys
  by (simp add: l4_unclaimed_scope)

lemma l4_unclaimed_scoped_virtual_cut_state:
  "virtual_cut_state b0_ex l4_unclaimed_prefix {100, 200, 300} ec4 H_ex"
  unfolding virtual_cut_state_def restrict_def
proof (rule ext)
  fix k :: nat
  show "(if k \<in> {100, 200, 300} then Apply l4_unclaimed_prefix k else None)
      = (if k \<in> {100, 200, 300} then Src b0_ex H_ex ec4 k else None)"
  proof (cases "k = 100")
    case True
    thus ?thesis
      using l4_unclaimed_apply_100 Src_b0_ex_H_ex_ec4_100 by simp
  next
    case not100: False
    show ?thesis
    proof (cases "k = 200")
      case True
      thus ?thesis
        using l4_unclaimed_apply_200 Src_b0_ex_H_ex_ec4_200 by simp
    next
      case not200: False
      show ?thesis
      proof (cases "k = 300")
        case True
        thus ?thesis
          using l4_unclaimed_apply_300 Src_b0_ex_H_ex_ec4_300 by simp
      next
        case False
        with not100 not200 show ?thesis by simp
      qed
    qed
  qed
qed

lemma l4_unclaimed_virtual_cut:
  "virtual_cut b0_ex l4_unclaimed_C H_ex"
  unfolding virtual_cut_def
  using l4_unclaimed_scoped_virtual_cut_state
  by (simp add: l4_unclaimed_clean_prefix
                l4_unclaimed_scope
                l4_unclaimed_frontier)

lemma l4_unclaimed_anchor_complete:
  "anchor_complete_at_boundary b0_ex H_ex l4_anchor
     (scope l4_unclaimed_C)"
  unfolding anchor_complete_at_boundary_def
  using l4_anchor_domain
  by (simp add: l4_unclaimed_scope)

lemma l4_unclaimed_all_post_anchor_changes_covered:
  "all_post_anchor_changes_covered H_ex l4_anchor
     (frontier l4_unclaimed_C) (scope l4_unclaimed_C)"
  unfolding all_post_anchor_changes_covered_def
  using l4_touched_between
  by (simp add: l4_unclaimed_frontier l3_frontier ex_frontier
                l4_unclaimed_scope)

lemma l4_unclaimed_anchor_le_frontier:
  "l4_anchor \<le> frontier l4_unclaimed_C"
  using ec1_le_ec4
  by (simp add: l4_anchor_def l4_unclaimed_frontier
                less_eq_src_coord_def)

lemma l4_unclaimed_table_scope_between:
  "table_scope_between b0_ex H_ex l4_anchor (frontier l4_unclaimed_C)
     = scope l4_unclaimed_C"
  using l4_table_scope_between
  by (simp add: l4_unclaimed_frontier l4_unclaimed_scope
                l3_frontier ex_frontier l3_scope ex_scope)

theorem l4_unclaimed_not_whole_table_claim_scope:
  "\<not> whole_table_claim_scope b0_ex l4_unclaimed_C H_ex l4_anchor"
  using l4_unclaimed_no_unclaimed_replay_keys_fails
  unfolding whole_table_claim_scope_def
  by blast

lemma l4_unclaimed_refresh_for_999:
  "Refresh (999::nat) (Some (4242::nat)) ec4
     \<in> set (clean_prefix l4_unclaimed_C)"
  by (simp add: l4_unclaimed_clean_prefix l4_unclaimed_prefix_def)

lemma l4_unclaimed_key_999_not_in_scope:
  "(999::nat) \<notin> scope l4_unclaimed_C"
  by (simp add: l4_unclaimed_scope)

lemma l4_unclaimed_apply_999_clean_prefix:
  "Apply (clean_prefix l4_unclaimed_C) (999::nat) = Some 4242"
  using l4_unclaimed_apply_999
  by (simp add: l4_unclaimed_clean_prefix)

lemma l4_unclaimed_source_absent_999:
  "Src b0_ex H_ex (frontier l4_unclaimed_C) (999::nat) = None"
  using l4_outside_source_absent
  by (simp add: l4_unclaimed_frontier l3_frontier ex_frontier)

theorem l4_unclaimed_unrestricted_equality_fails:
  "Apply (clean_prefix l4_unclaimed_C)
   \<noteq> Src b0_ex H_ex (frontier l4_unclaimed_C)"
proof
  assume eq:
    "Apply (clean_prefix l4_unclaimed_C)
     = Src b0_ex H_ex (frontier l4_unclaimed_C)"
  hence "Apply (clean_prefix l4_unclaimed_C) (999::nat)
       = Src b0_ex H_ex (frontier l4_unclaimed_C) 999"
    by simp
  thus False
    using l4_unclaimed_apply_999_clean_prefix
          l4_unclaimed_source_absent_999
    by simp
qed

theorem layer4_no_unclaimed_signature_determinacy_fixture:
  "virtual_cut b0_ex l4_unclaimed_C H_ex
   \<and> l4_anchor \<le> frontier l4_unclaimed_C
   \<and> anchor_complete_at_boundary b0_ex H_ex l4_anchor
        (scope l4_unclaimed_C)
   \<and> all_post_anchor_changes_covered H_ex l4_anchor
        (frontier l4_unclaimed_C) (scope l4_unclaimed_C)
   \<and> table_scope_between b0_ex H_ex l4_anchor (frontier l4_unclaimed_C)
        = scope l4_unclaimed_C
   \<and> replay_keys (clean_prefix l4_unclaimed_C) = {100, 200, 300, 999}
   \<and> Refresh 999 (Some 4242) ec4 \<in> set (clean_prefix l4_unclaimed_C)
   \<and> 999 \<notin> scope l4_unclaimed_C
   \<and> \<not> no_unclaimed_replay_keys
        (clean_prefix l4_unclaimed_C) (scope l4_unclaimed_C)
   \<and> \<not> whole_table_claim_scope b0_ex l4_unclaimed_C H_ex l4_anchor
   \<and> Apply (clean_prefix l4_unclaimed_C) 999 = Some 4242
   \<and> Src b0_ex H_ex (frontier l4_unclaimed_C) 999 = None
   \<and> Apply (clean_prefix l4_unclaimed_C)
      \<noteq> Src b0_ex H_ex (frontier l4_unclaimed_C)"
  using l4_unclaimed_virtual_cut
        l4_unclaimed_anchor_le_frontier
        l4_unclaimed_anchor_complete
        l4_unclaimed_all_post_anchor_changes_covered
        l4_unclaimed_table_scope_between
        l4_unclaimed_replay_keys
        l4_unclaimed_refresh_for_999
        l4_unclaimed_key_999_not_in_scope
        l4_unclaimed_no_unclaimed_replay_keys_fails
        l4_unclaimed_not_whole_table_claim_scope
        l4_unclaimed_apply_999_clean_prefix
        l4_unclaimed_source_absent_999
        l4_unclaimed_unrestricted_equality_fails
  by simp


section \<open>b0 base-state contribution to the anchor domain\<close>

definition l4_b0_anchor_b0 :: "nat \<rightharpoonup> nat" where
  "l4_b0_anchor_b0 = (\<lambda>k. if k = (700::nat) then Some (7000::nat) else None)"

definition l4_b0_anchor_H :: "(nat, nat) src_history" where
  "l4_b0_anchor_H = []"

definition l4_b0_anchor_prefix :: "(nat, nat) replay_event list" where
  "l4_b0_anchor_prefix =
     [Refresh (700::nat) (Some (7000::nat)) ec1]"

axiomatization l4_b0_anchor_C :: "(nat, nat) cert"
where
  l4_b0_anchor_scope:
    "scope l4_b0_anchor_C = {700}"
and
  l4_b0_anchor_frontier:
    "frontier l4_b0_anchor_C = ec4"
and
  l4_b0_anchor_clean_prefix:
    "clean_prefix l4_b0_anchor_C = l4_b0_anchor_prefix"

lemma l4_b0_anchor_base_key_present:
  "l4_b0_anchor_b0 (700::nat) = Some 7000"
  by (simp add: l4_b0_anchor_b0_def)

lemma l4_b0_anchor_no_source_event_for_key:
  "latest_src_event l4_b0_anchor_H l4_anchor (700::nat) = None"
  by (simp add: latest_src_event_def l4_b0_anchor_H_def)

lemma l4_b0_anchor_source_at_anchor:
  "Src l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor = l4_b0_anchor_b0"
  by (rule ext) (simp add: Src_def latest_src_event_def
                            l4_b0_anchor_H_def)

lemma l4_b0_anchor_source_at_frontier:
  "Src l4_b0_anchor_b0 l4_b0_anchor_H (frontier l4_b0_anchor_C)
     = l4_b0_anchor_b0"
  by (rule ext) (simp add: Src_def latest_src_event_def
                            l4_b0_anchor_H_def)

lemma l4_b0_anchor_source_key_at_anchor:
  "Src l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor (700::nat)
     = Some 7000"
  using l4_b0_anchor_base_key_present l4_b0_anchor_source_at_anchor
  by simp

lemma l4_b0_anchor_source_key_at_frontier:
  "Src l4_b0_anchor_b0 l4_b0_anchor_H
      (frontier l4_b0_anchor_C) (700::nat) = Some 7000"
  using l4_b0_anchor_base_key_present l4_b0_anchor_source_at_frontier
  by simp

lemma l4_b0_anchor_apply:
  "Apply (clean_prefix l4_b0_anchor_C) = l4_b0_anchor_b0"
  by (rule ext) (simp add: Apply_def
                            l4_b0_anchor_b0_def
                            l4_b0_anchor_clean_prefix
                            l4_b0_anchor_prefix_def)

lemma l4_b0_anchor_apply_key:
  "Apply (clean_prefix l4_b0_anchor_C) (700::nat) = Some 7000"
  using l4_b0_anchor_apply l4_b0_anchor_base_key_present by simp

lemma l4_b0_anchor_domain:
  "anchor_domain l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor = {700}"
  unfolding anchor_domain_def
  using l4_b0_anchor_source_at_anchor
  by (auto simp: l4_b0_anchor_b0_def)

lemma l4_b0_anchor_key_in_anchor_domain:
  "(700::nat) \<in> anchor_domain l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor"
  using l4_b0_anchor_domain by simp

lemma l4_b0_anchor_touched_between:
  "touched_between l4_b0_anchor_H l4_anchor
      (frontier l4_b0_anchor_C) = {}"
  by (simp add: touched_between_def l4_b0_anchor_H_def)

lemma l4_b0_anchor_table_scope_between:
  "table_scope_between l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor
      (frontier l4_b0_anchor_C) = scope l4_b0_anchor_C"
  by (simp add: table_scope_between_def
                l4_b0_anchor_domain
                l4_b0_anchor_touched_between
                l4_b0_anchor_scope)

lemma l4_b0_anchor_replay_keys:
  "replay_keys (clean_prefix l4_b0_anchor_C) = {700}"
  unfolding replay_keys_def
  by (simp add: l4_b0_anchor_clean_prefix
                l4_b0_anchor_prefix_def)

lemma l4_b0_anchor_no_unclaimed_replay_keys:
  "no_unclaimed_replay_keys
     (clean_prefix l4_b0_anchor_C) (scope l4_b0_anchor_C)"
  unfolding no_unclaimed_replay_keys_def
  by (simp add: l4_b0_anchor_replay_keys l4_b0_anchor_scope)

lemma l4_b0_anchor_anchor_complete:
  "anchor_complete_at_boundary l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor
     (scope l4_b0_anchor_C)"
  unfolding anchor_complete_at_boundary_def
  by (simp add: l4_b0_anchor_domain l4_b0_anchor_scope)

lemma l4_b0_anchor_all_post_anchor_changes_covered:
  "all_post_anchor_changes_covered l4_b0_anchor_H l4_anchor
     (frontier l4_b0_anchor_C) (scope l4_b0_anchor_C)"
  unfolding all_post_anchor_changes_covered_def
  by (simp add: l4_b0_anchor_touched_between)

lemma l4_b0_anchor_anchor_le_frontier:
  "l4_anchor \<le> frontier l4_b0_anchor_C"
  using ec1_le_ec4
  by (simp add: l4_anchor_def l4_b0_anchor_frontier
                less_eq_src_coord_def)

lemma l4_b0_anchor_whole_table_claim_scope:
  "whole_table_claim_scope l4_b0_anchor_b0 l4_b0_anchor_C
     l4_b0_anchor_H l4_anchor"
  unfolding whole_table_claim_scope_def
  using l4_b0_anchor_anchor_le_frontier
        l4_b0_anchor_anchor_complete
        l4_b0_anchor_all_post_anchor_changes_covered
        l4_b0_anchor_no_unclaimed_replay_keys
  by blast

lemma l4_b0_anchor_virtual_cut:
  "virtual_cut l4_b0_anchor_b0 l4_b0_anchor_C l4_b0_anchor_H"
  unfolding virtual_cut_def virtual_cut_state_def
  using l4_b0_anchor_apply l4_b0_anchor_source_at_frontier
  by (simp add: l4_b0_anchor_clean_prefix
                l4_b0_anchor_scope
                l4_b0_anchor_frontier)

theorem l4_b0_anchor_unrestricted_equality:
  "Apply (clean_prefix l4_b0_anchor_C)
   = Src l4_b0_anchor_b0 l4_b0_anchor_H (frontier l4_b0_anchor_C)"
  using l4_b0_anchor_apply l4_b0_anchor_source_at_frontier by simp

theorem layer4_b0_base_state_anchor_domain_fixture:
  "l4_b0_anchor_H = []
   \<and> l4_b0_anchor_b0 (700::nat) = Some 7000
   \<and> latest_src_event l4_b0_anchor_H l4_anchor (700::nat) = None
   \<and> Src l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor 700 = Some 7000
   \<and> Src l4_b0_anchor_b0 l4_b0_anchor_H
        (frontier l4_b0_anchor_C) 700 = Some 7000
   \<and> anchor_domain l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor = {700}
   \<and> (700::nat) \<in> anchor_domain l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor
   \<and> touched_between l4_b0_anchor_H l4_anchor
        (frontier l4_b0_anchor_C) = {}
   \<and> table_scope_between l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor
        (frontier l4_b0_anchor_C) = scope l4_b0_anchor_C
   \<and> scope l4_b0_anchor_C = {700}
   \<and> replay_keys (clean_prefix l4_b0_anchor_C) = {700}
   \<and> Apply (clean_prefix l4_b0_anchor_C) 700 = Some 7000
   \<and> l4_anchor \<le> frontier l4_b0_anchor_C
   \<and> anchor_complete_at_boundary l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor
        (scope l4_b0_anchor_C)
   \<and> all_post_anchor_changes_covered l4_b0_anchor_H l4_anchor
        (frontier l4_b0_anchor_C) (scope l4_b0_anchor_C)
   \<and> no_unclaimed_replay_keys
        (clean_prefix l4_b0_anchor_C) (scope l4_b0_anchor_C)
   \<and> whole_table_claim_scope l4_b0_anchor_b0 l4_b0_anchor_C
        l4_b0_anchor_H l4_anchor
   \<and> virtual_cut l4_b0_anchor_b0 l4_b0_anchor_C l4_b0_anchor_H
   \<and> Apply (clean_prefix l4_b0_anchor_C)
      = Src l4_b0_anchor_b0 l4_b0_anchor_H (frontier l4_b0_anchor_C)"
  using l4_b0_anchor_H_def
        l4_b0_anchor_base_key_present
        l4_b0_anchor_no_source_event_for_key
        l4_b0_anchor_source_key_at_anchor
        l4_b0_anchor_source_key_at_frontier
        l4_b0_anchor_domain
        l4_b0_anchor_key_in_anchor_domain
        l4_b0_anchor_touched_between
        l4_b0_anchor_table_scope_between
        l4_b0_anchor_scope
        l4_b0_anchor_replay_keys
        l4_b0_anchor_apply_key
        l4_b0_anchor_anchor_le_frontier
        l4_b0_anchor_anchor_complete
        l4_b0_anchor_all_post_anchor_changes_covered
        l4_b0_anchor_no_unclaimed_replay_keys
        l4_b0_anchor_whole_table_claim_scope
        l4_b0_anchor_virtual_cut
        l4_b0_anchor_unrestricted_equality
  by simp


section \<open>Same-coordinate anchor and frontier boundaries\<close>

definition l4_same_boundary_b0 :: "nat \<rightharpoonup> nat" where
  "l4_same_boundary_b0 = (\<lambda>_. None)"

definition l4_same_boundary_H :: "(nat, nat) src_history" where
  "l4_same_boundary_H =
     [ (ec1, Insert (800::nat) (8000::nat)),
       (ec4, Insert (900::nat) (9000::nat)) ]"

definition l4_same_boundary_prefix :: "(nat, nat) replay_event list" where
  "l4_same_boundary_prefix =
     [ Cdc ec1 (Insert (800::nat) (8000::nat)),
       Cdc ec4 (Insert (900::nat) (9000::nat)) ]"

axiomatization l4_same_boundary_C :: "(nat, nat) cert"
where
  l4_same_boundary_scope:
    "scope l4_same_boundary_C = {800, 900}"
and
  l4_same_boundary_frontier:
    "frontier l4_same_boundary_C = ec4"
and
  l4_same_boundary_clean_prefix:
    "clean_prefix l4_same_boundary_C = l4_same_boundary_prefix"

lemma l4_same_boundary_anchor_event_in_history:
  "(ec1, Insert (800::nat) (8000::nat)) \<in> set l4_same_boundary_H"
  by (simp add: l4_same_boundary_H_def)

lemma l4_same_boundary_frontier_event_in_history:
  "(ec4, Insert (900::nat) (9000::nat)) \<in> set l4_same_boundary_H"
  by (simp add: l4_same_boundary_H_def)

lemma l4_same_boundary_latest_anchor_800:
  "latest_src_event l4_same_boundary_H l4_anchor (800::nat) = Some 0"
  unfolding latest_src_event_def l4_same_boundary_H_def l4_anchor_def
  using src_le_refl[where c=ec1] not_src_le_ec4_ec1
  by simp

lemma l4_same_boundary_latest_anchor_900:
  "latest_src_event l4_same_boundary_H l4_anchor (900::nat) = None"
  unfolding latest_src_event_def l4_same_boundary_H_def l4_anchor_def
  using src_le_refl[where c=ec1] not_src_le_ec4_ec1
  by simp

lemma l4_same_boundary_latest_frontier_800:
  "latest_src_event l4_same_boundary_H
      (frontier l4_same_boundary_C) (800::nat) = Some 0"
  unfolding latest_src_event_def l4_same_boundary_H_def
  using ec1_le_ec4 l4_same_boundary_frontier
        src_le_refl[where c=ec4]
  by simp

lemma l4_same_boundary_latest_frontier_900:
  "latest_src_event l4_same_boundary_H
      (frontier l4_same_boundary_C) (900::nat) = Some 1"
  unfolding latest_src_event_def l4_same_boundary_H_def
  using ec1_le_ec4 l4_same_boundary_frontier
        src_le_refl[where c=ec4]
  by simp

lemma l4_same_boundary_source_anchor_800:
  "Src l4_same_boundary_b0 l4_same_boundary_H l4_anchor (800::nat)
     = Some 8000"
  unfolding Src_def
  using l4_same_boundary_latest_anchor_800
  by (simp add: l4_same_boundary_H_def)

lemma l4_same_boundary_source_anchor_900:
  "Src l4_same_boundary_b0 l4_same_boundary_H l4_anchor (900::nat) = None"
  unfolding Src_def l4_same_boundary_b0_def
  using l4_same_boundary_latest_anchor_900 by simp

lemma l4_same_boundary_source_frontier_800:
  "Src l4_same_boundary_b0 l4_same_boundary_H
      (frontier l4_same_boundary_C) (800::nat) = Some 8000"
  unfolding Src_def
  using l4_same_boundary_latest_frontier_800
  by (simp add: l4_same_boundary_H_def)

lemma l4_same_boundary_source_frontier_900:
  "Src l4_same_boundary_b0 l4_same_boundary_H
      (frontier l4_same_boundary_C) (900::nat) = Some 9000"
  unfolding Src_def
  using l4_same_boundary_latest_frontier_900
  by (simp add: l4_same_boundary_H_def)

lemma l4_same_boundary_anchor_domain:
  "anchor_domain l4_same_boundary_b0 l4_same_boundary_H l4_anchor = {800}"
  unfolding anchor_domain_def l4_same_boundary_b0_def
            l4_same_boundary_H_def l4_anchor_def Src_def latest_src_event_def
  using src_le_refl[where c=ec1] not_src_le_ec4_ec1
  by auto

lemma l4_same_boundary_anchor_key_in_anchor_domain:
  "(800::nat) \<in> anchor_domain l4_same_boundary_b0
     l4_same_boundary_H l4_anchor"
  using l4_same_boundary_anchor_domain by simp

lemma l4_same_boundary_frontier_key_not_in_anchor_domain:
  "(900::nat) \<notin> anchor_domain l4_same_boundary_b0
     l4_same_boundary_H l4_anchor"
  using l4_same_boundary_anchor_domain by simp

lemma l4_same_boundary_touched_between:
  "touched_between l4_same_boundary_H l4_anchor
      (frontier l4_same_boundary_C) = {900}"
proof (rule subset_antisym)
  show "touched_between l4_same_boundary_H l4_anchor
          (frontier l4_same_boundary_C) \<subseteq> {900}"
    unfolding touched_between_def l4_same_boundary_H_def l4_anchor_def
              l4_same_boundary_frontier
    by auto
next
  show "{900} \<subseteq> touched_between l4_same_boundary_H l4_anchor
          (frontier l4_same_boundary_C)"
  proof
    fix k :: nat
    assume "k \<in> {900}"
    hence k900: "k = 900" by simp
    have in_H:
      "(ec4, Insert (900::nat) (9000::nat)) \<in> set l4_same_boundary_H"
      by (simp add: l4_same_boundary_H_def)
    have after_anchor: "l4_anchor < ec4"
      using ec1_less_ec4 by (simp add: l4_anchor_def)
    have before_frontier: "ec4 \<le> frontier l4_same_boundary_C"
      by (simp add: l4_same_boundary_frontier)
    show "k \<in> touched_between l4_same_boundary_H l4_anchor
            (frontier l4_same_boundary_C)"
      unfolding touched_between_def
      using in_H k900 after_anchor before_frontier
      by (intro CollectI exI[where x=ec4]
                exI[where x="Insert (900::nat) (9000::nat)"]) auto
  qed
qed

lemma l4_same_boundary_anchor_key_not_touched:
  "(800::nat) \<notin> touched_between l4_same_boundary_H l4_anchor
      (frontier l4_same_boundary_C)"
  using l4_same_boundary_touched_between by simp

lemma l4_same_boundary_frontier_key_touched:
  "(900::nat) \<in> touched_between l4_same_boundary_H l4_anchor
      (frontier l4_same_boundary_C)"
  using l4_same_boundary_touched_between by simp

lemma l4_same_boundary_table_scope_between:
  "table_scope_between l4_same_boundary_b0 l4_same_boundary_H l4_anchor
      (frontier l4_same_boundary_C) = scope l4_same_boundary_C"
  by (auto simp: table_scope_between_def
                 l4_same_boundary_anchor_domain
                 l4_same_boundary_touched_between
                 l4_same_boundary_scope)

lemma l4_same_boundary_replay_keys:
  "replay_keys (clean_prefix l4_same_boundary_C) = {800, 900}"
  unfolding replay_keys_def
  by (auto simp: l4_same_boundary_clean_prefix
                 l4_same_boundary_prefix_def)

lemma l4_same_boundary_no_unclaimed_replay_keys:
  "no_unclaimed_replay_keys
     (clean_prefix l4_same_boundary_C) (scope l4_same_boundary_C)"
  unfolding no_unclaimed_replay_keys_def
  by (simp add: l4_same_boundary_replay_keys l4_same_boundary_scope)

lemma l4_same_boundary_anchor_complete:
  "anchor_complete_at_boundary l4_same_boundary_b0 l4_same_boundary_H
     l4_anchor (scope l4_same_boundary_C)"
  unfolding anchor_complete_at_boundary_def
  by (simp add: l4_same_boundary_anchor_domain
                l4_same_boundary_scope)

lemma l4_same_boundary_all_post_anchor_changes_covered:
  "all_post_anchor_changes_covered l4_same_boundary_H l4_anchor
     (frontier l4_same_boundary_C) (scope l4_same_boundary_C)"
  unfolding all_post_anchor_changes_covered_def
  by (simp add: l4_same_boundary_touched_between
                l4_same_boundary_scope)

lemma l4_same_boundary_anchor_le_frontier:
  "l4_anchor \<le> frontier l4_same_boundary_C"
  using ec1_le_ec4
  by (simp add: l4_anchor_def l4_same_boundary_frontier
                less_eq_src_coord_def)

lemma l4_same_boundary_whole_table_claim_scope:
  "whole_table_claim_scope l4_same_boundary_b0 l4_same_boundary_C
     l4_same_boundary_H l4_anchor"
  unfolding whole_table_claim_scope_def
  using l4_same_boundary_anchor_le_frontier
        l4_same_boundary_anchor_complete
        l4_same_boundary_all_post_anchor_changes_covered
        l4_same_boundary_no_unclaimed_replay_keys
  by blast

lemma l4_same_boundary_apply:
  "Apply (clean_prefix l4_same_boundary_C) =
     (\<lambda>k. if k = (800::nat) then Some (8000::nat)
          else if k = 900 then Some 9000
          else None)"
  by (rule ext) (simp add: Apply_def
                            l4_same_boundary_clean_prefix
                            l4_same_boundary_prefix_def)

lemma l4_same_boundary_apply_800:
  "Apply (clean_prefix l4_same_boundary_C) (800::nat) = Some 8000"
  by (simp add: l4_same_boundary_apply)

lemma l4_same_boundary_apply_900:
  "Apply (clean_prefix l4_same_boundary_C) (900::nat) = Some 9000"
  by (simp add: l4_same_boundary_apply)

lemma l4_same_boundary_virtual_cut:
  "virtual_cut l4_same_boundary_b0 l4_same_boundary_C l4_same_boundary_H"
  unfolding virtual_cut_def virtual_cut_state_def restrict_def
proof (rule ext)
  fix k :: nat
  show "(if k \<in> scope l4_same_boundary_C
         then Apply (clean_prefix l4_same_boundary_C) k else None)
      = (if k \<in> scope l4_same_boundary_C
         then Src l4_same_boundary_b0 l4_same_boundary_H
                (frontier l4_same_boundary_C) k else None)"
  proof (cases "k = 800")
    case True
    thus ?thesis
      using l4_same_boundary_apply_800
            l4_same_boundary_source_frontier_800
      by (simp add: l4_same_boundary_scope)
  next
    case not800: False
    show ?thesis
    proof (cases "k = 900")
      case True
      thus ?thesis
        using l4_same_boundary_apply_900
              l4_same_boundary_source_frontier_900
        by (simp add: l4_same_boundary_scope)
    next
      case False
      with not800 show ?thesis
        by (simp add: l4_same_boundary_scope)
    qed
  qed
qed

theorem l4_same_boundary_unrestricted_equality:
  "Apply (clean_prefix l4_same_boundary_C)
   = Src l4_same_boundary_b0 l4_same_boundary_H
       (frontier l4_same_boundary_C)"
  by (rule whole_table_equality_from_claim_scope
      [OF l4_same_boundary_virtual_cut
          l4_same_boundary_whole_table_claim_scope])

theorem layer4_same_coordinate_boundary_fixture:
  "(ec1, Insert (800::nat) (8000::nat)) \<in> set l4_same_boundary_H
   \<and> (ec4, Insert (900::nat) (9000::nat)) \<in> set l4_same_boundary_H
   \<and> frontier l4_same_boundary_C = ec4
   \<and> Src l4_same_boundary_b0 l4_same_boundary_H l4_anchor 800 = Some 8000
   \<and> Src l4_same_boundary_b0 l4_same_boundary_H l4_anchor 900 = None
   \<and> Src l4_same_boundary_b0 l4_same_boundary_H
        (frontier l4_same_boundary_C) 900 = Some 9000
   \<and> anchor_domain l4_same_boundary_b0 l4_same_boundary_H l4_anchor = {800}
   \<and> (800::nat) \<in> anchor_domain l4_same_boundary_b0
        l4_same_boundary_H l4_anchor
   \<and> (900::nat) \<notin> anchor_domain l4_same_boundary_b0
        l4_same_boundary_H l4_anchor
   \<and> touched_between l4_same_boundary_H l4_anchor
        (frontier l4_same_boundary_C) = {900}
   \<and> 800 \<notin> touched_between l4_same_boundary_H l4_anchor
        (frontier l4_same_boundary_C)
   \<and> 900 \<in> touched_between l4_same_boundary_H l4_anchor
        (frontier l4_same_boundary_C)
   \<and> table_scope_between l4_same_boundary_b0 l4_same_boundary_H l4_anchor
        (frontier l4_same_boundary_C) = scope l4_same_boundary_C
   \<and> scope l4_same_boundary_C = {800, 900}
   \<and> replay_keys (clean_prefix l4_same_boundary_C) = {800, 900}
   \<and> no_unclaimed_replay_keys
        (clean_prefix l4_same_boundary_C) (scope l4_same_boundary_C)
   \<and> whole_table_claim_scope l4_same_boundary_b0 l4_same_boundary_C
        l4_same_boundary_H l4_anchor
   \<and> virtual_cut l4_same_boundary_b0 l4_same_boundary_C l4_same_boundary_H
   \<and> Apply (clean_prefix l4_same_boundary_C)
      = Src l4_same_boundary_b0 l4_same_boundary_H
          (frontier l4_same_boundary_C)"
  using l4_same_boundary_anchor_event_in_history
        l4_same_boundary_frontier_event_in_history
        l4_same_boundary_frontier
        l4_same_boundary_source_anchor_800
        l4_same_boundary_source_anchor_900
        l4_same_boundary_source_frontier_900
        l4_same_boundary_anchor_domain
        l4_same_boundary_anchor_key_in_anchor_domain
        l4_same_boundary_frontier_key_not_in_anchor_domain
        l4_same_boundary_touched_between
        l4_same_boundary_anchor_key_not_touched
        l4_same_boundary_frontier_key_touched
        l4_same_boundary_table_scope_between
        l4_same_boundary_scope
        l4_same_boundary_replay_keys
        l4_same_boundary_no_unclaimed_replay_keys
        l4_same_boundary_whole_table_claim_scope
        l4_same_boundary_virtual_cut
        l4_same_boundary_unrestricted_equality
  by simp


section \<open>Materialized-run ambiguity is not Layer 4 evidence\<close>

text \<open>
  A set-only / run-sensitive boundary fixture.  The fixture
  certificate exposes the same Layer 4 data as the running-example
  witness -- scope, frontier, clean prefix, anchor, source history,
  virtual-cut equality, whole-table claim scope -- yet
  @{const materializes_run} is a relation, not a function: the same
  certificate and evidence are materialized by two distinct runs whose
  chunk sets, and whose responsible chunk for key 100, differ.  Layer 4
  must therefore not infer responsible-chunk or watermark facts from
  @{const whole_table_claim_scope}, or from any other set-only
  certificate predicate.

  The fixture is materialization-relational: the two runs are tied to
  the certificate only through @{const materializes_run}.  It
  deliberately does not also assert @{const cert_accessors_agree} on
  each run -- that predicate pins the defined function
  @{const clean_prefix_of} to the two-coordinate running-example clean
  prefix, which a single-chunk run cannot produce, so asserting it on
  the singleton-chunk run witnesses below would be inconsistent.  A
  variant asserting full accessor-surface agreement would need genuine
  multi-chunk run witnesses whose derived clean prefix equals the
  running example's; that variant is outside this fixture's scope.  The
  materialization-relational form here already discharges the
  overclaim-control point.
\<close>

axiomatization
    l4_run_ambiguity_C :: "(nat, nat) cert"
  and l4_run_ambiguity_E :: "(nat, nat) evidence"
  and l4_run_ambiguity_R_left :: "(nat, nat) run"
  and l4_run_ambiguity_R_right :: "(nat, nat) run"
  and l4_run_ambiguity_ch_left :: "(nat, nat) chunk"
  and l4_run_ambiguity_ch_right :: "(nat, nat) chunk"
where
  l4_run_ambiguity_scope:
    "scope l4_run_ambiguity_C = scope l3_C"
and
  l4_run_ambiguity_frontier:
    "frontier l4_run_ambiguity_C = frontier l3_C"
and
  l4_run_ambiguity_clean_prefix:
    "clean_prefix l4_run_ambiguity_C = clean_prefix l3_C"
and
  l4_run_ambiguity_materializes_left:
    "materializes_run l4_run_ambiguity_C l4_run_ambiguity_E
       l4_run_ambiguity_R_left"
and
  l4_run_ambiguity_materializes_right:
    "materializes_run l4_run_ambiguity_C l4_run_ambiguity_E
       l4_run_ambiguity_R_right"
and
  l4_run_ambiguity_chunks_left:
    "chunks l4_run_ambiguity_R_left = {l4_run_ambiguity_ch_left}"
and
  l4_run_ambiguity_chunks_right:
    "chunks l4_run_ambiguity_R_right = {l4_run_ambiguity_ch_right}"
and
  l4_run_ambiguity_chunks_distinct:
    "l4_run_ambiguity_ch_left \<noteq> l4_run_ambiguity_ch_right"
and
  l4_run_ambiguity_responsible_left:
    "responsible_chunk l4_run_ambiguity_R_left (100::nat)
       = Some l4_run_ambiguity_ch_left"
and
  l4_run_ambiguity_responsible_right:
    "responsible_chunk l4_run_ambiguity_R_right (100::nat)
       = Some l4_run_ambiguity_ch_right"

lemma l4_run_ambiguity_same_certificate_surface:
  "scope l4_run_ambiguity_C = scope l3_C
   \<and> frontier l4_run_ambiguity_C = frontier l3_C
   \<and> clean_prefix l4_run_ambiguity_C = clean_prefix l3_C"
  by (simp add: l4_run_ambiguity_scope
                l4_run_ambiguity_frontier
                l4_run_ambiguity_clean_prefix)

lemma l4_run_ambiguity_chunk_sets_differ:
  "chunks l4_run_ambiguity_R_left
   \<noteq> chunks l4_run_ambiguity_R_right"
  using l4_run_ambiguity_chunks_left
        l4_run_ambiguity_chunks_right
        l4_run_ambiguity_chunks_distinct
  by auto

lemma l4_run_ambiguity_responsible_chunks_differ:
  "responsible_chunk l4_run_ambiguity_R_left (100::nat)
   \<noteq> responsible_chunk l4_run_ambiguity_R_right 100"
  using l4_run_ambiguity_responsible_left
        l4_run_ambiguity_responsible_right
        l4_run_ambiguity_chunks_distinct
  by simp

lemma l4_run_ambiguity_whole_table_claim_scope:
  "whole_table_claim_scope b0_ex l4_run_ambiguity_C H_ex l4_anchor"
  unfolding whole_table_claim_scope_def
proof (intro conjI)
  show "l4_anchor \<le> frontier l4_run_ambiguity_C"
    using l4_anchor_le_frontier
    by (simp add: l4_run_ambiguity_frontier)
next
  show "anchor_complete_at_boundary b0_ex H_ex l4_anchor
          (scope l4_run_ambiguity_C)"
    unfolding anchor_complete_at_boundary_def
    using l4_anchor_domain l3_scope ex_scope
    by (simp add: l4_run_ambiguity_scope)
next
  show "all_post_anchor_changes_covered H_ex l4_anchor
          (frontier l4_run_ambiguity_C) (scope l4_run_ambiguity_C)"
    unfolding all_post_anchor_changes_covered_def
    using l4_touched_between l3_scope ex_scope
    by (simp add: l4_run_ambiguity_scope
                  l4_run_ambiguity_frontier)
next
  show "no_unclaimed_replay_keys
          (clean_prefix l4_run_ambiguity_C) (scope l4_run_ambiguity_C)"
    unfolding no_unclaimed_replay_keys_def
    using l4_replay_keys l3_scope ex_scope
    by (simp add: l4_run_ambiguity_clean_prefix
                  l4_run_ambiguity_scope)
qed

lemma l4_run_ambiguity_virtual_cut:
  "virtual_cut b0_ex l4_run_ambiguity_C H_ex"
proof -
  have l3_state:
    "virtual_cut_state b0_ex (clean_prefix l3_C) (scope l3_C)
       (frontier l3_C) H_ex"
    using l3_witness_accepted_virtual_cut_sound
    unfolding virtual_cut_def by simp
  show ?thesis
    unfolding virtual_cut_def
    using l3_state
    by (simp add: l4_run_ambiguity_scope
                  l4_run_ambiguity_frontier
                  l4_run_ambiguity_clean_prefix)
qed

lemma l4_run_ambiguity_unrestricted_equality:
  "Apply (clean_prefix l4_run_ambiguity_C)
   = Src b0_ex H_ex (frontier l4_run_ambiguity_C)"
  by (rule whole_table_equality_from_claim_scope
      [OF l4_run_ambiguity_virtual_cut
          l4_run_ambiguity_whole_table_claim_scope])

theorem layer4_materialized_run_ambiguity_fixture:
  "materializes_run l4_run_ambiguity_C l4_run_ambiguity_E
      l4_run_ambiguity_R_left
   \<and> materializes_run l4_run_ambiguity_C l4_run_ambiguity_E
      l4_run_ambiguity_R_right
   \<and> scope l4_run_ambiguity_C = scope l3_C
   \<and> frontier l4_run_ambiguity_C = frontier l3_C
   \<and> clean_prefix l4_run_ambiguity_C = clean_prefix l3_C
   \<and> chunks l4_run_ambiguity_R_left
      \<noteq> chunks l4_run_ambiguity_R_right
   \<and> responsible_chunk l4_run_ambiguity_R_left 100
      \<noteq> responsible_chunk l4_run_ambiguity_R_right 100
   \<and> whole_table_claim_scope b0_ex l4_run_ambiguity_C H_ex l4_anchor
   \<and> virtual_cut b0_ex l4_run_ambiguity_C H_ex
   \<and> Apply (clean_prefix l4_run_ambiguity_C)
      = Src b0_ex H_ex (frontier l4_run_ambiguity_C)"
  using l4_run_ambiguity_materializes_left
        l4_run_ambiguity_materializes_right
        l4_run_ambiguity_same_certificate_surface
        l4_run_ambiguity_chunk_sets_differ
        l4_run_ambiguity_responsible_chunks_differ
        l4_run_ambiguity_whole_table_claim_scope
        l4_run_ambiguity_virtual_cut
        l4_run_ambiguity_unrestricted_equality
  by simp

end
