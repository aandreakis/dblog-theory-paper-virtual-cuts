theory Source_History
  imports Main
begin

text \<open>
  Layer 0 source-history substrate.

  Source-side vocabulary:

    \<^item> @{text src_coord}: source-side ordering coordinate
        (commit position / LSN / monotone source-side timestamp);
    \<^item> @{text src_le}: source-coordinate ordering relation,
        axiomatized as a linear (total) order with a least element
        @{text c0}, over a nontrivial coordinate space (at least one
        coordinate is distinct from @{text c0});
    \<^item> @{text c0}: the named \<^emph>\<open>base coordinate\<close> -- the least
        element under @{text src_le}; a named constant, not a Hilbert
        choice or a locale parameter;
    \<^item> @{text src_lt}: derived strict relation
        @{text "src_lt c c' \<longleftrightarrow> src_le c c' \<and> c \<noteq> c'"};
    \<^item> @{text "('k, 'v) source_event"}: source-side per-key write
        events with three explicit constructors @{text Insert} /
        @{text Update} / @{text Delete};
    \<^item> @{text "('k, 'v) src_history"}: ordered append-only source-event
        log (a finite list of (coord, event) pairs);
    \<^item> @{text frontier}: a chosen source-coordinate prefix marker
        (a @{text src_coord});
    \<^item> @{text source_pos_order}: source-position relation \<^emph>\<open>on
        valid indices\<close> of a source history -- a relation on indices
        rather than on items, so two indices carrying identical
        @{text "(c, e)"} pairs remain distinguishable;
    \<^item> @{text latest_src_event}: latest-event-by-key, returning
        @{text "nat option"} -- an \<^emph>\<open>occurrence index\<close> of
        @{text H};
    \<^item> @{text wellformed_src_history}: source-history wellformedness
        predicate (paper @{text "wellformed-src-history H"} with
        clauses WF-H1 non-decreasing / WF-H2 no event at @{text c0} /
        WF-H3 @{text "\<preceq>\<^sub>H"} totality on valid indices);
    \<^item> @{text Src}: source state at a frontier, with an explicit
        \<^emph>\<open>base state\<close> parameter @{text b0}: @{text "Src(b0, H, f)"}.

  Source events and replay events are real Isabelle datatypes;
  @{text Apply}, @{text apply_step}, @{text Src},
  @{text latest_src_event}, @{text source_pos_order},
  @{text wellformed_src_history}, @{text src_lt}, and
  @{text cdc_lift} are real definitions. Only @{text src_le} and
  @{text c0} are axiomatized, because they carry the
  source-coordinate order axioms.

  Run accessors (in @{text DBLog_Run}) are written with an
  @{text "_of"} suffix --- @{text "scope_of(R)"},
  @{text "frontier_of(R)"}, @{text "clean_prefix_of(R)"} --- and the
  certificate accessors (in @{text Virtual_Cut}) are bare ---
  @{text "scope(C)"}, @{text "frontier(C)"}, @{text "clean_prefix(C)"}
  --- to mirror the paper's notation.
\<close>

subsection \<open>Source coordinates and the base coordinate\<close>

typedecl src_coord

axiomatization
      src_le :: "src_coord \<Rightarrow> src_coord \<Rightarrow> bool"
  and c0     :: src_coord
where
      src_le_refl:    "src_le c c"
  and src_le_antisym: "\<lbrakk>src_le c c'; src_le c' c\<rbrakk> \<Longrightarrow> c = c'"
  and src_le_trans:   "\<lbrakk>src_le c c'; src_le c' c''\<rbrakk> \<Longrightarrow> src_le c c''"
  and src_le_total:   "src_le c c' \<or> src_le c' c"
  and c0_least:       "src_le c0 c"
  and src_coord_nontrivial: "\<exists>c. c \<noteq> c0"

text \<open>
  The strict relation @{text src_lt} is the derived shorthand
  @{text "src_lt c c' \<longleftrightarrow> src_le c c' \<and> c \<noteq> c'"}; not a separate
  primitive. Paper "source-coordinate ordering" definition.
\<close>

definition src_lt :: "src_coord \<Rightarrow> src_coord \<Rightarrow> bool" where
  "src_lt c c' \<longleftrightarrow> src_le c c' \<and> c \<noteq> c'"

subsection \<open>@{class linorder} instance for @{type src_coord}\<close>

text \<open>
  @{type src_coord} is declared a @{class linorder} instance with
  @{text "(\<le>) = src_le"} and @{text "(<) = src_lt"}. The five
  linorder axioms (@{text less_le_not_le} / @{text order_refl} /
  @{text order_trans} / @{text order_antisym} / @{text linear})
  discharge directly from the @{text "src_le_*"} axiomatization
  above.

  Rationale: the canonical-clean-prefix construction at Layer 0
  (paper "Auxiliary Layer 0 definitions" / "Canonical clean
  prefix" step 3) interleaves replay events in source-coordinate
  order. The interleave step uses @{const sort_key} over @{text
  src_coord}, which requires the @{class linorder} instance. This
  surfaces an assumption the paper already makes (step 3 speaks of
  "source-coordinate order" as a total order); the instance makes
  it usable by Isabelle's library sorting function.

  No @{class order_bot} instance is declared (although
  @{text c0_least} would satisfy it): the body lift does not need a
  least-element typeclass.
\<close>

instantiation src_coord :: linorder
begin

definition less_eq_src_coord :: "src_coord \<Rightarrow> src_coord \<Rightarrow> bool" where
  "less_eq_src_coord = src_le"

definition less_src_coord :: "src_coord \<Rightarrow> src_coord \<Rightarrow> bool" where
  "less_src_coord = src_lt"

instance proof
  fix x y z :: src_coord
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_src_coord_def less_eq_src_coord_def src_lt_def
    using src_le_antisym src_le_refl by blast
  show "x \<le> x"
    unfolding less_eq_src_coord_def by (rule src_le_refl)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    unfolding less_eq_src_coord_def by (rule src_le_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    unfolding less_eq_src_coord_def by (rule src_le_antisym)
  show "x \<le> y \<or> y \<le> x"
    unfolding less_eq_src_coord_def by (rule src_le_total)
qed

end

text \<open>
  Compatibility lemmas: @{text "src_le = (\<le>)"} on @{type src_coord}
  and @{text "src_lt = (<)"} on @{type src_coord}. These let
  existing call sites that use @{const src_le} / @{const src_lt}
  by name continue to work without rewriting; new code can use the
  typeclass operators.
\<close>

lemma src_le_eq_less_eq: "src_le = ((\<le>) :: src_coord \<Rightarrow> src_coord \<Rightarrow> bool)"
  by (simp add: less_eq_src_coord_def)

lemma src_lt_eq_less: "src_lt = ((<) :: src_coord \<Rightarrow> src_coord \<Rightarrow> bool)"
  by (simp add: less_src_coord_def)

subsection \<open>Source events\<close>

text \<open>
  Source-side per-key write events, with three explicit
  constructors: @{text Insert} / @{text Update} / @{text Delete}.

  Insert vs Update is preserved at the source-event level (relevant
  for the Layer 4 anchor-domain story and for source CDC vendor
  semantics) and is collapsed by @{text Apply} at the state level
  (both produce @{text "m k = Some v"}).
\<close>

datatype ('k, 'v) source_event
  = Insert 'k 'v
  | Update 'k 'v
  | Delete 'k

fun key_of :: "('k, 'v) source_event \<Rightarrow> 'k" where
  "key_of (Insert k _) = k"
| "key_of (Update k _) = k"
| "key_of (Delete k) = k"

subsection \<open>Source histories\<close>

text \<open>
  A source history @{text H} is a finite list of @{text "(c, e)"}
  pairs where @{text "c :: src_coord"} and
  @{text "e :: ('k, 'v) source_event"}. Paper "Source histories"
  section.

  Field accessors: paper @{text "coord(H[i])"} = @{term fst} (the
  pair's source coordinate); paper @{text "event(H[i])"} = @{term snd}
  (the pair's source event). The @{text hist_coord} /
  @{text hist_event} abbreviations name these for cross-reference
  with the paper.
\<close>

type_synonym ('k, 'v) src_history
  = "(src_coord \<times> ('k, 'v) source_event) list"

type_synonym frontier = src_coord

abbreviation hist_coord
  :: "(src_coord \<times> ('k, 'v) source_event) \<Rightarrow> src_coord"
where
  "hist_coord p \<equiv> fst p"

abbreviation hist_event
  :: "(src_coord \<times> ('k, 'v) source_event) \<Rightarrow> ('k, 'v) source_event"
where
  "hist_event p \<equiv> snd p"

subsection \<open>Source-position relation \<open>\<preceq>\<^sub>H\<close> (on indices)\<close>

text \<open>
  Source-position relation on \<^emph>\<open>valid indices\<close> of @{text H}.
  Stating it on indices rather than on source-history items matters
  when two valid indices @{text "i \<noteq> j"} hold identical
  @{text "(c, e)"} pairs (the same source event listed twice at
  distinct positions): a relation on items could not distinguish
  them. On indices, same-coordinate ties resolve to list position
  (the later list position is the later occurrence under
  @{text "\<preceq>\<^sub>H"}).

  The definition itself carries no index-validity guard: HOL list
  indexing is total, so @{text source_pos_order} is a total relation
  on all of @{typ nat}. It models source order only under explicit
  @{text "i < length H"} and @{text "j < length H"} premises --- as
  supplied by WF-H3 in @{text wellformed_src_history} and by every
  downstream caller. Outside those premises its value is not intended
  to carry meaning.

  Paper "Source histories" section, "Definition (source-position
  relation @{text "\<preceq>\<^sub>H"})".
\<close>

definition source_pos_order
  :: "('k, 'v) src_history \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "source_pos_order H i j \<longleftrightarrow>
       src_lt (hist_coord (H ! i)) (hist_coord (H ! j))
     \<or> ( hist_coord (H ! i) = hist_coord (H ! j)  \<and>  i \<le> j )"

subsection \<open>Latest source event by key (occurrence index)\<close>

text \<open>
  @{text latest_src_event} returns @{text "nat option"} -- an
  \<^emph>\<open>occurrence index\<close> of @{text H} rather than the
  source-history pair itself. The reader recovers
  the underlying pair as @{text "H ! i"} when the result is
  @{text "Some i"}; the index is the means by which two valid indices
  carrying identical @{text "(c, e)"} pairs are distinguished.

  Paper "Source state" / "Definition (latest source event)".

  Implementation: @{text "filter (\<lambda>i. ...) [0..<length H]"} produces
  candidate indices in ascending order; @{term last} of that list is
  the @{text "\<preceq>\<^sub>H"}-greatest index (same-coord ties resolve to
  greatest list position by definition of @{text "\<preceq>\<^sub>H"}, and
  cross-coord ties resolve by @{text src_lt} which is monotone with
  list order under WF-H1).
\<close>

definition latest_src_event
  :: "('k, 'v) src_history \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> nat option"
where
  "latest_src_event H f k =
     (let cand = filter
                   (\<lambda>i. src_le (hist_coord (H ! i)) f
                      \<and> key_of (hist_event (H ! i)) = k)
                   [0..<length H]
      in if cand = [] then None else Some (last cand))"

subsection \<open>Source-history wellformedness\<close>

text \<open>
  Paper "Source histories" / "Definition
  (@{text \<open>wellformed-src-history H\<close>})". Three clauses:

    \<^item> WF-H1: non-decreasing source coordinates;
    \<^item> WF-H2: no source event at the base coordinate @{text c0}
      (so @{text "Src b0 H c0 = b0"} holds unconditionally on
      wellformed histories);
    \<^item> WF-H3: @{text "\<preceq>\<^sub>H"} totality on valid indices (a property
      of the indices, not the items).

  WF-H3 is automatic from @{const source_pos_order}'s definition
  (every pair of distinct valid indices has @{text src_lt} or equality
  on coords, and @{text "\<le>"} on naturals is total) but the paper
  states it explicitly so downstream lemmas can cite it; the body
  below names it for cross-reference.
\<close>

definition wellformed_src_history
  :: "('k, 'v) src_history \<Rightarrow> bool"
where
  "wellformed_src_history H \<longleftrightarrow>
     ( \<comment> \<open>WF-H1: non-decreasing source coordinates\<close>
       (\<forall>i. Suc i < length H
              \<longrightarrow> src_le (hist_coord (H ! i)) (hist_coord (H ! Suc i)))
     \<and> \<comment> \<open>WF-H2: no source event at the base coordinate \<open>c0\<close>\<close>
       (\<forall>i. i < length H \<longrightarrow> hist_coord (H ! i) \<noteq> c0)
     \<and> \<comment> \<open>WF-H3: \<open>\<preceq>\<^sub>H\<close> totality on valid indices\<close>
       (\<forall>i j. i < length H \<and> j < length H \<and> i \<noteq> j
                \<longrightarrow> source_pos_order H i j \<or> source_pos_order H j i) )"

subsection \<open>Source state \<open>Src b0 H f\<close>\<close>

text \<open>
  Paper "Source state" / "Definition (Src)". The source state is the
  per-key state obtained by starting from the \<^emph>\<open>base state\<close>
  @{text b0} and applying every event in @{text H} whose source
  coordinate is at or before @{text f}; the per-key recurrence is
  via @{const latest_src_event}. The signature takes three
  arguments, @{text "Src b0 H f"}.

  The body returns @{text "b0(k)"} when no event for @{text k}
  appears at or before @{text f}, the inserted/updated value when
  the latest event is @{text "Insert k v"} / @{text "Update k v"},
  and @{term None} when the latest event is @{text "Delete k"}.
\<close>

definition Src
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) src_history \<Rightarrow> frontier \<Rightarrow> ('k \<rightharpoonup> 'v)"
where
  "Src b0 H f =
     (\<lambda>k. case latest_src_event H f k of
            None \<Rightarrow> b0 k
          | Some i \<Rightarrow> (case hist_event (H ! i) of
                          Insert _ v \<Rightarrow> Some v
                        | Update _ v \<Rightarrow> Some v
                        | Delete _   \<Rightarrow> None))"

subsection \<open>Lemma 0.3 -- Src is characterized by latest source event at frontier\<close>

text \<open>
  Paper "Layer 0 basic lemmas" / "Lemma 0.3": for any base state
  @{text b0}, wellformed source history @{text H}, frontier
  @{text f}, and key @{text k}, the source state @{text "Src b0 H f"}
  at @{text k} is determined by @{const latest_src_event} via the
  per-event constructor: @{term "Some v"} when the latest event is
  @{text "Insert _ v"} or @{text "Update _ v"}, @{term None} when
  it is @{text "Delete _"}, and @{text "b0 k"} when no source event
  for @{text k} appears at or before @{text f}.

  The lemma is the definitional characterization of @{const Src}:
  @{const Src}'s body is the case-form below, so the lemma is the
  applied-to-@{text k} unfolding of the @{text Src_def} simp rule.
  Its value to consumers (the
  clean_prefix_of_per_key_replay_equals_source lemma primarily,
  plus the Layer 2 main
  theorem proof and Lemma 1.1) is to name the characterization
  explicitly, so proofs can invoke it by semantic name rather than
  by structural unfolding, and so the bridge holds stable across
  future revisions to @{const Src}'s body (any reformulation must
  re-prove this lemma).

  The lemma does NOT consume @{const wellformed_src_history}; the
  characterization is unconditional on @{const Src}'s definition.
  Wellformedness is needed downstream by callers that reason about
  WHICH index @{const latest_src_event} returns (for example, the
  clean_prefix_of_per_key_replay_equals_source lemma's lift from a
  clean-prefix Cdc event at coordinate
  @{text c} to the source event at the SAME coordinate uses WF-H1
  + WF2 to identify the index), but Lemma 0.3 itself is the
  characterization at the index, not its identification.
\<close>

theorem src_characterized_by_latest_event:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and f :: frontier
    and k :: 'k
  shows "Src b0 H f k = (case latest_src_event H f k of
                           None   \<Rightarrow> b0 k
                         | Some i \<Rightarrow> (case hist_event (H ! i) of
                                        Insert _ v \<Rightarrow> Some v
                                      | Update _ v \<Rightarrow> Some v
                                      | Delete _   \<Rightarrow> None))"
  by (simp add: Src_def)

end
