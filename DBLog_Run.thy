theory DBLog_Run
  imports Source_History Replay Scope "HOL-Library.Multiset" "HOL-Library.Sublist"
begin

text \<open>
  Layer 1 abstract DBLog run substrate.

  Layer 1 vocabulary:

    \<^item> @{text "('k, 'v) chunk"}: Layer 1 chunk carrier (held abstract);
    \<^item> @{text "('k, 'v) chunk_read_record"}: Layer 0 self-contained
        chunk-read record carrying @{text "(domain, read_coord,
        observation)"}; the paper places this at Layer 0 inside the
        canonical-clean-prefix construction's input shape, and the
        Isabelle artifact lives in this file because it is consumed
        only via the Layer 1 @{text clean_prefix_of} accessor's
        definitional equality;
    \<^item> @{text "('k, 'v) run"}: Layer 1 run carrier (held abstract);
    \<^item> Run accessors (paper "Run carrier and accessors", 7
        accessors): @{text scope_of} / @{text frontier_of} /
        @{text clean_prefix_of} / @{text chunks} /
        @{text src_history_of} / @{text chunk_read_result} /
        @{text cdc_events_of};
    \<^item> Chunk-plan accessors (paper "Chunk-plan accessors"):
        @{text chunk_domain} / @{text owns} /
        @{text responsible_chunk} /
        @{text canonical_chunk_ownership_domain};
    \<^item> Chunk watermarks (paper "Watermarks and chunk windows"):
        @{text chunk_lower_watermark} /
        @{text chunk_upper_watermark} / @{text chunk_read_coordinate};
    \<^item> Coverage predicates (paper "Coverage predicates"):
        @{text covers_ordinary_cdc} / @{text row_absence_meaningful};
    \<^item> @{text canonical_clean_prefix}: Layer 0 building block paper
        "Auxiliary Layer 0 definitions" / "Canonical clean prefix";
        the paper places this at Layer 0 but the Isabelle artifact
        lives here because the Layer 1 @{text clean_prefix_of}
        accessor is its only consumer;
    \<^item> @{text wellformed_dblog_run}: 3-argument predicate
        @{text "wellformed_dblog_run b0 R H"}; the body is the
        seven-clause conjunction WF0 / WF1 / WF2 / WF4 / WF5 / WF6 /
        WF7. There is no WF3 clause: the numbering carries a
        deliberate gap recording a clause that the model no longer
        uses.

  The run carrier and its abstract accessors are declared here;
  @{text wellformed_dblog_run}, @{text covers_ordinary_cdc}, and
  @{text row_absence_meaningful} are real Isabelle definitions
  transliterating their paper bodies, and @{text clean_prefix_of} is
  determined by the canonical-clean-prefix construction below.

  @{text owns} is an @{command abbreviation} over @{text chunk_domain}
  --- @{text "owns R ch k \<equiv> k \<in> chunk_domain R ch"} --- following the
  paper's reader-facing definitional equivalence; this rules out any
  gap where two independent accessors could disagree on a
  non-wellformed run.

  Run accessors use the @{text "_of"} suffix --- @{text "scope_of R"},
  @{text "frontier_of R"}, @{text "clean_prefix_of R"},
  @{text "src_history_of R"}, @{text "cdc_events_of R"}; certificate
  accessors live in @{text Virtual_Cut} with bare names.

  Naming note on the chunk-read record: the record-component selectors
  in Isabelle/HOL @{command record} blocks default to plain names
  ( @{text domain} / @{text read_coord} / @{text observation} );
  to avoid shadowing pre-existing Isabelle names (the standard
  @{text Domain} relation-domain projector lives in @{text Relation}),
  the selectors here are prefixed @{text "crr_"} ( @{text crr_domain}
  / @{text crr_read_coord} / @{text crr_observation} ). The
  paper-side names are unaffected.
\<close>

subsection \<open>Chunk carrier\<close>

typedecl ('k, 'v) chunk

subsection \<open>Chunk-read record (Layer 0 self-contained)\<close>

text \<open>
  @{text "('k, 'v) chunk_read_record"} is the Layer 0 self-contained
  record carrying the per-chunk evidence the canonical-clean-prefix
  construction's chunk-read step consumes:

    \<^item> @{text crr_domain} \<open>::\<close> @{text "'k set"} -- the chunk's
        claimed key set (paper @{text domain} field; Isabelle
        selector prefixed to avoid shadowing standard library
        names);
    \<^item> @{text crr_read_coord} \<open>::\<close> @{text src_coord} -- the
        source coordinate at which the chunk read executed (paper
        @{text read_coord} field);
    \<^item> @{text crr_observation} \<open>::\<close> @{text "'k \<Rightarrow> 'v option option"}
        -- the per-key observation, where the outer option
        distinguishes "key outside @{text domain}" from "observation
        recorded for an in-domain key" and the inner option
        distinguishes "value found" (@{text "Some v"}) from "no row
        found" (@{term None}) (paper @{text observation} field).

  Paper "Auxiliary Layer 0 definitions" / "Canonical clean prefix"
  / "ChunkReadRecord".
\<close>

record ('k, 'v) chunk_read_record =
  crr_domain      :: "'k set"
  crr_read_coord  :: src_coord
  crr_observation :: "'k \<Rightarrow> 'v option option"

subsection \<open>Run carrier\<close>

typedecl ('k, 'v) run

subsection \<open>Run accessors (7 accessors)\<close>

text \<open>
  Paper "Run carrier and accessors". Seven accessors project the
  run-level structure that the rest of Layer 1 + the Layer 2 theorem
  range over. Chunk-plan accessors and watermarks live in their own
  subsections below; the @{text clean_prefix_of} accessor's
  definitional equality (paper "Clean-prefix construction at Layer
  1") is recorded at the @{text canonical_clean_prefix} subsection
  below.
\<close>

consts
  scope_of           :: "('k, 'v) run \<Rightarrow> 'k set"
  frontier_of        :: "('k, 'v) run \<Rightarrow> frontier"
  chunks             :: "('k, 'v) run \<Rightarrow> ('k, 'v) chunk set"
  src_history_of     :: "('k, 'v) run \<Rightarrow> ('k, 'v) src_history"
  chunk_read_result  :: "('k, 'v) run \<Rightarrow> ('k, 'v) chunk \<Rightarrow> 'k \<Rightarrow> 'v option option"
  cdc_events_of      :: "('k, 'v) run \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list"

text \<open>
  The @{text clean_prefix_of} accessor is not declared here. It is
  defined as the Layer 1 definitional equality (paper "Clean-prefix
  construction at Layer 1") below, after the @{text chunks_list}
  accessor and the @{text canonical_clean_prefix} construction have
  been introduced.
\<close>

subsection \<open>Chunks enumeration accessor\<close>

text \<open>
  The paper's clean-prefix construction at Layer 1 writes the
  chunk-reads input to @{text canonical_clean_prefix} as the list
  comprehension
  @{text "[ ChunkReadRecord(chunk_domain(R, ch),
  chunk_read_coordinate(R, ch), chunk_read_result(R, ch)) | ch \<in>
  chunks(R) ]"}. This requires enumerating @{text "chunks(R) :: ('k, 'v) chunk set"}
  as a list. Since @{text "('k, 'v) chunk"} is opaque
  (@{command typedecl}; no natural @{class linorder}), the
  enumeration cannot be derived from a typeclass instance the way
  @{text "('k :: linorder) set"} can be enumerated by
  @{const sorted_list_of_set}. We therefore introduce
  @{text chunks_list} as a deterministic listing accessor with
  axioms tying it to @{const chunks}:

    \<^item> @{text chunks_list_set}: @{text "set (chunks_list R) = chunks R"};
    \<^item> @{text chunks_list_distinct}: @{text "distinct (chunks_list R)"}.

  Two properties of these axioms must be stated plainly,
  because they are easy to mistake for a harmless enumeration
  convenience.

  The first is global finiteness. @{text chunks_list_set}
  equates @{term "chunks R"} with the set of a list, so it
  forces @{term "finite (chunks R)"} for every run, not only
  for wellformed ones. This is a genuine global assumption on
  the abstract @{const chunks} accessor, not a conservative
  extension: an unconstrained @{const chunks} could return an
  infinite set, and these axioms exclude that everywhere. The
  assumption is intended and sound for the DBLog domain --- a
  run's chunk plan is bounded by construction, because chunking
  proceeds over a determinable key range (a maximum primary
  key, or an equivalent keyspace bound, is fixed before
  chunking begins as the termination criterion), so the chunk
  plan is finite for every run. The lemma @{text chunks_finite}
  just below records this consequence as a named,
  machine-checked fact. The wellformed-run predicate's WF1 (f)
  clause separately requires @{term "finite (scope_of R)"} and
  finiteness of each chunk domain, but does not restate
  chunk-set finiteness --- that fact holds globally and is
  established here.

  The second is that the enumeration order is unspecified. The
  axioms assert that a deterministic enumeration exists without
  pinning which one --- any permutation of @{term "chunks R"}
  satisfies them. The Layer 2 source-side soundness theorem
  does not depend on the choice: at one source coordinate,
  cross-chunk-read Refresh events affect distinct keys (by the
  strict canonical partition), so the per-key replay semantics
  is invariant across enumeration choices.

  Pragmatic alternative considered + rejected: Hilbert epsilon
  @{text "(SOME xs. distinct xs \<and> set xs = chunks R)"} would avoid
  the new constant declaration but would force every downstream
  proof to reason about non-determinism explicitly; a documented
  enumeration accessor is cleaner.
\<close>

consts
  chunks_list :: "('k, 'v) run \<Rightarrow> ('k, 'v) chunk list"

axiomatization where
  chunks_list_set:      "set (chunks_list R) = chunks R"
and
  chunks_list_distinct: "distinct (chunks_list R)"

text \<open>
  The global finiteness documented above, recorded as a named
  fact. Since @{text chunks_list_set} equates @{term "chunks R"}
  with @{term "set (chunks_list R)"}, the set of a list,
  @{term "finite (chunks R)"} holds for every run. Stating it as
  a lemma keeps the global modeling assumption visible and
  machine-checked rather than left implicit in the axiom block.
\<close>

lemma chunks_finite: "finite (chunks R)"
  by (metis chunks_list_set List.finite_set)

subsection \<open>Chunk-plan accessors\<close>

text \<open>
  Paper "Chunk-plan accessors". Naming: @{text chunk_domain} is the
  keys a chunk \<^emph>\<open>owns\<close>; @{text responsible_chunk} is the
  inverse projecting from a key to its owning chunk;
  @{text canonical_chunk_ownership_domain} is the union of chunk
  domains over all chunks of @{text R}.

  @{text owns} is an @{command abbreviation} over @{text chunk_domain}
  -- @{text "owns R ch k \<equiv> k \<in> chunk_domain R ch"} -- per the paper's
  reader-facing definitional equivalence (paper "Chunk-plan
  accessors": @{text "owns(R, ch, k) :: bool \<Leftrightarrow> k \<in> chunk_domain(R, ch)"}).
  Making it an abbreviation rather than an independent accessor rules
  out any gap where @{text owns} and @{text chunk_domain} could
  disagree on a non-wellformed run.
\<close>

consts
  chunk_domain                       :: "('k, 'v) run \<Rightarrow> ('k, 'v) chunk \<Rightarrow> 'k set"
  responsible_chunk                  :: "('k, 'v) run \<Rightarrow> 'k \<Rightarrow> ('k, 'v) chunk option"

abbreviation owns
  :: "('k, 'v) run \<Rightarrow> ('k, 'v) chunk \<Rightarrow> 'k \<Rightarrow> bool"
where
  "owns R ch k \<equiv> k \<in> chunk_domain R ch"

definition canonical_chunk_ownership_domain
  :: "('k, 'v) run \<Rightarrow> 'k set"
where
  "canonical_chunk_ownership_domain R =
     (\<Union>ch \<in> chunks R. chunk_domain R ch)"

subsection \<open>Chunk watermarks and read coordinates\<close>

text \<open>
  Paper "Watermarks and chunk windows". Three source-coordinate
  accessors per chunk: lower watermark, upper watermark, and the
  actual read coordinate. WF4 (clause body in the paper) requires
  @{text "lower \<le>\<^sub>src read \<le>\<^sub>src upper"}; WF5 additionally requires
  @{text "read \<le>\<^sub>src frontier_of(R)"}.
\<close>

consts
  chunk_lower_watermark   :: "('k, 'v) run \<Rightarrow> ('k, 'v) chunk \<Rightarrow> src_coord"
  chunk_upper_watermark   :: "('k, 'v) run \<Rightarrow> ('k, 'v) chunk \<Rightarrow> src_coord"
  chunk_read_coordinate   :: "('k, 'v) run \<Rightarrow> ('k, 'v) chunk \<Rightarrow> src_coord"

subsection \<open>Canonical clean prefix (Layer 0 building block)\<close>

text \<open>
  Paper "Auxiliary Layer 0 definitions" / "Canonical clean prefix".
  The Layer 0 construction the Layer 1 @{text clean_prefix_of}
  accessor is defined in terms of. Its inputs are typed --- chunk-read
  records, observed-CDC pairs, scope, frontier --- and the paper
  states finiteness premises on them.

  The construction is a real Isabelle @{command definition} mirroring
  the paper's 4-step construction:

    \<^enum> Step 1 (chunk-read Refresh emission). For each
        @{text chunk_read} in @{text chunk_reads} and each
        @{text k} in @{text "crr_domain chunk_read"} with
        @{text "crr_observation chunk_read k = Some m"}, emit
        @{text "Refresh k m (crr_read_coord chunk_read)"}. The
        @{text "crr_domain"} set enumeration uses
        @{const sorted_list_of_set} (requires @{class linorder}
        on the @{text 'k} type variable; surfaces the implicit
        deterministic-enumeration assumption the paper makes when
        it speaks of \"for each k in domain\").

    \<^enum> Step 2 (Cdc emission, scope+frontier filter). For each
        @{text "(c, e)"} in @{text cdc_events} with
        @{text "key_of e \<in> scope"} and @{text "c \<le> frontier"},
        emit @{text "Cdc c e"}.

    \<^enum> Step 3 (interleave by source coordinate). Stable
        @{const sort_key} by @{const cdc_coord}: at any coord
        @{text c}, the Cdcs (input order: cdc_events list) come
        before the Refreshes (input order: chunk_reads list). The
        Cdc-before-Refresh same-coord convention is realized by
        placing the Cdc-events list FIRST in the concatenated
        input to @{const sort_key}; @{const sort_key} is stable,
        so same-coord same-type relative order is preserved.

    \<^enum> Step 4 (retain duplicate stutters). The construction
        does not deduplicate; same-coord same-key duplicates are
        preserved. Apply's per-key fold semantics (Lemma 0.1
        latest-event-wins) handles intra-batch duplicates at the
        state level.

  The suppression-dominance step is split into a raw form (this
  @{text canonical_clean_prefix}) and a normalized form
  (@{text canonical_clean_prefix_normalized}); the two produce
  Apply-equivalent per-key states --- proved below as
  @{text apply_canonical_clean_prefix_normalized_eq} (paper
  "Suppression dominance" / "Apply state-equivalence remark"). The
  Layer 1 definitional equality picks the raw form; deployments may
  pre-normalize and remain wellformed under the same predicate.

  Five properties of @{text "clean_prefix_of(R)"} are load-bearing
  downstream --- refresh-generated, cdc-generated, no-future-cdcs,
  no-extra-events, coord-ordered --- and are derived as the separate
  Layer 2 supporting lemmas below.
\<close>

text \<open>
  Helper accessors used by the construction's interleave + the
  normalized companion's suppression filter. @{const event_key}
  and @{const is_refresh} live in theory @{text Replay} as Layer 0
  projectors on @{typ "('k, 'v) replay_event"}; this theory
  imports them transitively.
\<close>

text \<open>
  Step 1 builder: per chunk_read record, emit one Refresh per
  in-domain key with an observation. The
  @{const sorted_list_of_set} enumeration requires @{class linorder}
  on the @{text 'k} type variable and a finite
  @{text "crr_domain"} (the latter is a paper-level construction
  premise; if violated, @{const sorted_list_of_set} returns
  @{term "[]"} and the construction emits no Refreshes for that
  chunk read).
\<close>

definition chunk_read_refreshes
  :: "('k :: linorder, 'v) chunk_read_record \<Rightarrow> ('k, 'v) replay_event list"
where
  "chunk_read_refreshes r =
     List.map_filter
       (\<lambda>k. case crr_observation r k of
              Some m \<Rightarrow> Some (Refresh k m (crr_read_coord r))
            | None   \<Rightarrow> None)
       (sorted_list_of_set (crr_domain r))"

text \<open>
  Step 2 builder: filter @{text cdc_events} by scope + frontier
  and lift to @{text "Cdc c e"} replay events. Preserves input
  list order.
\<close>

definition cdc_event_replays
  :: "'k set \<Rightarrow> src_coord
       \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list
       \<Rightarrow> ('k, 'v) replay_event list"
where
  "cdc_event_replays scope frontier es =
     List.map_filter
       (\<lambda>p. if key_of (snd p) \<in> scope \<and> fst p \<le> frontier
            then Some (Cdc (fst p) (snd p))
            else None)
       es"

text \<open>
  The construction proper. Steps 1+2 generate the Refresh and Cdc
  event lists; step 3 interleaves them by source coordinate via
  stable @{const sort_key}; step 4 is implicit (no deduplication).
  The Cdc-event list is placed FIRST in the @{const sort_key} input
  so that, at any same source coordinate, Cdcs precede Refreshes
  (the same-coord read convention from paper "Source state").
\<close>

definition canonical_clean_prefix
  :: "('k :: linorder, 'v) chunk_read_record list
       \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list
       \<Rightarrow> 'k set
       \<Rightarrow> src_coord
       \<Rightarrow> ('k, 'v) replay_event list"
where
  "canonical_clean_prefix chunk_reads cdc_events scope frontier =
     sort_key cdc_coord
       (cdc_event_replays scope frontier cdc_events
        @ concat (map chunk_read_refreshes chunk_reads))"

text \<open>
  Suppression dominance: a Refresh at position @{text i} is
  dominated when some later position carries a non-Refresh
  (i.e., a Cdc) event for the same key at a strictly later source
  coordinate. Cdc events are never themselves dominated.
\<close>

definition refresh_dominated
  :: "('k, 'v) replay_event list \<Rightarrow> nat \<Rightarrow> bool"
where
  "refresh_dominated \<sigma> i \<longleftrightarrow>
     i < length \<sigma> \<and> is_refresh (\<sigma> ! i) \<and>
     (\<exists> j. i < j \<and> j < length \<sigma>
            \<and> \<not> is_refresh (\<sigma> ! j)
            \<and> src_lt (cdc_coord (\<sigma> ! i)) (cdc_coord (\<sigma> ! j))
            \<and> event_key (\<sigma> ! j) = event_key (\<sigma> ! i))"

definition canonical_clean_prefix_normalized
  :: "('k :: linorder, 'v) chunk_read_record list
       \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list
       \<Rightarrow> 'k set
       \<Rightarrow> src_coord
       \<Rightarrow> ('k, 'v) replay_event list"
where
  "canonical_clean_prefix_normalized chunk_reads cdc_events scope frontier =
     (let \<sigma> = canonical_clean_prefix chunk_reads cdc_events scope frontier
      in map (\<lambda>i. \<sigma> ! i)
             (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>]))"

subsection \<open>Normalized clean prefix: Apply-equivalence to the raw form\<close>

text \<open>
  Paper "Suppression dominance" / "Apply state-equivalence remark":
  @{const canonical_clean_prefix_normalized} (dominated refreshes
  suppressed) and the raw @{const canonical_clean_prefix} produce the
  same per-key @{const Apply} state. This is the machine-checked
  "proof-facing bridge" the paper relies on when it says a deployment
  may pre-normalize and remain wellformed under the same predicate.

  The argument: @{const Apply} is latest-event-wins per key
  (@{thm [source] apply_eq_apply_filter_key}), so @{term "Apply \<sigma> k"}
  is fixed by the last @{text k}-event of @{text \<sigma>}. A position that
  @{const refresh_dominated} removes is a refresh that has a strictly
  later same-key event, so it is never the last @{text k}-event;
  conversely the last @{text k}-event is never @{const refresh_dominated}
  and therefore survives normalization, in the same final position.
  Hence every key's last event --- and so @{const Apply} --- is
  unchanged.
\<close>

lemma cpn_filter_swap:
  "filter P (filter Q xs) = filter Q (filter P xs)"
  by (induction xs) auto

lemma cpn_sorted_filter:
  fixes xs :: "nat list"
  shows "sorted xs \<Longrightarrow> sorted (filter P xs)"
  by (induction xs) auto

lemma cpn_sorted_le_last:
  fixes zs :: "nat list"
  assumes "sorted zs" and "zs \<noteq> []" and "z \<in> set zs"
  shows "z \<le> last zs"
proof -
  from \<open>z \<in> set zs\<close> obtain m where m: "m < length zs" "zs ! m = z"
    by (meson in_set_conv_nth)
  have "m \<le> length zs - 1" using m(1) by simp
  moreover have "length zs - 1 < length zs" using \<open>zs \<noteq> []\<close> by simp
  ultimately have "zs ! m \<le> zs ! (length zs - 1)"
    using \<open>sorted zs\<close> sorted_nth_mono by blast
  thus ?thesis using m(2) \<open>zs \<noteq> []\<close> by (simp add: last_conv_nth)
qed

text \<open>
  If two replay-event lists agree on whether they carry any
  @{text k}-event, and (when they do) on the last @{text k}-event,
  then @{const Apply} agrees on @{text k}: @{const Apply} at a key is
  fixed by that key's last event.
\<close>

lemma cpn_apply_eq_of_filter_key_last:
  fixes xs ys :: "('k, 'v) replay_event list" and k :: 'k
  assumes empty_iff:
      "(filter (\<lambda>e. event_key e = k) xs = [])
         = (filter (\<lambda>e. event_key e = k) ys = [])"
  assumes last_eq:
      "filter (\<lambda>e. event_key e = k) xs \<noteq> []
         \<Longrightarrow> last (filter (\<lambda>e. event_key e = k) xs)
              = last (filter (\<lambda>e. event_key e = k) ys)"
  shows "Apply xs k = Apply ys k"
proof -
  have ax: "Apply xs k = Apply (filter (\<lambda>e. event_key e = k) xs) k"
    by (rule apply_eq_apply_filter_key)
  have ay: "Apply ys k = Apply (filter (\<lambda>e. event_key e = k) ys) k"
    by (rule apply_eq_apply_filter_key)
  show ?thesis
  proof (cases "filter (\<lambda>e. event_key e = k) xs = []")
    case True
    with empty_iff have "filter (\<lambda>e. event_key e = k) ys = []" by simp
    with True ax ay show ?thesis by (simp add: Apply_def)
  next
    case False
    with empty_iff have yne: "filter (\<lambda>e. event_key e = k) ys \<noteq> []" by simp
    have xu: "\<forall>e\<in>set (filter (\<lambda>e. event_key e = k) xs). event_key e = k"
      by auto
    have yu: "\<forall>e\<in>set (filter (\<lambda>e. event_key e = k) ys). event_key e = k"
      by auto
    have e1: "Apply (filter (\<lambda>e. event_key e = k) xs) k
              = (case last (filter (\<lambda>e. event_key e = k) xs) of
                   Cdc _ (Insert _ v) \<Rightarrow> Some v
                 | Cdc _ (Update _ v) \<Rightarrow> Some v
                 | Cdc _ (Delete _)   \<Rightarrow> None
                 | Refresh _ m_obs _  \<Rightarrow> m_obs)"
      by (rule apply_filter_uniform_last[OF xu False])
    have e2: "Apply (filter (\<lambda>e. event_key e = k) ys) k
              = (case last (filter (\<lambda>e. event_key e = k) ys) of
                   Cdc _ (Insert _ v) \<Rightarrow> Some v
                 | Cdc _ (Update _ v) \<Rightarrow> Some v
                 | Cdc _ (Delete _)   \<Rightarrow> None
                 | Refresh _ m_obs _  \<Rightarrow> m_obs)"
      by (rule apply_filter_uniform_last[OF yu yne])
    show ?thesis using ax ay e1 e2 last_eq[OF False] by simp
  qed
qed

theorem apply_canonical_clean_prefix_normalized_eq:
  fixes chunk_reads :: "('k :: linorder, 'v) chunk_read_record list"
    and cdc_events  :: "(src_coord \<times> ('k, 'v) source_event) list"
    and scope       :: "'k set"
    and frontier    :: src_coord
  shows "Apply (canonical_clean_prefix_normalized chunk_reads cdc_events scope frontier)
         = Apply (canonical_clean_prefix chunk_reads cdc_events scope frontier)"
proof (intro ext)
  fix k :: 'k
  define \<sigma> where "\<sigma> = canonical_clean_prefix chunk_reads cdc_events scope frontier"
  have norm_unfold:
    "canonical_clean_prefix_normalized chunk_reads cdc_events scope frontier
       = map (\<lambda>i. \<sigma> ! i) (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>])"
    by (simp add: canonical_clean_prefix_normalized_def Let_def \<sigma>_def)
  define J  where "J  = filter (\<lambda>i. event_key (\<sigma> ! i) = k) [0..<length \<sigma>]"
  define Jn where "Jn = filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) J"
  have sigma_k: "filter (\<lambda>e. event_key e = k) \<sigma> = map (\<lambda>i. \<sigma> ! i) J"
  proof -
    have "filter (\<lambda>e. event_key e = k) \<sigma>
            = filter (\<lambda>e. event_key e = k) (map (\<lambda>i. \<sigma> ! i) [0..<length \<sigma>])"
      by (simp only: map_nth)
    also have "\<dots> = map (\<lambda>i. \<sigma> ! i)
                      (filter (\<lambda>i. event_key (\<sigma> ! i) = k) [0..<length \<sigma>])"
      by (simp add: filter_map o_def)
    finally show ?thesis by (simp add: J_def)
  qed
  have norm_k: "filter (\<lambda>e. event_key e = k)
                  (map (\<lambda>i. \<sigma> ! i)
                       (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>]))
                = map (\<lambda>i. \<sigma> ! i) Jn"
  proof -
    have "filter (\<lambda>e. event_key e = k)
            (map (\<lambda>i. \<sigma> ! i)
                 (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>]))
          = map (\<lambda>i. \<sigma> ! i)
              (filter (\<lambda>i. event_key (\<sigma> ! i) = k)
                 (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>]))"
      by (simp add: filter_map o_def)
    also have "\<dots> = map (\<lambda>i. \<sigma> ! i) Jn"
      by (subst cpn_filter_swap) (simp add: J_def Jn_def)
    finally show ?thesis .
  qed
  have sortedJ: "sorted J" by (simp add: J_def cpn_sorted_filter)
  have keyJ: "\<And>i. i \<in> set J \<Longrightarrow> i < length \<sigma> \<and> event_key (\<sigma> ! i) = k"
    by (simp add: J_def)
  have crux: "J \<noteq> [] \<Longrightarrow> \<not> refresh_dominated \<sigma> (last J)"
  proof (rule notI)
    assume Jne: "J \<noteq> []" and dom: "refresh_dominated \<sigma> (last J)"
    have lin: "last J \<in> set J" using Jne by simp
    from dom obtain j where j: "last J < j" "j < length \<sigma>"
        "event_key (\<sigma> ! j) = event_key (\<sigma> ! (last J))"
      unfolding refresh_dominated_def by blast
    from keyJ[OF lin] j(3) have "event_key (\<sigma> ! j) = k" by simp
    with j(2) have "j \<in> set J" by (simp add: J_def)
    with sortedJ Jne have "j \<le> last J" by (simp add: cpn_sorted_le_last)
    with j(1) show False by simp
  qed
  have emptyiff:
    "(filter (\<lambda>e. event_key e = k)
        (map (\<lambda>i. \<sigma> ! i)
             (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>])) = [])
     = (filter (\<lambda>e. event_key e = k) \<sigma> = [])"
  proof -
    have "(Jn = []) = (J = [])"
    proof
      assume "J = []" thus "Jn = []" by (simp add: Jn_def)
    next
      assume Jnnil: "Jn = []"
      show "J = []"
      proof (rule ccontr)
        assume Jne: "J \<noteq> []"
        have "last J \<in> set Jn"
          using Jne crux[OF Jne] by (simp add: Jn_def)
        with Jnnil show False by simp
      qed
    qed
    thus ?thesis by (simp add: sigma_k norm_k)
  qed
  have lasteq:
    "filter (\<lambda>e. event_key e = k)
       (map (\<lambda>i. \<sigma> ! i)
            (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>])) \<noteq> []
     \<Longrightarrow> last (filter (\<lambda>e. event_key e = k)
            (map (\<lambda>i. \<sigma> ! i)
                 (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>])))
          = last (filter (\<lambda>e. event_key e = k) \<sigma>)"
  proof -
    assume "filter (\<lambda>e. event_key e = k)
              (map (\<lambda>i. \<sigma> ! i)
                   (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>])) \<noteq> []"
    hence Jnne: "Jn \<noteq> []" by (simp add: norm_k)
    hence Jne: "J \<noteq> []" by (auto simp: Jn_def)
    have lastJn: "last Jn = last J"
    proof -
      have "Jn = filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) (butlast J @ [last J])"
        by (simp add: Jn_def append_butlast_last_id[OF Jne])
      also have "\<dots> = filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) (butlast J) @ [last J]"
        using crux[OF Jne] by simp
      finally show ?thesis by simp
    qed
    have "last (map (\<lambda>i. \<sigma> ! i) Jn) = \<sigma> ! (last Jn)"
      using Jnne by (simp add: last_map)
    also have "\<dots> = \<sigma> ! (last J)" by (simp add: lastJn)
    also have "\<dots> = last (map (\<lambda>i. \<sigma> ! i) J)"
      using Jne by (simp add: last_map)
    finally show ?thesis by (simp add: sigma_k norm_k)
  qed
  show "Apply (canonical_clean_prefix_normalized chunk_reads cdc_events scope frontier) k
        = Apply (canonical_clean_prefix chunk_reads cdc_events scope frontier) k"
    unfolding norm_unfold \<sigma>_def[symmetric]
    by (rule cpn_apply_eq_of_filter_key_last[OF emptyiff lasteq])
qed

subsection \<open>Layer 1 clean-prefix definitional equality (clean_prefix_of)\<close>

text \<open>
  Paper "Clean-prefix construction at Layer 1": Layer 1's
  @{text "clean_prefix_of(R)"} is not a fresh primitive -- it is the
  Layer 0 @{text canonical_clean_prefix} building block instantiated
  for the run, with the chunk-read argument lifted out of an opaque
  "observed rows" assertion into per-chunk @{type chunk_read_record}
  values populated from the named accessors @{const chunk_domain},
  @{const chunk_read_coordinate}, and @{const chunk_read_result}, and
  with the CDC-side argument lifted out of "the source history's
  events" into the run-derived @{const cdc_events_of} accessor.

  @{text clean_prefix_of} is a real @{command definition} via this
  Layer 1 definitional equality. The signature carries a
  @{class linorder} constraint on @{text 'k} (propagated from
  @{text canonical_clean_prefix}); consumers (@{text wellformed_dblog_run},
  the Layer 2 source-side soundness theorem, downstream Layer 3
  certificate composition) inherit the constraint.

  Consequences:

    \<^item> the run carrier does not have to commit independently to a
        clean-prefix list shape; the wellformed-DBLog-run predicate's
        body constrains the run's @{const chunk_read_result},
        @{const chunks}, @{const scope_of}, @{const src_history_of},
        @{const cdc_events_of}, and @{const frontier_of} accessors,
        and @{text clean_prefix_of} is then determined by the
        construction;
    \<^item> the Layer 2 source-side soundness theorem can reason about
        @{text "clean_prefix_of(R)"} as a closed-form expression in
        the run's accessors, without needing a separate "clean prefix
        is some interleaving of chunk reads and CDC events"
        wellformedness clause;
    \<^item> the potential counterexample shape --- a
        @{text Cdc}-before-@{text Refresh} order at distinct source
        coordinates that satisfies all set-membership-shaped WF
        clauses but breaks the Layer 2 conclusion --- is structurally
        neutralized: under the construction body,
        @{text "clean_prefix_of(R)"} is sorted by source coordinate,
        so a low-coord @{text Cdc} cannot follow a high-coord
        @{text Refresh} for the same key.
\<close>

definition clean_prefix_of
  :: "('k :: linorder, 'v) run \<Rightarrow> ('k, 'v) replay_event list"
where
  "clean_prefix_of R =
     canonical_clean_prefix
       (map (\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                    crr_read_coord  = chunk_read_coordinate R ch,
                    crr_observation = chunk_read_result R ch \<rparr>)
            (chunks_list R))
       (cdc_events_of R)
       (scope_of R)
       (frontier_of R)"

subsection \<open>Coverage predicates\<close>

text \<open>
  Paper "Coverage predicates". @{text covers_ordinary_cdc} unwraps
  @{text responsible_chunk}'s @{text option} via an existential and
  compares against @{text cdc_events_of} (the run's observed CDC
  events) rather than @{text src_history_of} (the true source
  history); @{text row_absence_meaningful} is parameterised against
  @{text "Src b0 H (chunk_read_coordinate R ch) k = None"} rather
  than against an unstated "k was never inserted or deleted" reading.

  @{text covers_ordinary_cdc} is a real @{command definition}
  transliterating the paper "Coverage predicates" /
  "covers_ordinary_cdc(R, k, f)" body. The half-open interval
  @{text "(chunk_read_coordinate R ch, f]"} becomes
  @{text "src_lt (chunk_read_coordinate R ch) (hist_coord p)
  \<and> src_le (hist_coord p) f"} (strict on left, inclusive on right);
  the paper's "is reflected, with the same source coordinate, as a
  @{text "(c, e)"} pair in @{text "cdc_events_of(R)"}" becomes
  @{text "src_history_of R ! i \<in> set (cdc_events_of R)"} (the
  @{text "(c, e)"} pair preserved by element identity).

  @{text row_absence_meaningful} is a 5-argument predicate
  @{text "row_absence_meaningful b0 H R ch k"}, a real
  @{command definition} capturing the formalizable structural +
  source-state implication: if the key is in the chunk's domain and
  the chunk read for it produced an absence-Refresh in the clean
  prefix, then the source state at the chunk-read coordinate is
  absent (paper "Coverage predicates" / "row_absence_meaningful").
  WF6 (below) invokes it with the implication
  @{text "chunk_read_result R ch k = Some None \<longrightarrow>
  row_absence_meaningful b0 H R ch k"} on in-domain keys. That WF6
  implication is logically auto-satisfied under WF4 + WF6 main: WF4's
  @{text Refresh}-iff puts the structural antecedent of the
  predicate's body into scope when @{text "chunk_read_result = Some None"},
  and WF6 main forces @{text "Src b0 H (chunk_read_coordinate R ch) k = None"}.
  The predicate's role is structural rather than gating: the
  paper-side invocation exposes the deployment-level "no error / no
  partial result" obligation as reader-facing prose, and the
  formal-side predicate provides the type-level hook a deployment
  locale can axiomatize against if a stronger operational obligation
  is to be expressed inside the formal model.
\<close>

definition covers_ordinary_cdc
  :: "('k, 'v) run \<Rightarrow> 'k \<Rightarrow> frontier \<Rightarrow> bool"
where
  "covers_ordinary_cdc R k f \<longleftrightarrow>
     (\<exists> ch. responsible_chunk R k = Some ch
            \<and> (\<forall> i. i < length (src_history_of R)
                     \<longrightarrow> src_lt (chunk_read_coordinate R ch)
                                (hist_coord (src_history_of R ! i))
                     \<longrightarrow> src_le (hist_coord (src_history_of R ! i)) f
                     \<longrightarrow> key_of (hist_event (src_history_of R ! i)) = k
                     \<longrightarrow> src_history_of R ! i \<in> set (cdc_events_of R)))"

definition source_key_coord_slice
  :: "'k \<Rightarrow> src_coord
      \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list
      \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list"
where
  "source_key_coord_slice k c xs =
     filter (\<lambda>p. hist_coord p = c \<and> key_of (hist_event p) = k) xs"

definition row_absence_meaningful
  :: "('k :: linorder \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) src_history \<Rightarrow> ('k, 'v) run \<Rightarrow> ('k, 'v) chunk \<Rightarrow> 'k \<Rightarrow> bool"
where
  "row_absence_meaningful b0 H R ch k \<longleftrightarrow>
     (k \<in> chunk_domain R ch
      \<and> Refresh k None (chunk_read_coordinate R ch) \<in> set (clean_prefix_of R)
      \<longrightarrow> Src b0 H (chunk_read_coordinate R ch) k = None)"

subsection \<open>The wellformed-DBLog-run predicate\<close>

text \<open>
  Paper "The @{text \<open>wellformed-DBLog-run\<close>} predicate". The
  three-argument signature @{text "wellformed_dblog_run b0 R H"}
  threads the source-side baseline @{text b0} through the predicate
  body, so chunk-read observations are checked against
  @{text "Src b0 H (chunk_read_coordinate R ch)"} (clause WF6). The
  7-clause body is:

  \<^item> WF0: source-history binding (@{text "src_history_of R = H"} +
    @{text "wellformed_src_history H"});
  \<^item> WF1: strict canonical chunk partition over scope +
    @{text responsible_chunk} coherence + finite-domain / finite-
    scope + non-empty-chunk-domain obligations (sub-clauses
    (a)\<dots>(g));
  \<^item> WF2: ordinary-CDC coverage on every key in scope (paper
    @{text covers_ordinary_cdc}) + observed-CDC order-preserving
    sublist coherence against @{text src_history_of} on the
    in-scope / at-or-before-frontier slice + post-read same-key /
    same-coordinate multiplicity. The order-preserving sublist
    condition strengthens a membership-only faithfulness condition
    with source-position-order preservation; this is what rules out
    a same-coordinate CDC-order reversal, where two source events at
    one coordinate appear in @{text cdc_events_of} in the opposite
    order to @{text src_history_of} and break the Layer 2 conclusion.
    The post-read multiplicity conjunct requires, for an in-scope
    key, that every source coordinate strictly after its responsible
    chunk read and at-or-before the frontier carries the same
    multiset of matching records in @{text cdc_events_of} as in
    @{text src_history_of}, closing the duplicate-record gap in the
    Cdc case of the per-key replay-equality lemma;
  \<^item> (no WF3 -- the numbering carries a deliberate gap recording a
    clause the model no longer uses);
  \<^item> WF4: chunk-read evidence (watermark bracketing +
    @{text chunk_read_result} totality on chunk domain +
    @{text Refresh}-event agreement with @{text chunk_read_result});
  \<^item> WF5: chunk-read coordinate at-or-before frontier;
  \<^item> WF6: refresh correctness against
    @{text "Src b0 H (chunk_read_coordinate R ch)"}; AND, when
    @{text "chunk_read_result R ch k = Some None"} is observed for
    an in-domain key, @{text "row_absence_meaningful b0 H R ch k"}
    holds (the implication is auto-satisfied under WF4 + WF6 main,
    see the Coverage predicates header above);
  \<^item> WF7: clean-prefix CDC coherence -- bidirectional coherence
    between @{text "cdc_events_of(R)"} and @{text Cdc} events in
    @{text "clean_prefix_of(R)"} on the in-scope / at-or-before-
    frontier filter.

  @{text wellformed_dblog_run} is a real @{command definition}
  transliterating the paper "wellformed-DBLog-run predicate" body.

  Two of the clauses warrant a closer note.

  WF7 (clean-prefix CDC coherence) makes explicit a fact that is
  otherwise only implicit in @{text covers_ordinary_cdc}'s
  parenthetical "so that @{text "Cdc c e"} appears in
  @{text "clean_prefix_of(R)"}". With WF7, the body enforces both
  directions --- forward: @{text cdc_events_of} \<rightarrow>
  @{text clean_prefix_of}; reverse: @{text clean_prefix_of} \<rightarrow>
  @{text cdc_events_of} --- on the in-scope / at-or-before-frontier
  filter.

  WF2's order-preservation conjunct is the order-preserving sublist
  condition: there exists a strictly increasing index function
  @{text \<iota>} from indices of (the in-scope, at-or-before-frontier
  filter on @{text "cdc_events_of(R)"}) into indices of (the same
  filter on @{text "src_history_of(R)"}) with elements matching
  pairwise. This is equivalent to "@{text "cdc_events_of(R)"} is an
  order-preserving sublist of @{text "src_history_of(R)"} on that
  slice". A bare membership condition would permit the
  same-coordinate reversal
  @{text "H = [(c, Update k v1), (c, Update k v2)]"} versus
  @{text "cdc_events_of(R) = [(c, Update k v2), (c, Update k v1)]"},
  where set membership holds both ways but the source-position order
  is reversed, causing @{text "Apply (clean_prefix_of R) k"} to
  disagree with @{text "Src b0 H (frontier_of R) k"} on the in-scope
  key @{text k}. The membership condition is kept as a separate
  conjunct alongside the order-preserving one (it is logically
  subsumed, but stating it explicitly keeps the extraction proofs
  simple). The @{text covers_ordinary_cdc} forward direction is
  independent and still requires coverage in the post-chunk-read
  interval.
\<close>

definition wellformed_dblog_run
  :: "('k :: linorder \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) run \<Rightarrow> ('k, 'v) src_history \<Rightarrow> bool"
where
  "wellformed_dblog_run b0 R H \<longleftrightarrow>
     \<comment> \<open>WF0: source-history binding\<close>
     src_history_of R = H \<and> wellformed_src_history H
   \<and>
     \<comment> \<open>WF1 (a): \<exists>! responsible chunk per in-scope key\<close>
     (\<forall> k \<in> scope_of R. \<exists>! ch. ch \<in> chunks R \<and> owns R ch k)
   \<and>
     \<comment> \<open>WF1 (b): chunk domains are pairwise disjoint\<close>
     (\<forall> ch1 \<in> chunks R. \<forall> ch2 \<in> chunks R.
        ch1 \<noteq> ch2 \<longrightarrow> chunk_domain R ch1 \<inter> chunk_domain R ch2 = {})
   \<and>
     \<comment> \<open>WF1 (c): canonical chunk-ownership domain equals scope\<close>
     canonical_chunk_ownership_domain R = scope_of R
   \<and>
     \<comment> \<open>WF1 (d): responsible_chunk \<longleftrightarrow> ownership predicate (in scope)\<close>
     (\<forall> k \<in> scope_of R. \<forall> ch.
        responsible_chunk R k = Some ch
          \<longleftrightarrow> ch \<in> chunks R \<and> owns R ch k)
   \<and>
     \<comment> \<open>WF1 (e): out-of-scope keys have no responsible chunk\<close>
     (\<forall> k. k \<notin> scope_of R \<longrightarrow> responsible_chunk R k = None)
   \<and>
     \<comment> \<open>WF1 (f): scope and chunk domains are finite\<close>
     finite (scope_of R)
   \<and> (\<forall> ch \<in> chunks R. finite (chunk_domain R ch))
   \<and>
     \<comment> \<open>WF1 (g): every chunk has a non-empty domain --- no
         inert dead chunks. With WF1 (a)-(f) this makes the chunks
         of R a strict partition of scope_of R (a partition has
         non-empty parts). An empty-domain chunk would be inert ---
         it owns no key and emits no Refresh events --- so this
         clause is not needed for the headline theorems; it is
         included so the formal body matches the paper's
         strict-partition wording.\<close>
     (\<forall> ch \<in> chunks R. chunk_domain R ch \<noteq> {})
   \<and>
     \<comment> \<open>WF2 (coverage): observed CDC reaches every in-scope key
         through the frontier (paper covers_ordinary_cdc)\<close>
     (\<forall> k \<in> scope_of R. covers_ordinary_cdc R k (frontier_of R))
   \<and>
     \<comment> \<open>WF2 (faithfulness): observed CDC events that fall in scope
         and at-or-before frontier are real source events
         (membership condition). Logically subsumed by the
         order-preservation clause below (strict-monotonic indexing
         implies pairwise membership), but kept explicit as a
         separate conjunct so that the extraction proofs need not
         derive it from the embedding.\<close>
     (\<forall> p \<in> set (cdc_events_of R).
        key_of (hist_event p) \<in> scope_of R
        \<and> src_le (hist_coord p) (frontier_of R)
        \<longrightarrow> p \<in> set (src_history_of R))
   \<and>
     \<comment> \<open>WF2 (order-preserving sublist): on the in-scope /
         at-or-before-frontier slice, cdc_events_of(R) is an
         order-preserving sublist of src_history_of(R). The
         strict-monotonic indexing embedding strengthens the
         membership-only WF2 faithfulness clause above with
         source-position-order preservation, ruling out the
         same-coordinate CDC-order reversal. Consumed by the
         supporting lemma cdc_events_key_coord_slice_subseq_source_history_slice
         below, which extracts this strict-monotonic embedding to
         show the per-key / per-coordinate CDC slice is an
         order-preserving subsequence of the source-history slice,
         and through it by
         cdc_events_key_coord_slice_eq_source_history_slice_from_wf.\<close>
     (\<exists> \<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
        \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of R
                                 \<and> src_le (hist_coord p) (frontier_of R));
               cdc_in_slice  = filter in_slice (cdc_events_of R);
               hist_in_slice = filter in_slice (src_history_of R)
           in \<forall> i. i < length cdc_in_slice \<longrightarrow>
                   \<iota> i < length hist_in_slice
                 \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i))
   \<and>
     \<comment> \<open>WF2 (post-read same-key/same-coordinate multiplicity):
         for an in-scope key k, any source coordinate c strictly
         after k's responsible chunk read and at-or-before the run
         frontier has the same multiset of matching source records
         in cdc_events_of(R) as in src_history_of(R). Together with
         the order-preserving sublist clause, this closes the
         duplicate-record gap in the Cdc case of the per-key
         replay-equality lemma without requiring global
         source-history distinctness. Multiset equality rather than
         set membership is essential: an [A, B, A] source slice
         versus an [A, B] CDC slice is rejected by multiplicity,
         while a same-multiset permutation such as [A, B, A] versus
         [A, A, B] is excluded instead by the order-preserving
         sublist clause above.\<close>
     (\<forall> k \<in> scope_of R. \<forall> ch c.
        responsible_chunk R k = Some ch
        \<and> src_lt (chunk_read_coordinate R ch) c
        \<and> src_le c (frontier_of R)
        \<longrightarrow>
          mset (source_key_coord_slice k c (cdc_events_of R))
          = mset (source_key_coord_slice k c (src_history_of R)))
   \<and>
     \<comment> \<open>(no WF3 -- the numbering carries a deliberate gap
         recording a clause the model no longer uses)\<close>
     \<comment> \<open>WF4: chunk-read evidence (watermark bracketing +
         chunk_read_result totality on domain + Refresh-event
         agreement with chunk_read_result on domain)\<close>
     (\<forall> ch \<in> chunks R.
        src_le (chunk_lower_watermark R ch) (chunk_read_coordinate R ch)
      \<and> src_le (chunk_read_coordinate R ch) (chunk_upper_watermark R ch)
      \<and> (\<forall> k \<in> chunk_domain R ch.
           \<exists> m. chunk_read_result R ch k = Some m)
      \<and> (\<forall> k \<in> chunk_domain R ch. \<forall> m.
           chunk_read_result R ch k = Some m
             \<longleftrightarrow> Refresh k m (chunk_read_coordinate R ch)
                  \<in> set (clean_prefix_of R)))
   \<and>
     \<comment> \<open>WF5: chunk-read coordinate at-or-before frontier\<close>
     (\<forall> ch \<in> chunks R.
        src_le (chunk_read_coordinate R ch) (frontier_of R))
   \<and>
     \<comment> \<open>WF6 (main): refresh correctness against
         Src b0 H (chunk_read_coordinate R ch) k.\<close>
     (\<forall> ch \<in> chunks R. \<forall> k \<in> chunk_domain R ch. \<forall> m.
        chunk_read_result R ch k = Some m
          \<longrightarrow> m = Src b0 H (chunk_read_coordinate R ch) k)
   \<and>
     \<comment> \<open>WF6 (row-absence meaningfulness): when
         chunk_read_result R ch k = Some None is observed for an
         in-domain key, row_absence_meaningful b0 H R ch k holds.
         Auto-satisfied under WF4 + WF6 main; carries the paper's
         WF6 row-absence content into the formal body.\<close>
     (\<forall> ch \<in> chunks R. \<forall> k \<in> chunk_domain R ch.
        chunk_read_result R ch k = Some None
          \<longrightarrow> row_absence_meaningful b0 H R ch k)
   \<and>
     \<comment> \<open>WF7 (clean-prefix CDC coherence): forward direction --
         every observed CDC event whose key is in scope and whose
         coordinate is at-or-before frontier appears as a Cdc replay
         event in clean_prefix_of(R).\<close>
     (\<forall> p \<in> set (cdc_events_of R).
        key_of (hist_event p) \<in> scope_of R
        \<and> src_le (hist_coord p) (frontier_of R)
        \<longrightarrow> Cdc (hist_coord p) (hist_event p)
              \<in> set (clean_prefix_of R))
   \<and>
     \<comment> \<open>WF7 (clean-prefix CDC coherence): reverse direction --
         every Cdc replay event in clean_prefix_of(R) whose key is
         in scope and whose coordinate is at-or-before frontier is
         justified by the corresponding pair in cdc_events_of(R).\<close>
     (\<forall> e c. Cdc c e \<in> set (clean_prefix_of R)
                \<and> key_of e \<in> scope_of R
                \<and> src_le c (frontier_of R)
                \<longrightarrow> (c, e) \<in> set (cdc_events_of R))"

subsection \<open>Lemma 0.5 -- Refresh events represent source state at chunk-read coordinate\<close>

text \<open>
  Paper "Layer 0 basic lemmas" / "Lemma 0.5": for any wellformed
  source history @{text H}, any base state @{text b0}, and any
  chunk read at coordinate @{text c} whose observation for key
  @{text k} is @{text m}, \<^emph>\<open>if\<close> the chunk read honestly
  observed the source at coordinate @{text c}, \<^emph>\<open>then\<close> the
  replay event @{term "Refresh k m c"} carries the same value
  that @{term "Src b0 H c"} would compute for @{text k}:
  @{text "m = Src b0 H c k"}.

  The lemma is Conditional on the chunk-read honest-observation
  premise; in the formal spine, the honest-observation premise
  is folded into the @{const wellformed_dblog_run} body as the
  WF6 main clause. So the Isabelle form of Lemma 0.5 carries
  @{const wellformed_dblog_run} as a premise (along with chunk +
  domain + observed-value membership) and concludes the per-key
  value equality at the chunk-read coordinate.

  Proof: the lemma is the direct extraction of the WF6 main clause
  from the @{const wellformed_dblog_run} body. Unfold the body with
  @{text wellformed_dblog_run_def} and apply @{text blast} to pick up
  the WF6 main conjunct.

  Its value to consumers (the Layer 2 per-key replay-equality lemma,
  and Layer 3 trust-boundary reasoning) is to name the WF6 extraction
  explicitly: rather than unfold @{text wellformed_dblog_run_def} at
  every Refresh-case invocation, consumers cite this lemma. The
  result remains @{text Conditional} on chunk-read honesty --- that
  hypothesis is the external observation assumption discharged at
  deployment, and Layer 2 carries it as a premise via WF6 main.
\<close>

theorem refresh_coordinate_match:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v" and R :: "('k, 'v) run"
    and H :: "('k, 'v) src_history" and ch :: "('k, 'v) chunk"
    and k :: 'k and m :: "'v option"
  assumes wf:  "wellformed_dblog_run b0 R H"
  assumes ch_in: "ch \<in> chunks R"
  assumes k_in:  "k \<in> chunk_domain R ch"
  assumes obs:   "chunk_read_result R ch k = Some m"
  shows "m = Src b0 H (chunk_read_coordinate R ch) k"
  using assms unfolding wellformed_dblog_run_def by blast

subsection \<open>Layer 2 supporting clean-prefix lemmas\<close>

text \<open>
  The Layer 2 source-side virtual-cut soundness proof is factored
  through a family of structural supporting lemmas about
  @{const clean_prefix_of}.

  The clean_prefix_of_order_respects_coordinate lemma (THIS lemma)
  is the base structural property: @{const clean_prefix_of}
  is constructed via @{const sort_key} on @{const cdc_coord} (see the
  @{const canonical_clean_prefix} definition above), so its
  coordinate projection is non-decreasing under @{const src_le}.
  The remaining supporting clean-prefix lemmas and the headline
  Layer 2 source-side soundness theorem consume this lemma either
  directly or via Lemma 0.1 (latest-event-wins per key). The
  @{const wellformed_dblog_run} premise is included to match the
  common supporting-lemma signature; it is not consumed by this
  lemma itself.
\<close>

lemma clean_prefix_of_order_respects_coordinate:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and R :: "('k, 'v) run"
    and i j :: nat
  assumes "wellformed_dblog_run b0 R H"
      and "i < j"
      and "j < length (clean_prefix_of R)"
  shows "src_le (cdc_coord (clean_prefix_of R ! i))
                (cdc_coord (clean_prefix_of R ! j))"
proof -
  have sorted_cp: "sorted (map cdc_coord (clean_prefix_of R))"
    unfolding clean_prefix_of_def canonical_clean_prefix_def
    by (rule sorted_sort_key)
  from assms(2) have le_ij: "i \<le> j" by simp
  from assms(3) have j_bound:
    "j < length (map cdc_coord (clean_prefix_of R))" by simp
  from sorted_nth_mono[OF sorted_cp le_ij j_bound]
  have "map cdc_coord (clean_prefix_of R) ! i
          \<le> map cdc_coord (clean_prefix_of R) ! j" .
  hence "cdc_coord (clean_prefix_of R ! i)
           \<le> cdc_coord (clean_prefix_of R ! j)"
    using assms(2,3) by (simp add: nth_map)
  thus ?thesis by (simp add: less_eq_src_coord_def)
qed

text \<open>
  The clean_prefix_of_no_future_in_scope_events lemma (THIS lemma)
  bounds @{const clean_prefix_of}'s events on the right by the
  run's frontier: every event in @{text "clean_prefix_of R"}
  has a coordinate @{text "\<le> frontier_of R"}. The proof
  case-splits on the canonical_clean_prefix construction's two
  branches:

  \<^item> Case A (the @{const cdc_event_replays} branch): the
      construction filters @{const cdc_events_of} by the
      frontier predicate, so every @{text Cdc} event in the
      branch has its source coordinate @{text "\<le> frontier_of R"}
      by construction.

  \<^item> Case B (the @{const chunk_read_refreshes} branch): every
      @{text Refresh} event in the branch carries the
      @{const crr_read_coord} of the source chunk-read record,
      which (via the construction's record-mapping) equals
      @{const chunk_read_coordinate} on the run's chunk. WF5
      enforces @{const chunk_read_coordinate} @{text "\<le> frontier_of R"}
      for every @{text "ch \<in> chunks R"}; @{thm chunks_list_set}
      bridges the list-side @{const chunks_list} to the set-side
      @{const chunks}.

  The @{const wellformed_dblog_run} premise is consumed (WF5
  extraction in Case B; WF1 finiteness is not needed because
  membership in @{const chunk_read_refreshes}'s output already
  witnesses domain membership).
\<close>

lemma clean_prefix_of_no_future_in_scope_events:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and R :: "('k, 'v) run"
    and e :: "('k, 'v) replay_event"
  assumes wf: "wellformed_dblog_run b0 R H"
      and e_in: "e \<in> set (clean_prefix_of R)"
  shows "src_le (cdc_coord e) (frontier_of R)"
proof -
  let ?mkRec = "\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                       crr_read_coord  = chunk_read_coordinate R ch,
                       crr_observation = chunk_read_result R ch \<rparr>"
  have split: "e \<in> set (cdc_event_replays (scope_of R) (frontier_of R)
                                          (cdc_events_of R))
             \<or> (\<exists> ch \<in> set (chunks_list R).
                  e \<in> set (chunk_read_refreshes (?mkRec ch)))"
    using e_in
    by (auto simp: clean_prefix_of_def canonical_clean_prefix_def)
  from split show ?thesis
  proof
    assume "e \<in> set (cdc_event_replays (scope_of R) (frontier_of R)
                                       (cdc_events_of R))"
    \<comment> \<open>Case A: e is a Cdc replay event whose coordinate is
        \<le> frontier by the cdc_event_replays filter. The
        @{text less_eq_src_coord_def} unfolding bridges
        \<le> on src_coord to src_le.\<close>
    then show ?thesis
      unfolding cdc_event_replays_def List.map_filter_def
      by (auto split: if_splits simp: less_eq_src_coord_def)
  next
    assume "\<exists> ch \<in> set (chunks_list R).
              e \<in> set (chunk_read_refreshes (?mkRec ch))"
    then obtain ch where
      ch_in: "ch \<in> set (chunks_list R)"
      and e_in_refs: "e \<in> set (chunk_read_refreshes (?mkRec ch))"
      by blast
    \<comment> \<open>Case B: e is a Refresh event whose coordinate equals
        chunk_read_coordinate R ch (by the chunk_read_refreshes
        construction), which is \<le> frontier by WF5.\<close>
    from ch_in have ch_in_chunks: "ch \<in> chunks R"
      using chunks_list_set by blast
    from e_in_refs have e_coord:
      "cdc_coord e = chunk_read_coordinate R ch"
      unfolding chunk_read_refreshes_def List.map_filter_def
      by (auto split: option.splits)
    from wf have wf5:
      "\<forall> ch \<in> chunks R.
          src_le (chunk_read_coordinate R ch) (frontier_of R)"
      unfolding wellformed_dblog_run_def by blast
    from wf5 ch_in_chunks
    have "src_le (chunk_read_coordinate R ch) (frontier_of R)" by blast
    with e_coord show ?thesis by simp
  qed
qed

text \<open>
  The clean_prefix_of_refresh_generated_by_responsible_chunk lemma
  (THIS lemma) is the Refresh-side identification lemma: every
  @{text Refresh} event in @{const clean_prefix_of} is justified
  by a chunk_read_result for an in-scope key, on the chunk that
  owns the key. The proof works backward from the Refresh
  hypothesis:

  \<^item> @{const cdc_event_replays} produces only @{text Cdc} events
      (its emission shape is @{text "Cdc (fst p) (snd p)"}), so
      a @{text Refresh} cannot live there; the disjunction
      established by unfolding @{const clean_prefix_of} +
      @{const canonical_clean_prefix} collapses to the
      @{const chunk_read_refreshes} branch.

  \<^item> The @{const chunk_read_refreshes} emission shape gives
      @{text "Refresh k' m' (crr_read_coord r)"} for some
      @{text k'} with @{text "crr_observation r k' = Some m'"}
      and @{text "k' \<in> crr_domain r"}; pattern-matching against
      the hypothesis @{text "Refresh k m c"} fixes
      @{text "k' = k"}, @{text "m' = m"},
      @{text "c = crr_read_coord r = chunk_read_coordinate R ch"}.

  \<^item> WF1 (c) @{text "canonical_chunk_ownership_domain R = scope_of R"}
      + @{text "k \<in> chunk_domain R ch \<and> ch \<in> chunks R"} \<Longrightarrow>
      @{text "k \<in> scope_of R"}.

  \<^item> WF1 (d) responsible-chunk iff + @{text "ch \<in> chunks R \<and>
      owns R ch k"} (@{const owns} is an abbreviation for
      @{text "k \<in> chunk_domain R ch"}) \<Longrightarrow>
      @{text "responsible_chunk R k = Some ch"}.

  This lemma is ONE-DIRECTIONAL: Refresh in clean_prefix implies
  responsible-chunk identification. The REVERSE direction (in-
  scope responsible-chunk observation \<Longrightarrow> Refresh in clean_prefix)
  is the clean_prefix_of_in_scope_responsible_chunk_refresh_exists
  lemma below.
\<close>

lemma clean_prefix_of_refresh_generated_by_responsible_chunk:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and R :: "('k, 'v) run"
    and k :: 'k
    and m :: "'v option"
    and c :: src_coord
  assumes wf: "wellformed_dblog_run b0 R H"
      and e_in: "Refresh k m c \<in> set (clean_prefix_of R)"
  shows "k \<in> scope_of R
       \<and> (\<exists> ch. responsible_chunk R k = Some ch
              \<and> chunk_read_coordinate R ch = c
              \<and> chunk_read_result R ch k = Some m)"
proof -
  let ?mkRec = "\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                       crr_read_coord  = chunk_read_coordinate R ch,
                       crr_observation = chunk_read_result R ch \<rparr>"
  \<comment> \<open>Refresh events cannot come from the cdc_event_replays
      branch (which produces only Cdc events).\<close>
  have not_cdc:
    "Refresh k m c \<notin> set (cdc_event_replays (scope_of R)
                                            (frontier_of R)
                                            (cdc_events_of R))"
    unfolding cdc_event_replays_def List.map_filter_def
    by auto
  have split:
    "Refresh k m c \<in> set (cdc_event_replays (scope_of R)
                                            (frontier_of R)
                                            (cdc_events_of R))
   \<or> (\<exists> ch \<in> set (chunks_list R).
        Refresh k m c \<in> set (chunk_read_refreshes (?mkRec ch)))"
    using e_in
    by (auto simp: clean_prefix_of_def canonical_clean_prefix_def)
  from split not_cdc obtain ch where
    ch_in: "ch \<in> set (chunks_list R)" and
    refresh_in: "Refresh k m c \<in> set (chunk_read_refreshes (?mkRec ch))"
    by blast
  from ch_in have ch_in_chunks: "ch \<in> chunks R"
    using chunks_list_set by blast
  \<comment> \<open>Extract the conjuncts the downstream steps need: WF1
      (c), WF1 (d), and WF1 (f)'s chunk-domain finiteness.
      @{text blast} on the individual conjuncts can time out
      because of the WF2 strict_mono existential conjunct's
      complexity in the unfolded body; a single simp-based
      unfolding + elimination is faster.\<close>
  note wf_body = wf[unfolded wellformed_dblog_run_def]
  from wf_body have wf1c: "canonical_chunk_ownership_domain R = scope_of R"
    by (elim conjE)
  from wf_body have wf1d:
    "\<forall> k \<in> scope_of R. \<forall> ch.
        responsible_chunk R k = Some ch
          \<longleftrightarrow> ch \<in> chunks R \<and> owns R ch k"
    by (elim conjE)
  from wf_body have wf1f_chunks:
    "\<forall> ch \<in> chunks R. finite (chunk_domain R ch)"
    by (elim conjE)
  from wf1f_chunks ch_in_chunks have fin_dom: "finite (chunk_domain R ch)"
    by blast
  \<comment> \<open>Pattern-match the Refresh against the chunk_read_refreshes
      emission to extract k \<in> chunk_domain R ch, chunk_read_result
      R ch k = Some m, and c = chunk_read_coordinate R ch.\<close>
  from refresh_in fin_dom
  have k_props:
    "k \<in> chunk_domain R ch
   \<and> chunk_read_result R ch k = Some m
   \<and> c = chunk_read_coordinate R ch"
    unfolding chunk_read_refreshes_def List.map_filter_def
    by (auto split: option.splits)
  hence k_in_dom: "k \<in> chunk_domain R ch"
    and crr_res: "chunk_read_result R ch k = Some m"
    and c_eq: "c = chunk_read_coordinate R ch"
    by auto
  \<comment> \<open>Establish k \<in> scope_of R via WF1 (c) + chunk_domain \<subseteq>
      canonical_chunk_ownership_domain.\<close>
  from ch_in_chunks k_in_dom
  have "k \<in> canonical_chunk_ownership_domain R"
    unfolding canonical_chunk_ownership_domain_def by blast
  with wf1c have k_in_scope: "k \<in> scope_of R" by blast
  \<comment> \<open>Establish responsible_chunk R k = Some ch via WF1 (d).\<close>
  from wf1d k_in_scope ch_in_chunks k_in_dom
  have rc: "responsible_chunk R k = Some ch" by blast
  from k_in_scope rc c_eq crr_res show ?thesis by blast
qed

text \<open>
  The clean_prefix_of_in_scope_responsible_chunk_refresh_exists
  lemma (THIS lemma) is the REVERSE direction of
  clean_prefix_of_refresh_generated_by_responsible_chunk: every
  in-scope key has a @{text Refresh} event in
  @{const clean_prefix_of} reflecting the responsible chunk's
  @{const chunk_read_result} observation. Together, the two
  directions establish a full correspondence between
  @{text Refresh}-events in @{const clean_prefix_of} and the
  responsible-chunk's chunk-read observations on in-scope keys; the
  "@{text k} has no event in clean prefix" vacuity case of the
  latest-replay-correspondence proof consumes this lemma.

  The proof is the FORWARD direction of WF4's
  @{text "chunk_read_result \<longleftrightarrow> Refresh-in-clean-prefix"} iff:

  \<^item> WF1 (a) @{text "\<exists>!"} responsible chunk per in-scope key +
      @{const owns} abbreviation @{text "k \<in> chunk_domain R ch"}
      \<Longrightarrow> a chunk @{text "ch \<in> chunks R"} with
      @{text "k \<in> chunk_domain R ch"} exists.

  \<^item> WF4 totality @{text "\<forall> k \<in> chunk_domain R ch. \<exists> m.
      chunk_read_result R ch k = Some m"} \<Longrightarrow> an observation
      @{text "m"} exists.

  \<^item> WF4 iff (forward direction) lifts the chunk_read_result
      observation into a @{text Refresh} event in
      @{const clean_prefix_of}: at @{text "ch \<in> chunks R"} and
      @{text "k \<in> chunk_domain R ch"},
      @{text "chunk_read_result R ch k = Some m \<longleftrightarrow>
      Refresh k m (chunk_read_coordinate R ch) \<in>
      set (clean_prefix_of R)"}.

  Witnesses: @{text "m"} for the Refresh's value and
  @{text "chunk_read_coordinate R ch"} for its source coordinate.

  Note that this lemma does NOT unfold the
  @{const canonical_clean_prefix} construction directly. The WF4 iff
  is the wellformedness assertion that the clean prefix contains the
  expected @{text Refresh} events;
  clean_prefix_of_refresh_generated_by_responsible_chunk consumed
  its reverse direction (Refresh-in-clean-prefix \<Longrightarrow>
  chunk-identification) via the construction's
  @{const chunk_read_refreshes} branch, while this lemma consumes
  its forward direction (chunk-read-observation \<Longrightarrow>
  Refresh-in-clean-prefix) via the WF4 iff itself. This makes the
  refresh-generated / refresh-exists pair the two-directional
  source-side complement of the WF4 iff clause.

  The proof uses the @{text "wf_body = wf[unfolded
  wellformed_dblog_run_def]"} + @{text "(elim conjE)"} extraction
  pattern, because the WF body is bigger than @{text blast} can
  efficiently process when probing individual conjuncts.
\<close>

lemma clean_prefix_of_in_scope_responsible_chunk_refresh_exists:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and R :: "('k, 'v) run"
    and k :: 'k
  assumes wf: "wellformed_dblog_run b0 R H"
      and k_in_scope: "k \<in> scope_of R"
  shows "\<exists> m c. Refresh k m c \<in> set (clean_prefix_of R)"
proof -
  note wf_body = wf[unfolded wellformed_dblog_run_def]
  from wf_body have wf1a:
    "\<forall> k \<in> scope_of R. \<exists>! ch. ch \<in> chunks R \<and> owns R ch k"
    by (elim conjE)
  from wf_body have wf4:
    "\<forall> ch \<in> chunks R.
       src_le (chunk_lower_watermark R ch) (chunk_read_coordinate R ch)
     \<and> src_le (chunk_read_coordinate R ch) (chunk_upper_watermark R ch)
     \<and> (\<forall> k \<in> chunk_domain R ch.
          \<exists> m. chunk_read_result R ch k = Some m)
     \<and> (\<forall> k \<in> chunk_domain R ch. \<forall> m.
          chunk_read_result R ch k = Some m
            \<longleftrightarrow> Refresh k m (chunk_read_coordinate R ch)
                 \<in> set (clean_prefix_of R))"
    by (elim conjE)
  \<comment> \<open>WF1 (a) extracts the responsible chunk.\<close>
  from wf1a k_in_scope obtain ch where
    ch_in_chunks: "ch \<in> chunks R" and
    k_in_dom: "k \<in> chunk_domain R ch"
    by blast
  \<comment> \<open>WF4 totality on chunk_domain produces the observation.\<close>
  from wf4 ch_in_chunks k_in_dom obtain m where
    crr_res: "chunk_read_result R ch k = Some m"
    by blast
  \<comment> \<open>WF4 iff (forward) lifts the observation into clean_prefix_of.\<close>
  from wf4 ch_in_chunks k_in_dom crr_res
  have "Refresh k m (chunk_read_coordinate R ch)
          \<in> set (clean_prefix_of R)"
    by blast
  thus ?thesis by blast
qed

text \<open>
  The clean_prefix_of_cdc_generated_from_observed_cdc lemma (THIS
  lemma) is the Cdc-side complement of the
  clean_prefix_of_refresh_generated_by_responsible_chunk /
  clean_prefix_of_in_scope_responsible_chunk_refresh_exists pair:
  every @{text Cdc} event in @{const clean_prefix_of} is justified by
  an entry in @{const cdc_events_of} for an in-scope key at-or-
  before the frontier. Combined with WF2's reverse direction
  (observed-CDC faithfulness — every entry in @{const cdc_events_of}
  is itself an item of @{const src_history_of} on the in-scope/
  at-or-before-frontier slice), every @{text Cdc} in
  @{const clean_prefix_of} corresponds to a real source event.

  The proof case-splits on the @{const canonical_clean_prefix}
  construction's two branches. @{const chunk_read_refreshes}
  emits only @{text Refresh} events (its emission shape is
  @{text "Refresh k' m' (crr_read_coord r)"}), so a @{text Cdc}
  cannot live there; the disjunction established by unfolding
  @{const clean_prefix_of} + @{const canonical_clean_prefix}
  collapses to the @{const cdc_event_replays} branch. Then
  unfolding @{const cdc_event_replays} + @{const List.map_filter}
  + @{text "auto split: if_splits"} recovers the conjunction
  directly from the filter
  @{text "\<lambda> p. if key_of (snd p) \<in> scope \<and> fst p \<le> frontier
  then Some (Cdc (fst p) (snd p)) else None"}; the
  @{text less_eq_src_coord_def} linorder-instance unfolding
  bridges @{text "\<le>"} on @{type src_coord} to @{const src_le}.

  The @{const wellformed_dblog_run} premise is included for
  signature uniformity with the other supporting clean-prefix
  lemmas. NO WF clauses are consumed beyond the WF body's accessor
  identifications (@{const scope_of} / @{const frontier_of} /
  @{const cdc_events_of} are just run accessors; the property
  follows from the construction's filter form alone). This
  makes this lemma the most directly construction-derived of the
  supporting clean-prefix lemmas: its conclusion is exactly the
  filter's if-branch condition lifted back to the clean prefix.
\<close>

lemma clean_prefix_of_cdc_generated_from_observed_cdc:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and R :: "('k, 'v) run"
    and c :: src_coord
    and e :: "('k, 'v) source_event"
  assumes wf: "wellformed_dblog_run b0 R H"
      and e_in: "Cdc c e \<in> set (clean_prefix_of R)"
  shows "(c, e) \<in> set (cdc_events_of R)
       \<and> key_of e \<in> scope_of R
       \<and> src_le c (frontier_of R)"
proof -
  let ?mkRec = "\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                       crr_read_coord  = chunk_read_coordinate R ch,
                       crr_observation = chunk_read_result R ch \<rparr>"
  \<comment> \<open>Cdc events cannot come from the chunk_read_refreshes
      branch (which produces only Refresh events).\<close>
  have not_refresh_branch:
    "\<forall> ch. Cdc c e \<notin> set (chunk_read_refreshes (?mkRec ch))"
    unfolding chunk_read_refreshes_def List.map_filter_def
    by (auto split: option.splits)
  have split:
    "Cdc c e \<in> set (cdc_event_replays (scope_of R)
                                       (frontier_of R)
                                       (cdc_events_of R))
   \<or> (\<exists> ch \<in> set (chunks_list R).
        Cdc c e \<in> set (chunk_read_refreshes (?mkRec ch)))"
    using e_in
    by (auto simp: clean_prefix_of_def canonical_clean_prefix_def)
  from split not_refresh_branch have in_cdc_replays:
    "Cdc c e \<in> set (cdc_event_replays (scope_of R)
                                       (frontier_of R)
                                       (cdc_events_of R))"
    by blast
  \<comment> \<open>The cdc_event_replays filter directly yields the three
      conjuncts: (c, e) ∈ cdc_events_of R + key_of e ∈
      scope_of R + c \<le> frontier_of R (bridged to src_le via
      less_eq_src_coord_def).\<close>
  from in_cdc_replays show ?thesis
    unfolding cdc_event_replays_def List.map_filter_def
    by (auto split: if_splits simp: less_eq_src_coord_def)
qed

text \<open>
  Auxiliary list lemmas used by clean_prefix_of_cdc_order_respects_source_position:
  \<^const>\<open>filter\<close> preserves the
  strict order of @{text P}-satisfying positions in the underlying list.
  These are generic facts about @{const filter}, @{const take}, and
  @{const nth} on Isabelle lists; they package the standard
  ``position-of-the-$n$-th-survivor'' argument in a form that lemma can
  consume without explicit @{const nths} bookkeeping.

  Three pieces:

    \<^item> @{text filter_take_nth}: for any position @{text i} satisfying
      @{text P}, the @{text "length (filter P (take i xs))"}-th element
      of @{text "filter P xs"} is exactly @{text "xs ! i"}; furthermore
      that index lies strictly below @{text "length (filter P xs)"}.
      This gives the FORWARD direction of the position correspondence
      (positions in @{text xs} \<rightarrow> positions in @{text "filter P xs"}).

    \<^item> @{text length_filter_take_mono} / @{text length_filter_take_strict_mono}:
      @{text "length \<circ> filter P \<circ> take \<cdot>"} is monotone
      (resp.\ strictly monotone at any @{text P}-satisfying position)
      in the take-prefix length. The strict version drives the
      @{text "n_i < n_j"} step in
      clean_prefix_of_cdc_order_respects_source_position below.

    \<^item> @{text filter_index_strict_mono}: for any @{text "n < length (filter P xs)"},
      there exists a position @{text "p < length xs"} with
      @{text "xs ! p = filter P xs ! n"} and
      @{text "length (filter P (take p xs)) = n"}. This gives the
      BACKWARD direction (positions in @{text "filter P xs"} \<rightarrow> positions
      in @{text xs}). The @{text "length (filter P (take p xs)) = n"}
      witness is what lets us recover the original ordering from a
      pair of @{text n}'s via the @{text length_filter_take_mono} contrapositive.
\<close>

lemma filter_take_nth:
  fixes xs :: "'a list" and P :: "'a \<Rightarrow> bool" and i :: nat
  assumes i_lt:  "i < length xs"
      and Pi:    "P (xs ! i)"
  shows "filter P xs ! length (filter P (take i xs)) = xs ! i
       \<and> length (filter P (take i xs)) < length (filter P xs)"
proof -
  have xs_split: "xs = take i xs @ xs ! i # drop (Suc i) xs"
    using i_lt by (simp add: id_take_nth_drop)
  have filter_split:
    "filter P xs = filter P (take i xs) @ xs ! i # filter P (drop (Suc i) xs)"
  proof -
    have "filter P xs = filter P (take i xs @ xs ! i # drop (Suc i) xs)"
      using xs_split by simp
    also have "\<dots> = filter P (take i xs) @ filter P (xs ! i # drop (Suc i) xs)"
      by simp
    also have "filter P (xs ! i # drop (Suc i) xs) = xs ! i # filter P (drop (Suc i) xs)"
      using Pi by simp
    finally show ?thesis by simp
  qed
  have nth_eq:
    "filter P xs ! length (filter P (take i xs)) = xs ! i"
    using filter_split by (simp add: nth_append)
  have len_lt:
    "length (filter P (take i xs)) < length (filter P xs)"
    using filter_split by simp
  show ?thesis using nth_eq len_lt by simp
qed

lemma length_filter_take_mono:
  fixes xs :: "'a list" and P :: "'a \<Rightarrow> bool" and i j :: nat
  assumes "i \<le> j"
  shows "length (filter P (take i xs)) \<le> length (filter P (take j xs))"
proof -
  have take_i_eq: "take i (take j xs) = take i xs"
    using assms by (simp add: min_def take_take)
  have "take i xs @ drop i (take j xs) = take j xs"
    using take_i_eq append_take_drop_id by metis
  hence "filter P (take j xs)
       = filter P (take i xs) @ filter P (drop i (take j xs))"
    by (metis filter_append)
  thus ?thesis by simp
qed

lemma length_filter_take_strict_mono:
  fixes xs :: "'a list" and P :: "'a \<Rightarrow> bool" and i j :: nat
  assumes ij:       "i < j"
      and j_bound:  "j \<le> length xs"
      and Pi:       "P (xs ! i)"
  shows "length (filter P (take i xs)) < length (filter P (take j xs))"
proof -
  have i_bound: "i < length xs" using ij j_bound by linarith
  have suc_i_le_j: "Suc i \<le> j" using ij by simp
  have take_suc_i_eq: "take (Suc i) (take j xs) = take (Suc i) xs"
    using suc_i_le_j by (simp add: min_def take_take)
  have suc_split: "take (Suc i) xs @ drop (Suc i) (take j xs) = take j xs"
    using take_suc_i_eq append_take_drop_id by metis
  have take_suc_i: "take (Suc i) xs = take i xs @ [xs ! i]"
    using i_bound by (simp add: take_Suc_conv_app_nth)
  have decompose:
    "take j xs = take i xs @ [xs ! i] @ drop (Suc i) (take j xs)"
    using suc_split take_suc_i by simp
  have "filter P (take j xs)
      = filter P (take i xs @ [xs ! i] @ drop (Suc i) (take j xs))"
    using decompose by simp
  also have "\<dots> = filter P (take i xs) @ filter P [xs ! i] @ filter P (drop (Suc i) (take j xs))"
    by simp
  also have "filter P [xs ! i] = [xs ! i]" using Pi by simp
  finally have "filter P (take j xs)
              = filter P (take i xs) @ [xs ! i] @ filter P (drop (Suc i) (take j xs))"
    by simp
  thus ?thesis by simp
qed

lemma filter_index_strict_mono:
  fixes xs :: "'a list" and P :: "'a \<Rightarrow> bool" and n :: nat
  assumes "n < length (filter P xs)"
  shows "\<exists> p. p < length xs
           \<and> P (xs ! p)
           \<and> xs ! p = filter P xs ! n
           \<and> length (filter P (take p xs)) = n"
  using assms
proof (induction xs arbitrary: n)
  case Nil
  thus ?case by simp
next
  case (Cons a xs')
  show ?case
  proof (cases "P a")
    case Pa: True
    show ?thesis
    proof (cases n)
      case 0
      have at0: "filter P (a # xs') ! n = a" using Pa 0 by simp
      have "(0 :: nat) < length (a # xs')" by simp
      moreover have "P ((a # xs') ! 0)" using Pa by simp
      moreover have "(a # xs') ! 0 = filter P (a # xs') ! n" using at0 by simp
      moreover have "length (filter P (take 0 (a # xs'))) = n" using 0 by simp
      ultimately show ?thesis by (intro exI[where x = 0]) auto
    next
      case (Suc n')
      have filter_nth_eq:
        "filter P (a # xs') ! n = filter P xs' ! n'"
        using Pa Suc by simp
      have n'_lt: "n' < length (filter P xs')"
        using Cons.prems Pa Suc by simp
      obtain p' where p'_props:
          "p' < length xs'" "P (xs' ! p')"
          "xs' ! p' = filter P xs' ! n'"
          "length (filter P (take p' xs')) = n'"
        using Cons.IH[OF n'_lt] by blast
      have "Suc p' < length (a # xs')" using p'_props by simp
      moreover have "P ((a # xs') ! Suc p')" using p'_props by simp
      moreover have "(a # xs') ! Suc p' = filter P (a # xs') ! n"
        using filter_nth_eq p'_props by simp
      moreover have "length (filter P (take (Suc p') (a # xs'))) = n"
        using Pa Suc p'_props by simp
      ultimately show ?thesis by (intro exI[where x = "Suc p'"]) auto
    qed
  next
    case nPa: False
    have filter_a_eq: "filter P (a # xs') = filter P xs'" using nPa by simp
    have "n < length (filter P xs')"
      using Cons.prems filter_a_eq by simp
    obtain p' where p'_props:
        "p' < length xs'" "P (xs' ! p')"
        "xs' ! p' = filter P xs' ! n"
        "length (filter P (take p' xs')) = n"
      using Cons.IH \<open>n < length (filter P xs')\<close> by blast
    have "Suc p' < length (a # xs')" using p'_props by simp
    moreover have "P ((a # xs') ! Suc p')" using p'_props by simp
    moreover have "(a # xs') ! Suc p' = filter P (a # xs') ! n"
      using filter_a_eq p'_props by simp
    moreover have "length (filter P (take (Suc p') (a # xs'))) = n"
      using nPa p'_props by simp
    ultimately show ?thesis by (intro exI[where x = "Suc p'"]) auto
  qed
qed

lemma subseq_mset_eq_imp_eq:
  fixes xs ys :: "'a list"
  assumes sub: "subseq xs ys"
      and ms:  "mset xs = mset ys"
  shows "xs = ys"
  by (rule subseq_same_length[OF sub mset_eq_length[OF ms]])

lemma subseq_from_strict_mono_nth:
  fixes xs ys :: "'a list"
    and f :: "nat \<Rightarrow> nat"
  assumes mono: "strict_mono f"
      and hit: "\<And>i. i < length xs \<Longrightarrow> f i < length ys \<and> xs ! i = ys ! f i"
  shows "subseq xs ys"
  using assms
proof (induction xs arbitrary: ys f)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  from Cons.prems(2)[of 0] have f0_lt: "f 0 < length ys"
    and x_eq: "x = ys ! f 0"
    by simp_all
  let ?tail = "drop (Suc (f 0)) ys"
  let ?g = "\<lambda>i. f (Suc i) - Suc (f 0)"

  have g_mono: "strict_mono ?g"
  proof (rule strict_monoI)
    fix i j :: nat
    assume ij: "i < j"
    have f0_lt_i: "f 0 < f (Suc i)"
      using strict_monoD[OF Cons.prems(1), of 0 "Suc i"] by simp
    have "f (Suc i) < f (Suc j)"
      using strict_monoD[OF Cons.prems(1), of "Suc i" "Suc j"] ij by simp
    with f0_lt_i show "?g i < ?g j" by simp
  qed

  have g_hit:
    "\<And>i. i < length xs \<Longrightarrow>
       ?g i < length ?tail \<and> xs ! i = ?tail ! ?g i"
  proof -
    fix i
    assume i_lt: "i < length xs"
    from Cons.prems(2)[of "Suc i"] i_lt
    have fSi_lt: "f (Suc i) < length ys"
      and xs_i: "xs ! i = ys ! f (Suc i)"
      by simp_all
    have f0_lt_fSi: "f 0 < f (Suc i)"
      using strict_monoD[OF Cons.prems(1), of 0 "Suc i"] by simp
    hence fSi_eq: "Suc (f 0) + ?g i = f (Suc i)"
      by simp
    have g_lt: "?g i < length ?tail"
      using fSi_lt fSi_eq by simp
    have tail_nth: "?tail ! ?g i = ys ! f (Suc i)"
      using g_lt fSi_eq by simp
    show "?g i < length ?tail \<and> xs ! i = ?tail ! ?g i"
      using g_lt xs_i tail_nth by simp
  qed

  have tail_sub: "subseq xs ?tail"
    by (rule Cons.IH[OF g_mono g_hit])
  have cons_sub: "subseq (x # xs) (ys ! f 0 # ?tail)"
    using tail_sub x_eq by simp
  have ys_split: "ys = take (f 0) ys @ ys ! f 0 # ?tail"
    using f0_lt by (simp add: id_take_nth_drop)
  have prefixed: "subseq (x # xs) (take (f 0) ys @ (ys ! f 0 # ?tail))"
    by (rule subseq_drop_many[OF cons_sub])
  show ?case
    by (subst ys_split, rule prefixed)
qed

lemma last_filter_index:
  fixes xs :: "'a list"
  assumes nonempty: "filter P xs \<noteq> []"
  shows "\<exists>i. i < length xs
          \<and> P (xs ! i)
          \<and> xs ! i = last (filter P xs)
          \<and> (\<forall>j. i < j \<and> j < length xs \<longrightarrow> \<not> P (xs ! j))"
  using nonempty
proof (induction xs rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc x xs)
  show ?case
  proof (cases "P x")
    case True
    have idx_lt: "length xs < length (xs @ [x])" by simp
    have P_idx: "P ((xs @ [x]) ! length xs)" using True by simp
    have last_idx: "(xs @ [x]) ! length xs = last (filter P (xs @ [x]))"
      using True by simp
    have no_later:
      "\<forall>j. length xs < j \<and> j < length (xs @ [x])
            \<longrightarrow> \<not> P ((xs @ [x]) ! j)"
      by auto
    show ?thesis
      using idx_lt P_idx last_idx no_later
      by (intro exI[where x = "length xs"]) simp
  next
    case False
    note nPx = False
    have filter_xs_nonempty: "filter P xs \<noteq> []"
      using snoc.prems nPx by simp
    obtain i where i_lt_xs: "i < length xs"
      and Pi_xs: "P (xs ! i)"
      and last_xs: "xs ! i = last (filter P xs)"
      and no_later_xs: "\<forall>j. i < j \<and> j < length xs \<longrightarrow> \<not> P (xs ! j)"
      using snoc.IH[OF filter_xs_nonempty] by blast
    have i_lt: "i < length (xs @ [x])" using i_lt_xs by simp
    have Pi: "P ((xs @ [x]) ! i)" using Pi_xs i_lt_xs by (simp add: nth_append)
    have filter_append_eq: "filter P (xs @ [x]) = filter P xs"
      using nPx by simp
    have last_eq: "(xs @ [x]) ! i = last (filter P (xs @ [x]))"
    proof -
      have "(xs @ [x]) ! i = xs ! i"
        using i_lt_xs by (simp add: nth_append)
      also have "\<dots> = last (filter P xs)"
        using last_xs .
      also have "\<dots> = last (filter P (xs @ [x]))"
        using filter_append_eq by simp
      finally show ?thesis .
    qed
    have no_later:
      "\<forall>j. i < j \<and> j < length (xs @ [x]) \<longrightarrow> \<not> P ((xs @ [x]) ! j)"
    proof (intro allI impI)
      fix j
      assume j_assm: "i < j \<and> j < length (xs @ [x])"
      show "\<not> P ((xs @ [x]) ! j)"
      proof (cases "j < length xs")
        case True
        thus ?thesis using no_later_xs j_assm by (simp add: nth_append)
      next
        case False
        hence "j = length xs" using j_assm by simp
        thus ?thesis using nPx by simp
      qed
    qed
    show ?thesis
      using i_lt Pi last_eq no_later by blast
  qed
qed

lemma last_filter_upt_eq:
  fixes P :: "nat \<Rightarrow> bool"
  assumes i_lt: "i < n"
      and Pi: "P i"
      and no_after: "\<forall>j. i < j \<and> j < n \<longrightarrow> \<not> P j"
  shows "filter P [0..<n] \<noteq> [] \<and> last (filter P [0..<n]) = i"
  using i_lt Pi no_after
proof (induction n arbitrary: i)
  case 0
  thus ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "i = n")
    case True
    have upt: "[0..<Suc n] = [0..<n] @ [n]"
      by (simp add: upt_Suc_append)
    have "filter P [0..<Suc n] = filter P [0..<n] @ [n]"
      using True Suc.prems(2) upt by simp
    thus ?thesis using True by simp
  next
    case False
    hence i_lt_n: "i < n" using Suc.prems(1) by simp
    have Pn_false: "\<not> P n"
      using Suc.prems False by simp
    have no_after_n: "\<forall>j. i < j \<and> j < n \<longrightarrow> \<not> P j"
      using Suc.prems(3) by auto
    have ih: "filter P [0..<n] \<noteq> [] \<and> last (filter P [0..<n]) = i"
      by (rule Suc.IH[OF i_lt_n Suc.prems(2) no_after_n])
    have upt: "[0..<Suc n] = [0..<n] @ [n]"
      by (simp add: upt_Suc_append)
    have "filter P [0..<Suc n] = filter P [0..<n]"
      using Pn_false upt by simp
    thus ?thesis using ih by simp
  qed
qed

lemma append_no_B_before_A:
  fixes xs ys zs :: "'a list"
    and A B :: "'a \<Rightarrow> bool"
    and i j :: nat
  assumes zs_eq: "zs = xs @ ys"
      and xs_A: "\<forall>x \<in> set xs. A x"
      and ys_B: "\<forall>y \<in> set ys. B y"
      and disj: "\<And>z. A z \<Longrightarrow> B z \<Longrightarrow> False"
      and ij: "i < j"
      and j_lt: "j < length zs"
      and zi_B: "B (zs ! i)"
      and zj_A: "A (zs ! j)"
  shows False
proof (cases "i < length xs")
  case True
  hence "A (zs ! i)"
    using zs_eq xs_A by (simp add: nth_append)
  thus False using zi_B disj by blast
next
  case False
  hence j_ge: "length xs \<le> j" using ij by simp
  have "j - length xs < length ys"
    using zs_eq j_lt j_ge by simp
  hence "B (zs ! j)"
    using zs_eq ys_B j_ge by (simp add: nth_append)
  thus False using zj_A disj by blast
qed

lemma wellformed_src_history_coord_mono:
  fixes H :: "('k, 'v) src_history"
  assumes wf_h: "wellformed_src_history H"
      and ij: "i \<le> j"
      and j_lt: "j < length H"
  shows "src_le (hist_coord (H ! i)) (hist_coord (H ! j))"
proof -
  from wf_h have adj:
    "\<forall>i. Suc i < length H
          \<longrightarrow> src_le (hist_coord (H ! i)) (hist_coord (H ! Suc i))"
    unfolding wellformed_src_history_def by blast
  have step:
    "\<And>n. i + n < length H
      \<Longrightarrow> src_le (hist_coord (H ! i)) (hist_coord (H ! (i + n)))"
  proof -
    fix n
    assume bound: "i + n < length H"
    show "src_le (hist_coord (H ! i)) (hist_coord (H ! (i + n)))"
      using bound
    proof (induction n)
      case 0
      show ?case by (simp add: src_le_refl)
    next
      case (Suc n)
      have ih_bound: "i + n < length H" using Suc.prems by simp
      have ih:
        "src_le (hist_coord (H ! i)) (hist_coord (H ! (i + n)))"
        using Suc.IH[OF ih_bound] .
      have adj_step:
        "src_le (hist_coord (H ! (i + n))) (hist_coord (H ! Suc (i + n)))"
        using adj Suc.prems by simp
      have "src_le (hist_coord (H ! i)) (hist_coord (H ! Suc (i + n)))"
        using src_le_trans[OF ih adj_step] .
      thus ?case by (simp add: add_Suc_right)
    qed
  qed
  have j_eq: "j = i + (j - i)" using ij by simp
  show ?thesis
    using step[of "j - i"] j_lt j_eq by simp
qed

text \<open>
  The clean_prefix_of_cdc_order_respects_source_position lemma (THIS
  lemma) is the same-coordinate ordering invariant for @{text Cdc}
  events in the run-produced clean prefix: at any common source
  coordinate @{text c}, the relative order of @{text "Cdc c _"}
  events in @{const clean_prefix_of} matches their relative order in
  @{const cdc_events_of}. Its conclusion is in @{const cdc_events_of}
  position order; downstream consumers
  (clean_prefix_of_latest_replay_correspondence,
  clean_prefix_of_per_key_replay_equals_source, Lemma 1.1, the
  Layer 2 main theorem proof) lift that to source-position order
  @{text "\<preceq>_H"} on @{const src_history_of} via the WF2
  order-preservation conjunct's @{const strict_mono} embedding.
  This lemma itself does not consume any WF body clause; the
  @{const wellformed_dblog_run} premise is included for signature
  uniformity with the other supporting clean-prefix lemmas.

  The proof composes four definitional ingredients without any WF body
  extraction:

  \<^item> Step (a): definitional rewrite. @{thm clean_prefix_of_def}
    instantiates @{const clean_prefix_of} as
    @{const canonical_clean_prefix} for the run's named accessors;
    @{thm canonical_clean_prefix_def} expands the latter to
    @{text "sort_key cdc_coord (cdc_part @ refresh_part)"} where
    @{text cdc_part} ranges over @{const cdc_events_of} survivors and
    @{text refresh_part} concatenates the per-chunk
    @{const chunk_read_refreshes} lists.

  \<^item> Step (b): @{const List.map_filter}-as-@{const map}-of-@{const filter}
    unfold. @{const cdc_event_replays} is by definition a
    @{const List.map_filter}; the standard equivalence
    @{thm map_filter_map_filter} gives
    @{text "cdc_part = map (\<lambda>p. Cdc (fst p) (snd p)) (filter in_filter (cdc_events_of R))"},
    which is order-preserving in the @{const cdc_events_of} input.

  \<^item> Step (c): refresh-side exclusion. @{const chunk_read_refreshes}
    emits only @{text Refresh}-shaped events
    (@{text "Refresh k m (crr_read_coord r)"}); filtering for
    @{text Cdc}-at-coord-@{text c} on @{text refresh_part} yields
    @{term "[]"}.

  \<^item> Step (d): @{thm sort_key_stable}. The standard Isabelle stability
    lemma: at any key value @{text k}, the filter on
    @{text "cdc_coord = k"} commutes with @{const sort_key}; i.e.,
    @{text "filter (\<lambda>y. cdc_coord y = k) (sort_key cdc_coord xs)
                  = filter (\<lambda>y. cdc_coord y = k) xs"}.

  Composition: filtering @{const clean_prefix_of} to the
  @{text "Cdc c _"} subsequence collapses (by (c)+(d)+chained filtering)
  to filtering @{text cdc_part} to that same shape, which (by (b)) is a
  map over a sub-filter of @{const cdc_events_of} preserving the input
  order. The forward direction of position correspondence
  (@{text filter_take_nth} + @{text length_filter_take_strict_mono})
  lifts the @{text "i < j"} order from @{const clean_prefix_of} to the
  filter; the backward direction (@{text filter_index_strict_mono} +
  @{text length_filter_take_mono} contrapositive) lifts the filter
  positions back to @{const cdc_events_of} positions @{text "p < q"}
  with the required values.
\<close>

lemma clean_prefix_of_cdc_order_respects_source_position:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "('k, 'v) run"
    and c  :: src_coord
    and e1 e2 :: "('k, 'v) source_event"
    and i j :: nat
  assumes wf:       "wellformed_dblog_run b0 R H"
      and ij:       "i < j"
      and j_bound:  "j < length (clean_prefix_of R)"
      and at_i:     "clean_prefix_of R ! i = Cdc c e1"
      and at_j:     "clean_prefix_of R ! j = Cdc c e2"
  shows "\<exists> p q. p < q
              \<and> q < length (cdc_events_of R)
              \<and> cdc_events_of R ! p = (c, e1)
              \<and> cdc_events_of R ! q = (c, e2)"
proof -
  let ?mkRec = "\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                       crr_read_coord  = chunk_read_coordinate R ch,
                       crr_observation = chunk_read_result R ch \<rparr>"
  let ?cdc_part     = "cdc_event_replays (scope_of R) (frontier_of R) (cdc_events_of R)"
  let ?refresh_part = "concat (map chunk_read_refreshes (map ?mkRec (chunks_list R)))"
  let ?inp          = "?cdc_part @ ?refresh_part"
  let ?Pc = "\<lambda>x::('k, 'v) replay_event. \<exists> e. x = Cdc c e"
  let ?Qc = "\<lambda>x::('k, 'v) replay_event. cdc_coord x = c"
  let ?Qpair = "\<lambda>p::(src_coord \<times> ('k, 'v) source_event).
                  fst p = c
                  \<and> key_of (snd p) \<in> scope_of R
                  \<and> fst p \<le> frontier_of R"
  let ?in_filter = "\<lambda>p::(src_coord \<times> ('k, 'v) source_event).
                      key_of (snd p) \<in> scope_of R
                      \<and> fst p \<le> frontier_of R"
  define S where "S = filter ?Qpair (cdc_events_of R)"

  have i_lt_cp: "i < length (clean_prefix_of R)" using ij j_bound by simp
  have Pi: "?Pc (clean_prefix_of R ! i)" using at_i by auto
  have Pj: "?Pc (clean_prefix_of R ! j)" using at_j by auto

  \<comment> \<open>Step (a): @{const clean_prefix_of} as the sort_key over cdc_part @ refresh_part.\<close>
  have cp_eq: "clean_prefix_of R = sort_key cdc_coord ?inp"
    unfolding clean_prefix_of_def canonical_clean_prefix_def by simp

  \<comment> \<open>Step (b): cdc_part as map over a filter of cdc_events_of R.\<close>
  have cdc_part_eq:
    "?cdc_part = map (\<lambda>p. Cdc (fst p) (snd p)) (filter ?in_filter (cdc_events_of R))"
    unfolding cdc_event_replays_def
    by (simp add: map_filter_map_filter[symmetric])

  \<comment> \<open>Step (c): refresh_part contributes no Cdc events.\<close>
  have refresh_no_Cdc:
    "\<And> ch x. x \<in> set (chunk_read_refreshes (?mkRec ch)) \<Longrightarrow> \<not> ?Pc x"
    by (auto simp: chunk_read_refreshes_def List.map_filter_def split: option.splits)
  have refresh_filter_empty: "filter ?Pc ?refresh_part = []"
  proof -
    have "\<forall> x \<in> set ?refresh_part. \<not> ?Pc x"
      using refresh_no_Cdc by auto
    thus ?thesis by (simp add: filter_empty_conv)
  qed

  \<comment> \<open>Step (d): @{thm sort_key_stable} at coordinate c.\<close>
  have stab_Qc:
    "filter ?Qc (clean_prefix_of R) = filter ?Qc ?inp"
    using cp_eq sort_key_stable[of cdc_coord c ?inp] by simp

  \<comment> \<open>Chained filtering: ?Pc x implies ?Qc x, so filtering by ?Pc
      commutes with first filtering by ?Qc.\<close>
  have Pc_chain:
    "filter ?Pc xs = filter ?Pc (filter ?Qc xs)"
    for xs :: "('k, 'v) replay_event list"
    by (induction xs) auto

  \<comment> \<open>Composition: filter ?Pc collapses to the cdc_part contribution.\<close>
  have filter_Pc_cp:
    "filter ?Pc (clean_prefix_of R) = filter ?Pc ?cdc_part"
  proof -
    have "filter ?Pc (clean_prefix_of R) = filter ?Pc (filter ?Qc (clean_prefix_of R))"
      using Pc_chain by simp
    also have "\<dots> = filter ?Pc (filter ?Qc ?inp)"
      using stab_Qc by simp
    also have "\<dots> = filter ?Pc ?inp"
      using Pc_chain by simp
    also have "filter ?Pc ?inp
             = filter ?Pc ?cdc_part @ filter ?Pc ?refresh_part"
      by simp
    also have "\<dots> = filter ?Pc ?cdc_part"
      using refresh_filter_empty by simp
    finally show ?thesis .
  qed

  \<comment> \<open>filter ?Pc cdc_part as a map over S.\<close>
  have filter_Pc_cdc_part:
    "filter ?Pc ?cdc_part = map (\<lambda>p. Cdc c (snd p)) S"
  proof -
    have "filter ?Pc ?cdc_part
        = filter ?Pc (map (\<lambda>p. Cdc (fst p) (snd p))
                          (filter ?in_filter (cdc_events_of R)))"
      using cdc_part_eq by simp
    also have "\<dots> = map (\<lambda>p. Cdc (fst p) (snd p))
                         (filter (\<lambda>p. ?Pc (Cdc (fst p) (snd p)))
                                 (filter ?in_filter (cdc_events_of R)))"
      by (simp add: filter_map o_def)
    also have pred_simp:
      "(\<lambda>p::(src_coord \<times> ('k, 'v) source_event). ?Pc (Cdc (fst p) (snd p)))
         = (\<lambda>p. fst p = c)"
      by (auto intro: ext)
    also have "filter (\<lambda>p::(src_coord \<times> ('k, 'v) source_event). fst p = c)
                       (filter ?in_filter (cdc_events_of R))
             = filter ?Qpair (cdc_events_of R)"
      by (simp add: filter_filter conj_commute)
    also have "filter ?Qpair (cdc_events_of R) = S"
      unfolding S_def by simp
    finally have step:
      "filter ?Pc ?cdc_part = map (\<lambda>p. Cdc (fst p) (snd p)) S" by simp
    have rewrite_map:
      "map (\<lambda>p. Cdc (fst p) (snd p)) S = map (\<lambda>p. Cdc c (snd p)) S"
      by (rule map_cong[OF refl]) (auto simp: S_def)
    show ?thesis using step rewrite_map by simp
  qed

  have filter_Pc_eq_map:
    "filter ?Pc (clean_prefix_of R) = map (\<lambda>p. Cdc c (snd p)) S"
    using filter_Pc_cp filter_Pc_cdc_part by simp

  \<comment> \<open>Forward step: positions i, j in clean_prefix_of R lift to positions
      n_i < n_j in filter ?Pc (clean_prefix_of R) via filter_take_nth +
      length_filter_take_strict_mono.\<close>
  define n_i where "n_i = length (filter ?Pc (take i (clean_prefix_of R)))"
  define n_j where "n_j = length (filter ?Pc (take j (clean_prefix_of R)))"

  have nth_i_val_lt:
    "filter ?Pc (clean_prefix_of R) ! n_i = clean_prefix_of R ! i
   \<and> n_i < length (filter ?Pc (clean_prefix_of R))"
    using filter_take_nth[where xs = "clean_prefix_of R"
                            and P = "\<lambda>x::('k,'v) replay_event. \<exists>e. x = Cdc c e"
                            and i = i, OF i_lt_cp Pi]
    unfolding n_i_def by simp
  have nth_j_val_lt:
    "filter ?Pc (clean_prefix_of R) ! n_j = clean_prefix_of R ! j
   \<and> n_j < length (filter ?Pc (clean_prefix_of R))"
    using filter_take_nth[where xs = "clean_prefix_of R"
                            and P = "\<lambda>x::('k,'v) replay_event. \<exists>e. x = Cdc c e"
                            and i = j, OF j_bound Pj]
    unfolding n_j_def by simp
  have ni_lt_nj: "n_i < n_j"
    using length_filter_take_strict_mono[where xs = "clean_prefix_of R"
                                           and P = "\<lambda>x::('k,'v) replay_event. \<exists>e. x = Cdc c e"
                                           and i = i and j = j,
                                         OF ij _ Pi] j_bound
    unfolding n_i_def n_j_def by simp

  \<comment> \<open>S-positions at n_i, n_j carry (c, e1), (c, e2).\<close>
  have len_eq: "length (filter ?Pc (clean_prefix_of R)) = length S"
    using filter_Pc_eq_map by (simp add: length_map)
  have ni_lt_S: "n_i < length S" using nth_i_val_lt len_eq by simp
  have nj_lt_S: "n_j < length S" using nth_j_val_lt len_eq by simp
  have S_at_ni: "S ! n_i = (c, e1)"
  proof -
    have "(map (\<lambda>p. Cdc c (snd p)) S) ! n_i = Cdc c (snd (S ! n_i))"
      using ni_lt_S by simp
    moreover have "(map (\<lambda>p. Cdc c (snd p)) S) ! n_i = Cdc c e1"
      using filter_Pc_eq_map nth_i_val_lt at_i by simp
    ultimately have "Cdc c (snd (S ! n_i)) = Cdc c e1" by simp
    hence snd_eq: "snd (S ! n_i) = e1" by simp
    have "S ! n_i \<in> set S" using ni_lt_S nth_mem by blast
    hence fst_eq: "fst (S ! n_i) = c"
      using S_def by auto
    show "S ! n_i = (c, e1)" using snd_eq fst_eq by (cases "S ! n_i") simp
  qed
  have S_at_nj: "S ! n_j = (c, e2)"
  proof -
    have "(map (\<lambda>p. Cdc c (snd p)) S) ! n_j = Cdc c (snd (S ! n_j))"
      using nj_lt_S by simp
    moreover have "(map (\<lambda>p. Cdc c (snd p)) S) ! n_j = Cdc c e2"
      using filter_Pc_eq_map nth_j_val_lt at_j by simp
    ultimately have "Cdc c (snd (S ! n_j)) = Cdc c e2" by simp
    hence snd_eq: "snd (S ! n_j) = e2" by simp
    have "S ! n_j \<in> set S" using nj_lt_S nth_mem by blast
    hence fst_eq: "fst (S ! n_j) = c"
      using S_def by auto
    show "S ! n_j = (c, e2)" using snd_eq fst_eq by (cases "S ! n_j") simp
  qed

  \<comment> \<open>Backward step: positions n_i, n_j in S lift to positions p, q in
      cdc_events_of R via filter_index_strict_mono +
      length_filter_take_mono contrapositive.\<close>
  have ni_lt_S_filter: "n_i < length (filter ?Qpair (cdc_events_of R))"
    using ni_lt_S S_def by simp
  have nj_lt_S_filter: "n_j < length (filter ?Qpair (cdc_events_of R))"
    using nj_lt_S S_def by simp
  obtain p where p_props:
      "p < length (cdc_events_of R)"
      "?Qpair (cdc_events_of R ! p)"
      "cdc_events_of R ! p = filter ?Qpair (cdc_events_of R) ! n_i"
      "length (filter ?Qpair (take p (cdc_events_of R))) = n_i"
    using filter_index_strict_mono[OF ni_lt_S_filter] by blast
  obtain q where q_props:
      "q < length (cdc_events_of R)"
      "?Qpair (cdc_events_of R ! q)"
      "cdc_events_of R ! q = filter ?Qpair (cdc_events_of R) ! n_j"
      "length (filter ?Qpair (take q (cdc_events_of R))) = n_j"
    using filter_index_strict_mono[OF nj_lt_S_filter] by blast

  have p_val: "cdc_events_of R ! p = (c, e1)"
    using p_props S_at_ni S_def by simp
  have q_val: "cdc_events_of R ! q = (c, e2)"
    using q_props S_at_nj S_def by simp

  \<comment> \<open>p < q follows from monotonicity of length \<circ> filter ?Qpair \<circ> take \<cdot>
      composed with the contrapositive of n_i < n_j.\<close>
  have p_lt_q: "p < q"
  proof (rule ccontr)
    assume "\<not> p < q"
    hence q_le_p: "q \<le> p" by simp
    have "length (filter ?Qpair (take q (cdc_events_of R)))
        \<le> length (filter ?Qpair (take p (cdc_events_of R)))"
      using length_filter_take_mono[where xs = "cdc_events_of R"
                                      and P = ?Qpair
                                      and i = q and j = p,
                                    OF q_le_p]
      by simp
    hence "n_j \<le> n_i" using p_props q_props by simp
    thus False using ni_lt_nj by simp
  qed

  show ?thesis
  proof (intro exI conjI)
    show "p < q" by (rule p_lt_q)
    show "q < length (cdc_events_of R)" using q_props by simp
    show "cdc_events_of R ! p = (c, e1)" by (rule p_val)
    show "cdc_events_of R ! q = (c, e2)" by (rule q_val)
  qed
qed

text \<open>
  The clean_prefix_of_latest_replay_correspondence lemma
  (THIS lemma) is the structural correspondence form: for any
  in-scope key @{text "k \<in> scope_of(R)"}, the per-key latest replay
  event in @{const clean_prefix_of} is EITHER (a) a @{text "Cdc c e"}
  event with @{text "key_of e = k"} whose source pair
  @{text "(c, e)"} lives in @{const cdc_events_of} at-or-before
  the frontier, OR (b) a @{text "Refresh k m c_read"} event whose
  value @{text m} is the @{const chunk_read_result} of the
  responsible chunk for @{text k} at its
  @{const chunk_read_coordinate}.

  This lemma is the structural input to the per-key value equality
  of clean_prefix_of_per_key_replay_equals_source. Splitting the
  correspondence into a structural form and a value-equality form
  separates:

    \<^item> clean_prefix_of_latest_replay_correspondence (this lemma):
      which @{const clean_prefix_of} event
      corresponds to which source-side entity (a structural
      correspondence claim depending on @{const cdc_events_of} /
      @{const chunk_read_result} membership, not on
      value-equality semantics);

    \<^item> clean_prefix_of_per_key_replay_equals_source:
      @{text "Apply (clean_prefix_of R) (k) =
      Src b0 H (frontier_of R) k"} (the per-key value equality,
      consuming this lemma + Lemmas 0.1 / 0.3 / 0.4 / 0.5).

  This lemma's proof composes four definitional ingredients:

    Step 1: existence of a latest @{text k}-event via
      clean_prefix_of_in_scope_responsible_chunk_refresh_exists.
      @{thm clean_prefix_of_in_scope_responsible_chunk_refresh_exists}
      gives @{text "\<exists>m c. Refresh k m c \<in> set (clean_prefix_of R)"}
      under the in-scope premise; an index @{text i} for this
      occurrence carries @{text "event_key (clean_prefix_of R ! i) = k"}.

    Step 2: take @{text "i_max = Max"} of the (finite, nonempty)
      set of @{text k}-event indices in @{const clean_prefix_of};
      @{const Max} membership + @{thm Max_ge} give that no later
      index carries @{text "event_key = k"}.

    Step 3: case-split on
      @{text "clean_prefix_of R ! i_max"}'s shape (Cdc vs Refresh).

      \<^item> Cdc case: the
        @{thm clean_prefix_of_cdc_generated_from_observed_cdc}
        lemma
        extracts the three correspondence conjuncts directly:
        @{text "(c, e) \<in> set (cdc_events_of R)"}
        + @{text "key_of e \<in> scope_of R"} + @{text "src_le c (frontier_of R)"}.

      \<^item> Refresh case: the
        @{thm clean_prefix_of_refresh_generated_by_responsible_chunk}
        lemma
        extracts the three correspondence conjuncts:
        @{text "responsible_chunk R k = Some ch"} +
        @{text "chunk_read_coordinate R ch = c_read"} +
        @{text "chunk_read_result R ch k = Some m"}.

  This lemma does NOT consume Lemmas 0.1 / 0.3 / 0.4 / 0.5 --- those
  Layer 0 basic lemmas drive the value equality of
  clean_prefix_of_per_key_replay_equals_source, not the
  structural correspondence here. Like
  clean_prefix_of_cdc_order_respects_source_position, this lemma
  concentrates only on the structural correspondence and pushes
  value semantics to clean_prefix_of_per_key_replay_equals_source.

  The remaining case --- "@{text k} has no
  event in @{const clean_prefix_of}" --- is ruled out for in-scope
  @{text k} by the refresh-existence of
  clean_prefix_of_in_scope_responsible_chunk_refresh_exists; the
  disjunction collapses to (a) Cdc OR (b) Refresh.
\<close>

lemma clean_prefix_of_latest_replay_correspondence:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "('k, 'v) run"
    and k  :: 'k
  assumes wf:          "wellformed_dblog_run b0 R H"
      and k_in_scope:  "k \<in> scope_of R"
  shows
    "(\<exists> i c e.
        i < length (clean_prefix_of R)
        \<and> clean_prefix_of R ! i = Cdc c e
        \<and> key_of e = k
        \<and> (\<forall> j. i < j \<and> j < length (clean_prefix_of R)
                  \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k)
        \<and> (c, e) \<in> set (cdc_events_of R)
        \<and> src_le c (frontier_of R))
   \<or>
    (\<exists> i ch m c_read.
        i < length (clean_prefix_of R)
        \<and> clean_prefix_of R ! i = Refresh k m c_read
        \<and> (\<forall> j. i < j \<and> j < length (clean_prefix_of R)
                  \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k)
        \<and> responsible_chunk R k = Some ch
        \<and> chunk_read_result R ch k = Some m
        \<and> chunk_read_coordinate R ch = c_read)"
proof -
  \<comment> \<open>Step 1: clean_prefix_of_in_scope_responsible_chunk_refresh_exists gives a
      Refresh event for k, yielding existence of an index.\<close>
  obtain m0 c0_read where refresh_exists:
    "Refresh k m0 c0_read \<in> set (clean_prefix_of R)"
    using clean_prefix_of_in_scope_responsible_chunk_refresh_exists[OF wf k_in_scope]
    by blast

  define event_indices where
    "event_indices =
       {i. i < length (clean_prefix_of R)
         \<and> event_key (clean_prefix_of R ! i) = k}"
  have event_indices_finite: "finite event_indices"
    unfolding event_indices_def by auto
  have event_indices_nonempty: "event_indices \<noteq> {}"
  proof -
    from refresh_exists obtain i where
      i_lt: "i < length (clean_prefix_of R)"
      and at_i: "clean_prefix_of R ! i = Refresh k m0 c0_read"
      by (auto simp: in_set_conv_nth)
    have "event_key (clean_prefix_of R ! i) = k"
      using at_i by simp
    hence "i \<in> event_indices"
      using i_lt unfolding event_indices_def by auto
    thus ?thesis by blast
  qed

  \<comment> \<open>Step 2: i_max = Max event_indices is the latest k-event position.\<close>
  define i_max where "i_max = Max event_indices"
  have i_max_in: "i_max \<in> event_indices"
    using event_indices_finite event_indices_nonempty
    unfolding i_max_def by (rule Max_in)
  have i_max_lt: "i_max < length (clean_prefix_of R)"
    using i_max_in unfolding event_indices_def by simp
  have i_max_event_key: "event_key (clean_prefix_of R ! i_max) = k"
    using i_max_in unfolding event_indices_def by simp
  have i_max_latest:
    "\<forall> j. i_max < j \<and> j < length (clean_prefix_of R)
              \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k"
  proof (intro allI impI)
    fix j
    assume j_assm: "i_max < j \<and> j < length (clean_prefix_of R)"
    hence j_props: "i_max < j" "j < length (clean_prefix_of R)" by auto
    show "event_key (clean_prefix_of R ! j) \<noteq> k"
    proof (rule ccontr)
      assume "\<not> event_key (clean_prefix_of R ! j) \<noteq> k"
      hence j_event_key: "event_key (clean_prefix_of R ! j) = k" by simp
      hence j_in: "j \<in> event_indices"
        unfolding event_indices_def using j_props by auto
      have "j \<le> i_max"
        unfolding i_max_def
        by (rule Max_ge[OF event_indices_finite j_in])
      with j_props show False by simp
    qed
  qed

  \<comment> \<open>Step 3: case-split on the shape of clean_prefix_of R ! i_max.\<close>
  show ?thesis
  proof (cases "clean_prefix_of R ! i_max")
    case (Cdc c e)
    \<comment> \<open>Cdc case: apply clean_prefix_of_cdc_generated_from_observed_cdc
        to extract the three correspondence conjuncts.\<close>
    have e_in_cp: "Cdc c e \<in> set (clean_prefix_of R)"
      using i_max_lt Cdc nth_mem by force
    have cdc_correspondence:
      "(c, e) \<in> set (cdc_events_of R)
       \<and> key_of e \<in> scope_of R
       \<and> src_le c (frontier_of R)"
      using clean_prefix_of_cdc_generated_from_observed_cdc[OF wf e_in_cp]
      by blast
    have key_eq: "key_of e = k"
      using i_max_event_key Cdc by simp
    show ?thesis
    proof (intro disjI1 exI[where x = i_max] exI[where x = c] exI[where x = e] conjI)
      show "i_max < length (clean_prefix_of R)" by (rule i_max_lt)
      show "clean_prefix_of R ! i_max = Cdc c e" by (rule Cdc)
      show "key_of e = k" by (rule key_eq)
      show "\<forall>j. i_max < j \<and> j < length (clean_prefix_of R)
                \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k"
        by (rule i_max_latest)
      show "(c, e) \<in> set (cdc_events_of R)" using cdc_correspondence by simp
      show "src_le c (frontier_of R)" using cdc_correspondence by simp
    qed
  next
    case (Refresh k' m' c_read)
    \<comment> \<open>Refresh case: i_max_event_key forces k' = k, then apply
        clean_prefix_of_refresh_generated_by_responsible_chunk.\<close>
    have k'_eq_k: "k' = k"
      using i_max_event_key Refresh by simp
    have refresh_in_cp: "Refresh k m' c_read \<in> set (clean_prefix_of R)"
      using i_max_lt Refresh k'_eq_k nth_mem by force
    obtain ch where ch_props:
      "responsible_chunk R k = Some ch"
      "chunk_read_coordinate R ch = c_read"
      "chunk_read_result R ch k = Some m'"
      using clean_prefix_of_refresh_generated_by_responsible_chunk[OF wf refresh_in_cp]
      by blast
    show ?thesis
    proof (intro disjI2 exI[where x = i_max] exI[where x = ch]
                       exI[where x = m'] exI[where x = c_read] conjI)
      show "i_max < length (clean_prefix_of R)" by (rule i_max_lt)
      show "clean_prefix_of R ! i_max = Refresh k m' c_read"
        using Refresh k'_eq_k by simp
      show "\<forall>j. i_max < j \<and> j < length (clean_prefix_of R)
                \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k"
        by (rule i_max_latest)
      show "responsible_chunk R k = Some ch" using ch_props by simp
      show "chunk_read_result R ch k = Some m'" using ch_props by simp
      show "chunk_read_coordinate R ch = c_read" using ch_props by simp
    qed
  qed
qed

text \<open>
  Auxiliary lemma used by clean_prefix_of_per_key_replay_equals_source:
  the @{const Apply} value at a key
  @{text k} reduces to the per-event constructor effect of the
  @{text k}-event at the @{text "latest"} position, when one such
  position is named.

  Generic fact about @{const Apply} on lists of @{type replay_event}:
  given a position @{text i_max} in a sequence @{text \<sigma>} such that
  @{text "event_key (\<sigma> ! i_max) = k"} and no later position in
  @{text \<sigma>} carries @{text "event_key = k"}, the per-key value
  @{text "Apply \<sigma> k"} equals the per-constructor effect of
  @{text "\<sigma> ! i_max"}: @{term "Some v"} for the @{text Cdc}
  @{text Insert} / @{text Update} shapes, @{term None} for the
  @{text Cdc} @{text Delete} shape, and the observed value
  @{term m_obs} for the @{text Refresh} shape.

  Composes @{thm apply_latest_event_wins} (Lemma 0.1) with a list
  decomposition argument: split @{text \<sigma>} at @{text i_max}, observe
  that the suffix @{term "drop (Suc i_max) \<sigma>"} contributes no
  @{text k}-events to the per-key filter (by the @{text i_max}
  latest-position assumption), and conclude that the last element of
  the per-key filter is @{text "\<sigma> ! i_max"}; then apply
  @{thm apply_latest_event_wins} to read off the per-constructor
  case.

  Used twice in the proof body of
  clean_prefix_of_per_key_replay_equals_source: once in the
  @{text Cdc} case (where @{text "\<sigma> ! i_max = Cdc c e"}) and once
  in the @{text Refresh} case (where
  @{text "\<sigma> ! i_max = Refresh k m c_read"}).
  Live here at the site of clean_prefix_of_per_key_replay_equals_source
  rather than in @{file Replay.thy}
  because that is its only consumer; relocation to @{file Replay.thy}
  is reasonable if a second consumer ever materializes.
\<close>

lemma apply_at_latest_k_event:
  fixes \<sigma> :: "('k, 'v) replay_event list"
    and k :: 'k
    and i :: nat
  assumes i_lt:    "i < length \<sigma>"
      and i_key:   "event_key (\<sigma> ! i) = k"
      and i_last:  "\<forall> j. i < j \<and> j < length \<sigma> \<longrightarrow> event_key (\<sigma> ! j) \<noteq> k"
  shows "Apply \<sigma> k = (case \<sigma> ! i of
                        Cdc _ (Insert _ v) \<Rightarrow> Some v
                      | Cdc _ (Update _ v) \<Rightarrow> Some v
                      | Cdc _ (Delete _)   \<Rightarrow> None
                      | Refresh _ m_obs _  \<Rightarrow> m_obs)"
proof -
  let ?P = "\<lambda>e :: ('k, 'v) replay_event. event_key e = k"
  let ?\<sigma>_k = "filter ?P \<sigma>"

  \<comment> \<open>Decompose @{text \<sigma>} at position @{text i}.\<close>
  have decomp: "\<sigma> = take i \<sigma> @ [\<sigma> ! i] @ drop (Suc i) \<sigma>"
    using i_lt
    by (metis Cons_nth_drop_Suc append_Cons append_Nil append_take_drop_id)

  \<comment> \<open>The drop part has no k-events.\<close>
  have drop_no_k: "filter ?P (drop (Suc i) \<sigma>) = []"
  proof -
    have "\<forall> e \<in> set (drop (Suc i) \<sigma>). event_key e \<noteq> k"
    proof
      fix e assume e_in: "e \<in> set (drop (Suc i) \<sigma>)"
      then obtain j where j_lt_drop: "j < length (drop (Suc i) \<sigma>)"
                          and e_at: "drop (Suc i) \<sigma> ! j = e"
        by (auto simp: in_set_conv_nth)
      let ?j' = "Suc (i + j)"
      have j'_lt: "?j' < length \<sigma>"
        using j_lt_drop by simp
      have e_eq: "e = \<sigma> ! ?j'"
        using e_at j_lt_drop
        by (simp add: add.commute)
      have i_lt_j': "i < ?j'" by simp
      from i_last i_lt_j' j'_lt
      have "event_key (\<sigma> ! ?j') \<noteq> k" by blast
      thus "event_key e \<noteq> k" using e_eq by simp
    qed
    thus ?thesis by (simp add: filter_empty_conv)
  qed

  \<comment> \<open>Filter splits + drop has no k-events: filter equals
      filter on the prefix, with @{text "[\<sigma> ! i]"} appended.\<close>
  have filter_eq:
    "?\<sigma>_k = filter ?P (take i \<sigma>) @ [\<sigma> ! i]"
  proof -
    have "?\<sigma>_k = filter ?P (take i \<sigma> @ [\<sigma> ! i] @ drop (Suc i) \<sigma>)"
      using decomp by simp
    also have "\<dots> = filter ?P (take i \<sigma>) @ filter ?P [\<sigma> ! i]
                    @ filter ?P (drop (Suc i) \<sigma>)"
      by simp
    also have "filter ?P [\<sigma> ! i] = [\<sigma> ! i]"
      using i_key by simp
    also have "filter ?P (drop (Suc i) \<sigma>) = []"
      by (rule drop_no_k)
    finally show ?thesis by simp
  qed

  have nonempty: "?\<sigma>_k \<noteq> []"
    using filter_eq by simp
  have last_eq: "last ?\<sigma>_k = \<sigma> ! i"
    using filter_eq by simp

  \<comment> \<open>Apply via apply_latest_event_wins, then read off via last_eq.\<close>
  have apply_eq:
    "Apply \<sigma> k = (case ?\<sigma>_k of
                    []     \<Rightarrow> None
                  | _ # _  \<Rightarrow> (case last ?\<sigma>_k of
                                 Cdc _ (Insert _ v) \<Rightarrow> Some v
                               | Cdc _ (Update _ v) \<Rightarrow> Some v
                               | Cdc _ (Delete _)   \<Rightarrow> None
                               | Refresh _ m_obs _  \<Rightarrow> m_obs))"
    by (rule apply_latest_event_wins)
  also have "\<dots> = (case last ?\<sigma>_k of
                     Cdc _ (Insert _ v) \<Rightarrow> Some v
                   | Cdc _ (Update _ v) \<Rightarrow> Some v
                   | Cdc _ (Delete _)   \<Rightarrow> None
                   | Refresh _ m_obs _  \<Rightarrow> m_obs)"
    using nonempty by (cases ?\<sigma>_k) auto
  also have "\<dots> = (case \<sigma> ! i of
                     Cdc _ (Insert _ v) \<Rightarrow> Some v
                   | Cdc _ (Update _ v) \<Rightarrow> Some v
                   | Cdc _ (Delete _)   \<Rightarrow> None
                   | Refresh _ m_obs _  \<Rightarrow> m_obs)"
    using last_eq by simp
  finally show ?thesis .
qed

text \<open>
  Auxiliary lemma used by clean_prefix_of_per_key_replay_equals_source:
  if no @{text k}-event in
  @{text "src_history_of R = H"} lies strictly past a coordinate
  @{text c'} and at-or-before the frontier, then
  @{term "Src b0 H f k"} restricted to @{text k} agrees with
  @{term "Src b0 H c' k"}. Generic property of @{const Src} +
  @{const latest_src_event} on histories: when @{term latest_src_event}
  cand-set agrees on the two thresholds (no @{text k}-events in the
  open interval @{text "(c', f]"}), the per-key state is identical.

  Used in the @{text Refresh} case of
  clean_prefix_of_per_key_replay_equals_source: lifts
  @{thm refresh_coordinate_match} (Lemma 0.5; Src at chunk-read
  coordinate) to Src at frontier when no later source event for
  @{text k} appears in the open interval @{text "(c_read, frontier_of(R)]"}.
\<close>

lemma src_eq_when_no_later_src_event_for_k:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and c' f :: frontier
    and k :: 'k
  assumes c'_le_f: "src_le c' f"
      and no_later:
        "\<forall> i < length H. src_lt c' (hist_coord (H ! i))
                          \<and> src_le (hist_coord (H ! i)) f
                          \<longrightarrow> key_of (hist_event (H ! i)) \<noteq> k"
  shows "Src b0 H f k = Src b0 H c' k"
proof -
  let ?cand_f =
    "filter (\<lambda>i. src_le (hist_coord (H ! i)) f
              \<and> key_of (hist_event (H ! i)) = k)
            [0..<length H]"
  let ?cand_c' =
    "filter (\<lambda>i. src_le (hist_coord (H ! i)) c'
              \<and> key_of (hist_event (H ! i)) = k)
            [0..<length H]"
  let ?Pf  = "\<lambda>i. src_le (hist_coord (H ! i)) f
                  \<and> key_of (hist_event (H ! i)) = k"
  let ?Pc' = "\<lambda>i. src_le (hist_coord (H ! i)) c'
                  \<and> key_of (hist_event (H ! i)) = k"

  \<comment> \<open>The two candidate filters coincide.\<close>
  have cand_eq: "?cand_f = ?cand_c'"
  proof -
    have "\<And>i. i \<in> set [0..<length H] \<Longrightarrow> ?Pf i = ?Pc' i"
    proof -
      fix i assume i_in: "i \<in> set [0..<length H]"
      hence i_lt: "i < length H" by simp
      show "?Pf i = ?Pc' i"
      proof
        assume Pf: "?Pf i"
        hence le_f: "src_le (hist_coord (H ! i)) f"
          and key_eq: "key_of (hist_event (H ! i)) = k"
          by auto
        have "src_le (hist_coord (H ! i)) c'"
        proof (rule ccontr)
          assume "\<not> src_le (hist_coord (H ! i)) c'"
          hence "src_le c' (hist_coord (H ! i))"
                "hist_coord (H ! i) \<noteq> c'"
            using src_le_total
            by (auto simp: less_eq_src_coord_def)
          hence "src_lt c' (hist_coord (H ! i))"
            unfolding src_lt_def by simp
          with no_later i_lt le_f have "key_of (hist_event (H ! i)) \<noteq> k"
            by blast
          with key_eq show False by simp
        qed
        thus "?Pc' i" using key_eq by simp
      next
        assume Pc': "?Pc' i"
        hence le_c': "src_le (hist_coord (H ! i)) c'"
          and key_eq: "key_of (hist_event (H ! i)) = k"
          by auto
        have "src_le (hist_coord (H ! i)) f"
          using le_c' c'_le_f src_le_trans by blast
        thus "?Pf i" using key_eq by simp
      qed
    qed
    thus ?thesis by (rule filter_cong[OF refl])
  qed

  have "latest_src_event H f k = latest_src_event H c' k"
    unfolding latest_src_event_def using cand_eq by simp
  thus ?thesis
    unfolding Src_def by simp
qed

text \<open>
  Helper extractions for the Cdc branch of
  clean_prefix_of_per_key_replay_equals_source. These package the
  WF2 multiplicity payload at the granularity the Cdc-case proof
  needs: first as an mset fact on the scoped
  same-key/same-coordinate slice, then as list equality once a
  subsequence/order-preservation fact is supplied.
\<close>

lemma cdc_events_key_coord_slice_mset_eq_source_history_slice:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "('k, 'v) run"
    and k  :: 'k
    and ch :: "('k, 'v) chunk"
    and c  :: src_coord
  assumes wf: "wellformed_dblog_run b0 R H"
      and k_scope: "k \<in> scope_of R"
      and rc: "responsible_chunk R k = Some ch"
      and read_lt_c: "src_lt (chunk_read_coordinate R ch) c"
      and c_le_f: "src_le c (frontier_of R)"
  shows "mset (source_key_coord_slice k c (cdc_events_of R))
       = mset (source_key_coord_slice k c (src_history_of R))"
proof -
  note wf_body = wf[unfolded wellformed_dblog_run_def]
  from wf_body have wf2_mset:
    "\<forall> k \<in> scope_of R. \<forall> ch c.
       responsible_chunk R k = Some ch
       \<and> src_lt (chunk_read_coordinate R ch) c
       \<and> src_le c (frontier_of R)
       \<longrightarrow>
         mset (source_key_coord_slice k c (cdc_events_of R))
         = mset (source_key_coord_slice k c (src_history_of R))"
    by (elim conjE)
  from wf2_mset k_scope rc read_lt_c c_le_f show ?thesis by blast
qed

lemma cdc_events_key_coord_slice_eq_source_history_slice:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "('k, 'v) run"
    and k  :: 'k
    and ch :: "('k, 'v) chunk"
    and c  :: src_coord
  assumes wf: "wellformed_dblog_run b0 R H"
      and k_scope: "k \<in> scope_of R"
      and rc: "responsible_chunk R k = Some ch"
      and read_lt_c: "src_lt (chunk_read_coordinate R ch) c"
      and c_le_f: "src_le c (frontier_of R)"
      and sub:
        "subseq (source_key_coord_slice k c (cdc_events_of R))
                (source_key_coord_slice k c (src_history_of R))"
  shows "source_key_coord_slice k c (cdc_events_of R)
       = source_key_coord_slice k c (src_history_of R)"
proof -
  have ms:
    "mset (source_key_coord_slice k c (cdc_events_of R))
     = mset (source_key_coord_slice k c (src_history_of R))"
    by (rule cdc_events_key_coord_slice_mset_eq_source_history_slice
          [OF wf k_scope rc read_lt_c c_le_f])
  show ?thesis by (rule subseq_mset_eq_imp_eq[OF sub ms])
qed

lemma cdc_events_key_coord_slice_subseq_source_history_slice:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "('k, 'v) run"
    and k  :: 'k
    and c  :: src_coord
  assumes wf: "wellformed_dblog_run b0 R H"
      and k_scope: "k \<in> scope_of R"
      and c_le_f: "src_le c (frontier_of R)"
  shows "subseq (source_key_coord_slice k c (cdc_events_of R))
                (source_key_coord_slice k c (src_history_of R))"
proof -
  note wf_body = wf[unfolded wellformed_dblog_run_def]
  define in_slice
    where "in_slice =
      (\<lambda>p::(src_coord \<times> ('k, 'v) source_event).
        key_of (hist_event p) \<in> scope_of R
        \<and> src_le (hist_coord p) (frontier_of R))"
  let ?Q =
    "\<lambda>p::(src_coord \<times> ('k, 'v) source_event).
       hist_coord p = c \<and> key_of (hist_event p) = k"

  from wf_body obtain \<iota> :: "nat \<Rightarrow> nat" where
    iota_mono: "strict_mono \<iota>" and
    iota_body:
      "(let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of R
                              \<and> src_le (hist_coord p) (frontier_of R));
            cdc_in_slice = filter in_slice (cdc_events_of R);
            hist_in_slice = filter in_slice (src_history_of R)
        in \<forall>i. i < length cdc_in_slice
              \<longrightarrow> \<iota> i < length hist_in_slice
                    \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
    by (elim conjE exE)
  have iota_all:
    "\<forall>i. i < length (filter in_slice (cdc_events_of R))
      \<longrightarrow> \<iota> i < length (filter in_slice (src_history_of R))
            \<and> filter in_slice (cdc_events_of R) ! i
               = filter in_slice (src_history_of R) ! \<iota> i"
    using iota_body unfolding in_slice_def by (simp add: Let_def)

  have sub_in:
    "subseq (filter in_slice (cdc_events_of R))
            (filter in_slice (src_history_of R))"
  proof (rule subseq_from_strict_mono_nth[OF iota_mono])
    fix i
    assume i_lt: "i < length (filter in_slice (cdc_events_of R))"
    from iota_all i_lt
    show "\<iota> i < length (filter in_slice (src_history_of R))
          \<and> filter in_slice (cdc_events_of R) ! i
             = filter in_slice (src_history_of R) ! \<iota> i"
      by blast
  qed

  have sub_filtered:
    "subseq (filter ?Q (filter in_slice (cdc_events_of R)))
            (filter ?Q (filter in_slice (src_history_of R)))"
    by (rule subseq_filter[OF sub_in])

  have cdc_rewrite:
    "filter ?Q (filter in_slice (cdc_events_of R))
     = source_key_coord_slice k c (cdc_events_of R)"
    unfolding source_key_coord_slice_def in_slice_def
    by (simp add: filter_filter,
        rule filter_cong[OF refl],
        use k_scope c_le_f in auto)
  have hist_rewrite:
    "filter ?Q (filter in_slice (src_history_of R))
     = source_key_coord_slice k c (src_history_of R)"
    unfolding source_key_coord_slice_def in_slice_def
    by (simp add: filter_filter,
        rule filter_cong[OF refl],
        use k_scope c_le_f in auto)

  show ?thesis
    using sub_filtered by (simp only: cdc_rewrite hist_rewrite)
qed

lemma cdc_events_key_coord_slice_eq_source_history_slice_from_wf:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "('k, 'v) run"
    and k  :: 'k
    and ch :: "('k, 'v) chunk"
    and c  :: src_coord
  assumes wf: "wellformed_dblog_run b0 R H"
      and k_scope: "k \<in> scope_of R"
      and rc: "responsible_chunk R k = Some ch"
      and read_lt_c: "src_lt (chunk_read_coordinate R ch) c"
      and c_le_f: "src_le c (frontier_of R)"
  shows "source_key_coord_slice k c (cdc_events_of R)
       = source_key_coord_slice k c (src_history_of R)"
proof -
  have sub:
    "subseq (source_key_coord_slice k c (cdc_events_of R))
            (source_key_coord_slice k c (src_history_of R))"
    by (rule cdc_events_key_coord_slice_subseq_source_history_slice
          [OF wf k_scope c_le_f])
  show ?thesis
    by (rule cdc_events_key_coord_slice_eq_source_history_slice
          [OF wf k_scope rc read_lt_c c_le_f sub])
qed

lemma clean_prefix_cdc_key_coord_slice:
  fixes R :: "('k :: linorder, 'v) run"
    and k :: 'k
    and c :: src_coord
  assumes k_scope: "k \<in> scope_of R"
      and c_le_f: "src_le c (frontier_of R)"
  shows "filter
          (\<lambda>x. case x of
                 Cdc c' e \<Rightarrow> c' = c \<and> key_of e = k
               | Refresh _ _ _ \<Rightarrow> False)
          (clean_prefix_of R)
       = map (\<lambda>p. Cdc (hist_coord p) (hist_event p))
           (source_key_coord_slice k c (cdc_events_of R))"
proof -
  let ?mkRec = "\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                       crr_read_coord  = chunk_read_coordinate R ch,
                       crr_observation = chunk_read_result R ch \<rparr>"
  let ?cdc_part = "cdc_event_replays (scope_of R) (frontier_of R) (cdc_events_of R)"
  let ?refresh_part = "concat (map chunk_read_refreshes (map ?mkRec (chunks_list R)))"
  let ?inp = "?cdc_part @ ?refresh_part"
  let ?P = "\<lambda>x::('k, 'v) replay_event.
              case x of Cdc c' e \<Rightarrow> c' = c \<and> key_of e = k
                      | Refresh _ _ _ \<Rightarrow> False"
  let ?Qc = "\<lambda>x::('k, 'v) replay_event. cdc_coord x = c"

  have cp_eq: "clean_prefix_of R = sort_key cdc_coord ?inp"
    unfolding clean_prefix_of_def canonical_clean_prefix_def by simp
  have refresh_no_cdc_slice:
    "\<And> ch x. x \<in> set (chunk_read_refreshes (?mkRec ch)) \<Longrightarrow> \<not> ?P x"
    by (auto simp: chunk_read_refreshes_def List.map_filter_def split: option.splits)
  have refresh_filter_empty: "filter ?P ?refresh_part = []"
  proof -
    have "\<forall> x \<in> set ?refresh_part. \<not> ?P x"
      using refresh_no_cdc_slice by auto
    thus ?thesis by (simp add: filter_empty_conv)
  qed
  have stab_Qc: "filter ?Qc (clean_prefix_of R) = filter ?Qc ?inp"
    using cp_eq sort_key_stable[of cdc_coord c ?inp] by simp
  have P_chain:
    "filter ?P xs = filter ?P (filter ?Qc xs)"
    for xs :: "('k, 'v) replay_event list"
    by (induction xs) (auto split: replay_event.splits)
  have filter_P_cp: "filter ?P (clean_prefix_of R) = filter ?P ?cdc_part"
  proof -
    have "filter ?P (clean_prefix_of R) = filter ?P (filter ?Qc (clean_prefix_of R))"
      using P_chain by simp
    also have "\<dots> = filter ?P (filter ?Qc ?inp)"
      using stab_Qc by simp
    also have "\<dots> = filter ?P ?inp"
      using P_chain by simp
    also have "\<dots> = filter ?P ?cdc_part @ filter ?P ?refresh_part"
      by simp
    also have "\<dots> = filter ?P ?cdc_part"
      using refresh_filter_empty by simp
    finally show ?thesis .
  qed
  have cdc_part_slice:
    "filter ?P ?cdc_part
       = map (\<lambda>p. Cdc (hist_coord p) (hist_event p))
           (source_key_coord_slice k c (cdc_events_of R))"
  proof -
    let ?in_filter =
      "\<lambda>p::(src_coord \<times> ('k, 'v) source_event).
          key_of (snd p) \<in> scope_of R \<and> fst p \<le> frontier_of R"
    have cdc_part_eq:
      "?cdc_part =
         map (\<lambda>p. Cdc (hist_coord p) (hist_event p))
           (filter ?in_filter (cdc_events_of R))"
      unfolding cdc_event_replays_def
      by (simp add: map_filter_map_filter[symmetric])
    have filter_collapse:
      "filter (\<lambda>p. hist_coord p = c \<and> key_of (hist_event p) = k)
              (filter ?in_filter (cdc_events_of R))
       = source_key_coord_slice k c (cdc_events_of R)"
      unfolding source_key_coord_slice_def
      by (simp add: filter_filter,
          rule filter_cong[OF refl],
          use k_scope c_le_f in \<open>auto simp: less_eq_src_coord_def\<close>)
    have "filter ?P ?cdc_part
        = filter ?P
            (map (\<lambda>p. Cdc (hist_coord p) (hist_event p))
              (filter ?in_filter (cdc_events_of R)))"
      using cdc_part_eq by simp
    also have "\<dots>
        = map (\<lambda>p. Cdc (hist_coord p) (hist_event p))
            (filter (\<lambda>p. hist_coord p = c \<and> key_of (hist_event p) = k)
              (filter ?in_filter (cdc_events_of R)))"
      by (simp add: filter_map o_def)
    also have "\<dots>
        = map (\<lambda>p. Cdc (hist_coord p) (hist_event p))
            (source_key_coord_slice k c (cdc_events_of R))"
      using filter_collapse by simp
    finally show ?thesis .
  qed
  show ?thesis using filter_P_cp cdc_part_slice by simp
qed

lemma clean_prefix_same_coord_refresh_before_cdc_false:
  fixes R :: "('k :: linorder, 'v) run"
    and k :: 'k
    and m :: "'v option"
    and c :: src_coord
    and e :: "('k, 'v) source_event"
    and i j :: nat
  assumes ij: "i < j"
      and j_lt: "j < length (clean_prefix_of R)"
      and at_i: "clean_prefix_of R ! i = Refresh k m c"
      and at_j: "clean_prefix_of R ! j = Cdc c e"
  shows False
proof -
  let ?mkRec = "\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                       crr_read_coord  = chunk_read_coordinate R ch,
                       crr_observation = chunk_read_result R ch \<rparr>"
  let ?cdc_part = "cdc_event_replays (scope_of R) (frontier_of R) (cdc_events_of R)"
  let ?refresh_part = "concat (map chunk_read_refreshes (map ?mkRec (chunks_list R)))"
  let ?inp = "?cdc_part @ ?refresh_part"
  let ?Qc = "\<lambda>x::('k, 'v) replay_event. cdc_coord x = c"
  let ?A = "\<lambda>x::('k, 'v) replay_event. case x of Cdc _ _ \<Rightarrow> True | Refresh _ _ _ \<Rightarrow> False"
  let ?B = "\<lambda>x::('k, 'v) replay_event. case x of Refresh _ _ _ \<Rightarrow> True | Cdc _ _ \<Rightarrow> False"

  have i_lt: "i < length (clean_prefix_of R)" using ij j_lt by simp
  have Q_i: "?Qc (clean_prefix_of R ! i)" using at_i by simp
  have Q_j: "?Qc (clean_prefix_of R ! j)" using at_j by simp
  have cp_eq: "clean_prefix_of R = sort_key cdc_coord ?inp"
    unfolding clean_prefix_of_def canonical_clean_prefix_def by simp
  have stab_Qc: "filter ?Qc (clean_prefix_of R) = filter ?Qc ?inp"
    using cp_eq sort_key_stable[of cdc_coord c ?inp] by simp

  define n_i where "n_i = length (filter ?Qc (take i (clean_prefix_of R)))"
  define n_j where "n_j = length (filter ?Qc (take j (clean_prefix_of R)))"

  have nth_i:
    "filter ?Qc (clean_prefix_of R) ! n_i = clean_prefix_of R ! i
   \<and> n_i < length (filter ?Qc (clean_prefix_of R))"
    using filter_take_nth[where xs = "clean_prefix_of R" and P = ?Qc and i = i,
                          OF i_lt Q_i]
    unfolding n_i_def by simp
  have nth_j:
    "filter ?Qc (clean_prefix_of R) ! n_j = clean_prefix_of R ! j
   \<and> n_j < length (filter ?Qc (clean_prefix_of R))"
    using filter_take_nth[where xs = "clean_prefix_of R" and P = ?Qc and i = j,
                          OF j_lt Q_j]
    unfolding n_j_def by simp
  have ni_lt_nj: "n_i < n_j"
    using length_filter_take_strict_mono[where xs = "clean_prefix_of R"
                                           and P = ?Qc
                                           and i = i and j = j,
                                         OF ij _ Q_i] j_lt
    unfolding n_i_def n_j_def by simp
  have nj_lt_inp: "n_j < length (filter ?Qc ?inp)"
    using nth_j stab_Qc by simp
  have ni_B: "?B (filter ?Qc ?inp ! n_i)"
    using nth_i at_i stab_Qc by simp
  have nj_A: "?A (filter ?Qc ?inp ! n_j)"
    using nth_j at_j stab_Qc by simp

  have cdc_all_A: "\<forall>x \<in> set (filter ?Qc ?cdc_part). ?A x"
    unfolding cdc_event_replays_def List.map_filter_def
    by (auto split: if_splits)
  have refresh_all_B: "\<forall>y \<in> set (filter ?Qc ?refresh_part). ?B y"
    unfolding chunk_read_refreshes_def List.map_filter_def
    by (auto split: option.splits)
  have disj: "?A z \<Longrightarrow> ?B z \<Longrightarrow> False" for z
    by (cases z) auto

  show False
    by (rule append_no_B_before_A
          [where xs = "filter ?Qc ?cdc_part"
             and ys = "filter ?Qc ?refresh_part"
             and zs = "filter ?Qc ?inp"
             and A = ?A and B = ?B
             and i = n_i and j = n_j])
       (use cdc_all_A refresh_all_B disj ni_lt_nj nj_lt_inp ni_B nj_A in auto)
qed

lemma latest_cdc_for_key_implies_chunk_read_strictly_before:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "('k, 'v) run"
    and k  :: 'k
    and i  :: nat
    and c  :: src_coord
    and e  :: "('k, 'v) source_event"
  assumes wf: "wellformed_dblog_run b0 R H"
      and k_scope: "k \<in> scope_of R"
      and i_lt: "i < length (clean_prefix_of R)"
      and cp_i: "clean_prefix_of R ! i = Cdc c e"
      and key_e: "key_of e = k"
      and i_latest:
        "\<forall> j. i < j \<and> j < length (clean_prefix_of R)
              \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k"
  shows "\<exists>ch. responsible_chunk R k = Some ch
            \<and> src_lt (chunk_read_coordinate R ch) c"
proof -
  obtain m c_read where refresh_in:
    "Refresh k m c_read \<in> set (clean_prefix_of R)"
    using clean_prefix_of_in_scope_responsible_chunk_refresh_exists[OF wf k_scope]
    by blast
  then obtain i_r where
    i_r_lt: "i_r < length (clean_prefix_of R)" and
    i_r_at: "clean_prefix_of R ! i_r = Refresh k m c_read"
    by (auto simp: in_set_conv_nth)
  obtain ch where
    rc: "responsible_chunk R k = Some ch" and
    read_eq: "chunk_read_coordinate R ch = c_read"
    using clean_prefix_of_refresh_generated_by_responsible_chunk[OF wf refresh_in]
    by blast

  have i_r_key: "event_key (clean_prefix_of R ! i_r) = k"
    using i_r_at by simp
  have i_r_le_i: "i_r \<le> i"
  proof (rule ccontr)
    assume "\<not> i_r \<le> i"
    hence i_lt_ir: "i < i_r" by simp
    from i_latest i_lt_ir i_r_lt
    have "event_key (clean_prefix_of R ! i_r) \<noteq> k" by blast
    with i_r_key show False by simp
  qed
  have i_r_ne_i: "i_r \<noteq> i"
  proof
    assume "i_r = i"
    with i_r_at cp_i show False by simp
  qed
  have i_r_lt_i: "i_r < i"
    using i_r_le_i i_r_ne_i by linarith
  have coord_le: "src_le c_read c"
    using clean_prefix_of_order_respects_coordinate[OF wf i_r_lt_i i_lt]
          i_r_at cp_i
    by simp
  have c_read_ne_c: "c_read \<noteq> c"
  proof
    assume c_eq: "c_read = c"
    have "clean_prefix_of R ! i_r = Refresh k m c"
      using i_r_at c_eq by simp
    from clean_prefix_same_coord_refresh_before_cdc_false[OF i_r_lt_i i_lt this cp_i]
    show False .
  qed
  have read_lt: "src_lt (chunk_read_coordinate R ch) c"
    using coord_le c_read_ne_c read_eq
    unfolding src_lt_def by simp
  show ?thesis using rc read_lt by blast
qed

lemma latest_cdc_no_source_event_strictly_after_coord:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "('k, 'v) run"
    and k  :: 'k
    and ch :: "('k, 'v) chunk"
    and i  :: nat
    and c  :: src_coord
    and e  :: "('k, 'v) source_event"
  assumes wf: "wellformed_dblog_run b0 R H"
      and k_scope: "k \<in> scope_of R"
      and rc: "responsible_chunk R k = Some ch"
      and read_lt_c: "src_lt (chunk_read_coordinate R ch) c"
      and i_lt: "i < length (clean_prefix_of R)"
      and cp_i: "clean_prefix_of R ! i = Cdc c e"
      and key_e: "key_of e = k"
      and i_latest:
        "\<forall> j. i < j \<and> j < length (clean_prefix_of R)
              \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k"
  shows "\<forall> j_src < length H.
           src_lt c (hist_coord (H ! j_src))
           \<and> src_le (hist_coord (H ! j_src)) (frontier_of R)
           \<longrightarrow> key_of (hist_event (H ! j_src)) \<noteq> k"
proof (intro allI impI)
  note wf_body = wf[unfolded wellformed_dblog_run_def]
  from wf_body have src_hist_eq: "src_history_of R = H"
    by (elim conjE)
  from wf_body have wf2_cov_all:
    "\<forall> k \<in> scope_of R. covers_ordinary_cdc R k (frontier_of R)"
    by (elim conjE)
  from wf_body have wf7_fwd:
    "\<forall> p \<in> set (cdc_events_of R).
       key_of (hist_event p) \<in> scope_of R
       \<and> src_le (hist_coord p) (frontier_of R)
       \<longrightarrow> Cdc (hist_coord p) (hist_event p)
             \<in> set (clean_prefix_of R)"
    by (elim conjE)

  from wf2_cov_all k_scope
  have cov_k: "covers_ordinary_cdc R k (frontier_of R)" by blast
  then obtain ch_cov where
    rc_cov: "responsible_chunk R k = Some ch_cov" and
    cov_body:
      "\<forall> i. i < length (src_history_of R)
              \<longrightarrow> src_lt (chunk_read_coordinate R ch_cov)
                         (hist_coord (src_history_of R ! i))
              \<longrightarrow> src_le (hist_coord (src_history_of R ! i)) (frontier_of R)
              \<longrightarrow> key_of (hist_event (src_history_of R ! i)) = k
              \<longrightarrow> src_history_of R ! i \<in> set (cdc_events_of R)"
    unfolding covers_ordinary_cdc_def by blast
  have ch_cov_eq: "ch_cov = ch"
    using rc_cov rc by simp

  fix j_src
  assume j_lt: "j_src < length H"
  assume j_after_le_f:
    "src_lt c (hist_coord (H ! j_src))
     \<and> src_le (hist_coord (H ! j_src)) (frontier_of R)"
  hence j_after: "src_lt c (hist_coord (H ! j_src))"
    and j_le_f: "src_le (hist_coord (H ! j_src)) (frontier_of R)"
    by auto
  show "key_of (hist_event (H ! j_src)) \<noteq> k"
  proof (rule ccontr)
    assume "\<not> key_of (hist_event (H ! j_src)) \<noteq> k"
    hence j_key: "key_of (hist_event (H ! j_src)) = k" by simp

    have read_lt_j:
      "src_lt (chunk_read_coordinate R ch) (hist_coord (H ! j_src))"
    proof -
      have read_le_c: "src_le (chunk_read_coordinate R ch) c"
        using read_lt_c unfolding src_lt_def by simp
      have read_ne_c: "chunk_read_coordinate R ch \<noteq> c"
        using read_lt_c unfolding src_lt_def by simp
      have c_le_j: "src_le c (hist_coord (H ! j_src))"
        using j_after unfolding src_lt_def by simp
      have read_le_j: "src_le (chunk_read_coordinate R ch) (hist_coord (H ! j_src))"
        using read_le_c c_le_j src_le_trans by blast
      have read_ne_j: "chunk_read_coordinate R ch \<noteq> hist_coord (H ! j_src)"
      proof
        assume eq: "chunk_read_coordinate R ch = hist_coord (H ! j_src)"
        hence "src_le c (chunk_read_coordinate R ch)"
          using c_le_j by simp
        hence "chunk_read_coordinate R ch = c"
          using read_le_c src_le_antisym by blast
        with read_ne_c show False by simp
      qed
      show ?thesis unfolding src_lt_def using read_le_j read_ne_j by simp
    qed
    have j_lt_R: "j_src < length (src_history_of R)"
      using j_lt src_hist_eq by simp
    have j_after_R:
      "src_lt (chunk_read_coordinate R ch_cov)
              (hist_coord (src_history_of R ! j_src))"
      using read_lt_j ch_cov_eq src_hist_eq by simp
    have j_le_f_R:
      "src_le (hist_coord (src_history_of R ! j_src)) (frontier_of R)"
      using j_le_f src_hist_eq by simp
    have j_key_R:
      "key_of (hist_event (src_history_of R ! j_src)) = k"
      using j_key src_hist_eq by simp

    from cov_body j_lt_R j_after_R j_le_f_R j_key_R
    have hjs_in_cdc_R: "src_history_of R ! j_src \<in> set (cdc_events_of R)"
      by blast
    have hjs_in_cdc: "H ! j_src \<in> set (cdc_events_of R)"
      using hjs_in_cdc_R src_hist_eq by simp
    have key_in_scope_j: "key_of (hist_event (H ! j_src)) \<in> scope_of R"
      using j_key k_scope by simp
    from wf7_fwd hjs_in_cdc key_in_scope_j j_le_f
    have cdc_in_cp:
      "Cdc (hist_coord (H ! j_src)) (hist_event (H ! j_src))
         \<in> set (clean_prefix_of R)"
      by blast
    then obtain i_h where
      i_h_lt: "i_h < length (clean_prefix_of R)" and
      i_h_at:
        "clean_prefix_of R ! i_h
          = Cdc (hist_coord (H ! j_src)) (hist_event (H ! j_src))"
      by (auto simp: in_set_conv_nth)
    have i_h_key: "event_key (clean_prefix_of R ! i_h) = k"
      using i_h_at j_key by simp

    have i_h_le_i: "i_h \<le> i"
    proof (rule ccontr)
      assume "\<not> i_h \<le> i"
      hence i_lt_ih: "i < i_h" by simp
      from i_latest i_lt_ih i_h_lt
      have "event_key (clean_prefix_of R ! i_h) \<noteq> k" by blast
      with i_h_key show False by simp
    qed

    consider (eq) "i_h = i" | (lt) "i_h < i"
      using i_h_le_i by linarith
    thus False
    proof cases
      case eq
      have c_eq_j: "c = hist_coord (H ! j_src)"
        using cp_i i_h_at eq by simp
      with j_after show False
        unfolding src_lt_def by simp
    next
      case lt
      from clean_prefix_of_order_respects_coordinate[OF wf lt i_lt]
      have "src_le (cdc_coord (clean_prefix_of R ! i_h))
                   (cdc_coord (clean_prefix_of R ! i))" .
      hence "src_le (hist_coord (H ! j_src)) c"
        using i_h_at cp_i by simp
      with j_after show False
        unfolding src_lt_def
        using src_le_antisym by blast
    qed
  qed
qed

lemma src_frontier_eq_effect_of_last_key_coord_slice:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and f c :: src_coord
    and k  :: 'k
    and e  :: "('k, 'v) source_event"
  assumes wf_h: "wellformed_src_history H"
      and c_le_f: "src_le c f"
      and no_later:
        "\<forall>j < length H.
           src_lt c (hist_coord (H ! j))
           \<and> src_le (hist_coord (H ! j)) f
           \<longrightarrow> key_of (hist_event (H ! j)) \<noteq> k"
      and slice_nonempty: "source_key_coord_slice k c H \<noteq> []"
      and last_slice: "last (source_key_coord_slice k c H) = (c, e)"
  shows "Src b0 H f k = (case e of
                          Insert _ v \<Rightarrow> Some v
                        | Update _ v \<Rightarrow> Some v
                        | Delete _   \<Rightarrow> None)"
proof -
  let ?Q = "\<lambda>p::(src_coord \<times> ('k, 'v) source_event).
              hist_coord p = c \<and> key_of (hist_event p) = k"
  let ?P = "\<lambda>j. src_le (hist_coord (H ! j)) f
                  \<and> key_of (hist_event (H ! j)) = k"

  obtain i where
    i_lt: "i < length H" and
    Q_i: "?Q (H ! i)" and
    H_i_last: "H ! i = last (filter ?Q H)" and
    no_after_same: "\<forall>j. i < j \<and> j < length H \<longrightarrow> \<not> ?Q (H ! j)"
    using last_filter_index[of ?Q H] slice_nonempty
    unfolding source_key_coord_slice_def by blast
  have H_i: "H ! i = (c, e)"
    using H_i_last last_slice
    unfolding source_key_coord_slice_def by simp
  have coord_i: "hist_coord (H ! i) = c"
    using H_i by simp
  have event_i: "hist_event (H ! i) = e"
    using H_i by simp
  have P_i: "?P i"
    using c_le_f Q_i by simp

  have no_after_P: "\<forall>j. i < j \<and> j < length H \<longrightarrow> \<not> ?P j"
  proof (intro allI impI)
    fix j
    assume j_assm: "i < j \<and> j < length H"
    hence i_le_j: "i \<le> j" and j_lt: "j < length H" by auto
    show "\<not> ?P j"
    proof
      assume P_j: "?P j"
      hence j_le_f: "src_le (hist_coord (H ! j)) f"
        and j_key: "key_of (hist_event (H ! j)) = k"
        by auto
      have c_le_j: "src_le c (hist_coord (H ! j))"
        using wellformed_src_history_coord_mono[OF wf_h i_le_j j_lt]
              coord_i
        by simp
      show False
      proof (cases "hist_coord (H ! j) = c")
        case True
        hence "?Q (H ! j)" using j_key by simp
        with no_after_same j_assm show False by blast
      next
        case False
        hence c_lt_j: "src_lt c (hist_coord (H ! j))"
          using c_le_j unfolding src_lt_def by simp
        from no_later j_lt c_lt_j j_le_f
        have "key_of (hist_event (H ! j)) \<noteq> k" by blast
        with j_key show False by simp
      qed
    qed
  qed

  have cand_last:
    "filter ?P [0..<length H] \<noteq> []
     \<and> last (filter ?P [0..<length H]) = i"
    by (rule last_filter_upt_eq[OF i_lt P_i no_after_P])
  hence latest_eq: "latest_src_event H f k = Some i"
    unfolding latest_src_event_def by (simp add: Let_def)

  have "Src b0 H f k =
          (case hist_event (H ! i) of
             Insert _ v \<Rightarrow> Some v
           | Update _ v \<Rightarrow> Some v
           | Delete _   \<Rightarrow> None)"
    unfolding Src_def using latest_eq by simp
  thus ?thesis using event_i by simp
qed

lemma latest_cdc_event_last_in_clean_prefix_key_coord_slice:
  fixes R :: "('k :: linorder, 'v) run"
    and k :: 'k
    and i :: nat
    and c :: src_coord
    and e :: "('k, 'v) source_event"
  assumes i_lt: "i < length (clean_prefix_of R)"
      and cp_i: "clean_prefix_of R ! i = Cdc c e"
      and key_e: "key_of e = k"
      and i_latest:
        "\<forall> j. i < j \<and> j < length (clean_prefix_of R)
              \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k"
  shows "let slice =
           filter
             (\<lambda>x. case x of
                    Cdc c' e' \<Rightarrow> c' = c \<and> key_of e' = k
                  | Refresh _ _ _ \<Rightarrow> False)
             (clean_prefix_of R)
         in slice \<noteq> [] \<and> last slice = Cdc c e"
proof -
  let ?P = "\<lambda>x::('k, 'v) replay_event.
              case x of Cdc c' e' \<Rightarrow> c' = c \<and> key_of e' = k
                      | Refresh _ _ _ \<Rightarrow> False"
  have P_i: "?P (clean_prefix_of R ! i)"
    using cp_i key_e by simp
  have decomp:
    "clean_prefix_of R =
       take i (clean_prefix_of R)
       @ [clean_prefix_of R ! i]
       @ drop (Suc i) (clean_prefix_of R)"
    using i_lt
    by (metis Cons_nth_drop_Suc append_Cons append_Nil append_take_drop_id)
  have drop_no_P: "filter ?P (drop (Suc i) (clean_prefix_of R)) = []"
  proof -
    have "\<forall> x \<in> set (drop (Suc i) (clean_prefix_of R)). \<not> ?P x"
    proof
      fix x
      assume x_in: "x \<in> set (drop (Suc i) (clean_prefix_of R))"
      then obtain j where
        j_lt_drop: "j < length (drop (Suc i) (clean_prefix_of R))"
        and x_at: "drop (Suc i) (clean_prefix_of R) ! j = x"
        by (auto simp: in_set_conv_nth)
      let ?j' = "Suc (i + j)"
      have j'_lt: "?j' < length (clean_prefix_of R)"
        using j_lt_drop by simp
      have x_eq: "x = clean_prefix_of R ! ?j'"
        using x_at j_lt_drop by (simp add: add.commute)
      have i_lt_j': "i < ?j'" by simp
      from i_latest i_lt_j' j'_lt
      have later_not_k: "event_key (clean_prefix_of R ! ?j') \<noteq> k" by blast
      show "\<not> ?P x"
      proof
        assume Px: "?P x"
        hence "event_key x = k"
          by (cases x) auto
        hence "event_key (clean_prefix_of R ! ?j') = k"
          using x_eq by simp
        with later_not_k show False by simp
      qed
    qed
    thus ?thesis by (simp add: filter_empty_conv)
  qed
  have slice_eq:
    "filter ?P (clean_prefix_of R)
     = filter ?P (take i (clean_prefix_of R)) @ [Cdc c e]"
  proof -
    have "filter ?P (clean_prefix_of R)
        = filter ?P
            (take i (clean_prefix_of R)
             @ [clean_prefix_of R ! i]
             @ drop (Suc i) (clean_prefix_of R))"
      using decomp by simp
    also have "\<dots>
        = filter ?P (take i (clean_prefix_of R))
          @ filter ?P [clean_prefix_of R ! i]
          @ filter ?P (drop (Suc i) (clean_prefix_of R))"
      by simp
    also have "\<dots> = filter ?P (take i (clean_prefix_of R)) @ [Cdc c e]"
      using P_i cp_i drop_no_P by simp
    finally show ?thesis .
  qed
  show ?thesis
    using slice_eq by simp
qed

lemma clean_prefix_of_per_key_replay_equals_source_cdc_case:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "('k, 'v) run"
    and k  :: 'k
    and i_max :: nat
    and c  :: src_coord
    and e  :: "('k, 'v) source_event"
  assumes wf: "wellformed_dblog_run b0 R H"
      and k_in_scope: "k \<in> scope_of R"
      and i_max_lt: "i_max < length (clean_prefix_of R)"
      and cp_at_imax: "clean_prefix_of R ! i_max = Cdc c e"
      and key_e: "key_of e = k"
      and i_max_latest:
        "\<forall>j. i_max < j \<and> j < length (clean_prefix_of R)
              \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k"
      and c_le_f: "src_le c (frontier_of R)"
  shows "Apply (clean_prefix_of R) k = Src b0 H (frontier_of R) k"
proof -
  note wf_body = wf[unfolded wellformed_dblog_run_def]
  from wf_body have src_hist_eq: "src_history_of R = H"
    by (elim conjE)
  from wf_body have wf_h: "wellformed_src_history H"
    by (elim conjE)

  let ?E =
    "(case e of Insert _ v \<Rightarrow> Some v
              | Update _ v \<Rightarrow> Some v
              | Delete _   \<Rightarrow> None)"

  have ev_key_imax: "event_key (clean_prefix_of R ! i_max) = k"
    using cp_at_imax key_e by simp
  have apply_val: "Apply (clean_prefix_of R) k = ?E"
  proof -
    have "Apply (clean_prefix_of R) k =
            (case clean_prefix_of R ! i_max of
               Cdc _ (Insert _ v) \<Rightarrow> Some v
             | Cdc _ (Update _ v) \<Rightarrow> Some v
             | Cdc _ (Delete _)   \<Rightarrow> None
             | Refresh _ m_obs _  \<Rightarrow> m_obs)"
      by (rule apply_at_latest_k_event[OF i_max_lt ev_key_imax i_max_latest])
    also have "\<dots> = ?E"
      using cp_at_imax by (cases e) auto
    finally show ?thesis .
  qed

  obtain ch where
    rc: "responsible_chunk R k = Some ch" and
    read_lt_c: "src_lt (chunk_read_coordinate R ch) c"
    using latest_cdc_for_key_implies_chunk_read_strictly_before
            [OF wf k_in_scope i_max_lt cp_at_imax key_e i_max_latest]
    by blast

  have no_later_src:
    "\<forall>j < length H.
       src_lt c (hist_coord (H ! j))
       \<and> src_le (hist_coord (H ! j)) (frontier_of R)
       \<longrightarrow> key_of (hist_event (H ! j)) \<noteq> k"
    by (rule latest_cdc_no_source_event_strictly_after_coord
          [OF wf k_in_scope rc read_lt_c i_max_lt cp_at_imax key_e i_max_latest])

  have slice_eq_R:
    "source_key_coord_slice k c (cdc_events_of R)
     = source_key_coord_slice k c (src_history_of R)"
    by (rule cdc_events_key_coord_slice_eq_source_history_slice_from_wf
          [OF wf k_in_scope rc read_lt_c c_le_f])

  let ?cp_slice =
    "filter
       (\<lambda>x::('k, 'v) replay_event.
          case x of
            Cdc c' e' \<Rightarrow> c' = c \<and> key_of e' = k
          | Refresh _ _ _ \<Rightarrow> False)
       (clean_prefix_of R)"
  let ?cdc_slice = "source_key_coord_slice k c (cdc_events_of R)"
  let ?hist_R_slice = "source_key_coord_slice k c (src_history_of R)"
  let ?hist_H_slice = "source_key_coord_slice k c H"

  have cp_slice_nonempty: "?cp_slice \<noteq> []"
    and cp_slice_last: "last ?cp_slice = Cdc c e"
    using latest_cdc_event_last_in_clean_prefix_key_coord_slice
            [OF i_max_lt cp_at_imax key_e i_max_latest]
    by (simp_all add: Let_def)
  have cp_slice_map:
    "?cp_slice =
       map (\<lambda>p. Cdc (hist_coord p) (hist_event p)) ?cdc_slice"
    by (rule clean_prefix_cdc_key_coord_slice[OF k_in_scope c_le_f])
  have cdc_slice_nonempty: "?cdc_slice \<noteq> []"
    using cp_slice_nonempty cp_slice_map by auto
  have last_map:
    "last ?cp_slice =
       Cdc (hist_coord (last ?cdc_slice)) (hist_event (last ?cdc_slice))"
  proof -
    let ?f = "\<lambda>p. Cdc (hist_coord p) (hist_event p)"
    have cdc_decomp: "?cdc_slice = butlast ?cdc_slice @ [last ?cdc_slice]"
      using cdc_slice_nonempty by simp
    have map_decomp:
      "map ?f ?cdc_slice = map ?f (butlast ?cdc_slice) @ [?f (last ?cdc_slice)]"
      by (subst cdc_decomp, simp)
    have "last ?cp_slice = last (map ?f ?cdc_slice)"
      using cp_slice_map by simp
    also have "\<dots> = last (map ?f (butlast ?cdc_slice) @ [?f (last ?cdc_slice)])"
      using map_decomp by simp
    also have "\<dots> = ?f (last ?cdc_slice)"
      by simp
    finally show ?thesis .
  qed
  have last_cdc_slice: "last ?cdc_slice = (c, e)"
  proof -
    have coord_eq: "hist_coord (last ?cdc_slice) = c"
      and event_eq: "hist_event (last ?cdc_slice) = e"
      using last_map cp_slice_last by simp_all
    show ?thesis
      using coord_eq event_eq by (cases "last ?cdc_slice") simp
  qed

  have hist_R_nonempty: "?hist_R_slice \<noteq> []"
    using slice_eq_R cdc_slice_nonempty by simp
  have hist_R_last: "last ?hist_R_slice = (c, e)"
    using slice_eq_R last_cdc_slice by simp
  have hist_H_nonempty: "?hist_H_slice \<noteq> []"
    using hist_R_nonempty src_hist_eq by simp
  have hist_H_last: "last ?hist_H_slice = (c, e)"
    using hist_R_last src_hist_eq by simp

  have src_val: "Src b0 H (frontier_of R) k = ?E"
    by (rule src_frontier_eq_effect_of_last_key_coord_slice
          [OF wf_h c_le_f no_later_src hist_H_nonempty hist_H_last])

  show ?thesis using apply_val src_val by simp
qed

text \<open>
  The clean_prefix_of_per_key_replay_equals_source lemma (THIS
  lemma) is the per-key value-equality form of the Layer 2
  source-side
  soundness conclusion: under the wellformed-DBLog-run premise, on
  any in-scope key @{text k}, the per-key @{const Apply} value of
  @{const clean_prefix_of} equals @{term "Src b0 H (frontier_of R) k"}.
  This is the load-bearing per-key reduction step of the Layer 2 main
  theorem proof; the Layer 2 main theorem follows by Lemma 0.2
  (Restriction equality is pointwise) + @{text virtual_cut_state_def}
  unfolding.

  This lemma composes clean_prefix_of_latest_replay_correspondence
  (structural correspondence; Cdc vs Refresh
  disjunction at the latest @{text k}-event position) with the four
  Layer 0 basic lemmas and the WF body. By the case split on that
  disjunction:

    \<^item> Refresh case (@{text "ev = Refresh k m c_read"};
        @{const responsible_chunk} + @{const chunk_read_result}
        identification): @{const Apply} value equals @{text m} (via
        @{thm apply_at_latest_k_event}). @{text "m = Src b0 H c_read k"}
        via @{thm refresh_coordinate_match} (Lemma 0.5).
        @{text "Src b0 H (frontier_of R) k = Src b0 H c_read k"} follows
        from a no-source-event-for-@{text k}-in-@{text "(c_read, frontier]"}
        argument: any such source event would yield a
        @{text "Cdc (c', _)"} in @{const clean_prefix_of} via
        @{const covers_ordinary_cdc} + WF7 forward, which by
        clean_prefix_of_order_respects_coordinate
        would be at strictly later position than the @{text Refresh},
        contradicting @{text Refresh} being the latest @{text k}-event.

    \<^item> Cdc case (@{text "ev = Cdc c e"}, @{text "key_of e = k"},
        @{text "(c, e) \<in> cdc_events_of R"}): delegated to the
        standalone helper lemma
        clean_prefix_of_per_key_replay_equals_source_cdc_case above.
        The @{const Apply} value equals the per-Insert/Update/Delete
        case of @{text e} (via @{thm apply_at_latest_k_event}). For
        the source value, the helper identifies @{text k}'s
        responsible chunk and shows its read coordinate is strictly
        before @{text c}
        (latest_cdc_for_key_implies_chunk_read_strictly_before), then
        derives the per-key / per-coordinate slice equality
        @{text "source_key_coord_slice k c (cdc_events_of R)
                = source_key_coord_slice k c (src_history_of R)"}
        from cdc_events_key_coord_slice_eq_source_history_slice_from_wf
        (which consumes the WF2 order-preserving sublist and post-read
        multiplicity conjuncts). With clean_prefix_cdc_key_coord_slice
        this places @{text "(c, e)"} as the last entry of the
        key-@{text k} coordinate-@{text c} slice of @{text H}; then
        src_frontier_eq_effect_of_last_key_coord_slice --- using
        latest_cdc_no_source_event_strictly_after_coord to exclude any
        in-scope @{text k}-event strictly after @{text c} ---
        evaluates @{term "Src b0 H (frontier_of R) k"} to the same
        per-Insert/Update/Delete case.

  Both cases rule out a source event for @{text k} strictly after
  the latest replay coordinate. The Refresh case derives this from
  @{const covers_ordinary_cdc} + WF7 forward +
  clean_prefix_of_order_respects_coordinate; the Cdc case obtains the
  corresponding fact (latest_cdc_no_source_event_strictly_after_coord)
  and additionally pins the latest same-coordinate value through the
  key-coordinate slice equality, inside the helper lemma
  clean_prefix_of_per_key_replay_equals_source_cdc_case.

  This lemma is the last of the supporting clean-prefix lemmas. It
  feeds the paper-level proof of Lemma 1.1 and the Layer 2 main
  theorem @{text wellformed_run_implies_virtual_cut}.
\<close>

lemma clean_prefix_of_per_key_replay_equals_source:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "('k, 'v) run"
    and k  :: 'k
  assumes wf:          "wellformed_dblog_run b0 R H"
      and k_in_scope:  "k \<in> scope_of R"
  shows "Apply (clean_prefix_of R) k = Src b0 H (frontier_of R) k"
proof -
  \<comment> \<open>Step 1: extract the WF body conjuncts this lemma consumes.
      Using the pattern wf_body = wf[unfolded ...] + (elim conjE),
      individual conjuncts are extracted one by one rather than as a
      compound (elim conjE breaks all conjunctions, including WF0's
      inner src_history_of R = H ∧ wellformed_src_history H).\<close>
  note wf_body = wf[unfolded wellformed_dblog_run_def]
  from wf_body have src_hist_eq: "src_history_of R = H"
    by (elim conjE)
  from wf_body have wf_h: "wellformed_src_history H"
    by (elim conjE)
  from wf_body have wf2_cov_all:
    "\<forall> k \<in> scope_of R. covers_ordinary_cdc R k (frontier_of R)"
    by (elim conjE)
  from wf_body have wf2_faith:
    "\<forall> p \<in> set (cdc_events_of R).
       key_of (hist_event p) \<in> scope_of R
       \<and> src_le (hist_coord p) (frontier_of R)
       \<longrightarrow> p \<in> set (src_history_of R)"
    by (elim conjE)
  from wf_body have wf5:
    "\<forall> ch \<in> chunks R.
        src_le (chunk_read_coordinate R ch) (frontier_of R)"
    by (elim conjE)
  from wf_body have wf7_fwd:
    "\<forall> p \<in> set (cdc_events_of R).
       key_of (hist_event p) \<in> scope_of R
       \<and> src_le (hist_coord p) (frontier_of R)
       \<longrightarrow> Cdc (hist_coord p) (hist_event p)
             \<in> set (clean_prefix_of R)"
    by (elim conjE)

  \<comment> \<open>Extract covers_ordinary_cdc R k (frontier_of R) for THIS k.\<close>
  from wf2_cov_all k_in_scope
  have cov_k: "covers_ordinary_cdc R k (frontier_of R)" by blast
  then obtain ch_k where
    rc_k: "responsible_chunk R k = Some ch_k" and
    cov_k_body:
      "\<forall> i. i < length (src_history_of R)
              \<longrightarrow> src_lt (chunk_read_coordinate R ch_k)
                         (hist_coord (src_history_of R ! i))
              \<longrightarrow> src_le (hist_coord (src_history_of R ! i)) (frontier_of R)
              \<longrightarrow> key_of (hist_event (src_history_of R ! i)) = k
              \<longrightarrow> src_history_of R ! i \<in> set (cdc_events_of R)"
    unfolding covers_ordinary_cdc_def by blast

  \<comment> \<open>Step 2: invoke clean_prefix_of_latest_replay_correspondence
      to obtain the Cdc-or-Refresh disjunction at the latest k-event
      position in clean_prefix_of(R).\<close>
  note latest_replay_disj = clean_prefix_of_latest_replay_correspondence[OF wf k_in_scope]

  \<comment> \<open>Step 3: case-split on the
      clean_prefix_of_latest_replay_correspondence disjunction.\<close>
  show ?thesis
  proof (rule disjE[OF latest_replay_disj])
    \<comment> \<open>**Cdc case**: latest k-event is a Cdc(c, e).\<close>
    assume cdc_disj:
      "\<exists> i c e. i < length (clean_prefix_of R)
              \<and> clean_prefix_of R ! i = Cdc c e
              \<and> key_of e = k
              \<and> (\<forall> j. i < j \<and> j < length (clean_prefix_of R)
                        \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k)
              \<and> (c, e) \<in> set (cdc_events_of R)
              \<and> src_le c (frontier_of R)"
    then obtain i_max c e where
      i_max_lt:    "i_max < length (clean_prefix_of R)" and
      cp_at_imax:  "clean_prefix_of R ! i_max = Cdc c e" and
      key_e:       "key_of e = k" and
      i_max_latest:
                   "\<forall> j. i_max < j \<and> j < length (clean_prefix_of R)
                          \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k" and
      ce_in_cdc:   "(c, e) \<in> set (cdc_events_of R)" and
      c_le_f:      "src_le c (frontier_of R)"
      by blast

    \<comment> \<open>Cdc case: delegated to the standalone helper lemma above.\<close>
    show "Apply (clean_prefix_of R) k = Src b0 H (frontier_of R) k"
      by (rule clean_prefix_of_per_key_replay_equals_source_cdc_case
            [OF wf k_in_scope i_max_lt cp_at_imax key_e i_max_latest
                c_le_f])
  next
    \<comment> \<open>**Refresh case**: latest k-event is a Refresh(k, m, c_read).\<close>
    assume refresh_disj:
      "\<exists> i ch m c_read.
          i < length (clean_prefix_of R)
          \<and> clean_prefix_of R ! i = Refresh k m c_read
          \<and> (\<forall> j. i < j \<and> j < length (clean_prefix_of R)
                    \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k)
          \<and> responsible_chunk R k = Some ch
          \<and> chunk_read_result R ch k = Some m
          \<and> chunk_read_coordinate R ch = c_read"
    then obtain i_max ch m c_read where
      i_max_lt:    "i_max < length (clean_prefix_of R)" and
      cp_at_imax:  "clean_prefix_of R ! i_max = Refresh k m c_read" and
      i_max_latest:
                   "\<forall> j. i_max < j \<and> j < length (clean_prefix_of R)
                          \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k" and
      rc_eq:       "responsible_chunk R k = Some ch" and
      crr_res:     "chunk_read_result R ch k = Some m" and
      cr_eq:       "chunk_read_coordinate R ch = c_read"
      by blast

    \<comment> \<open>Refresh case Step 1: ch_k = ch (uniqueness via Some-injectivity).\<close>
    have ch_eq: "ch = ch_k"
      using rc_eq rc_k by simp

    \<comment> \<open>Refresh case Step 2: ch ∈ chunks R + k ∈ chunk_domain R ch
        via WF1 (a) + WF1 (d).\<close>
    from wf_body have wf1d:
      "\<forall> k \<in> scope_of R. \<forall> ch.
         responsible_chunk R k = Some ch
           \<longleftrightarrow> ch \<in> chunks R \<and> owns R ch k"
      by (elim conjE)
    from wf1d k_in_scope rc_eq
    have ch_props: "ch \<in> chunks R \<and> owns R ch k" by blast
    hence ch_in_chunks: "ch \<in> chunks R" and k_in_dom: "k \<in> chunk_domain R ch"
      by auto

    \<comment> \<open>Refresh case Step 3: Apply value via apply_at_latest_k_event.\<close>
    have ev_key_imax: "event_key (clean_prefix_of R ! i_max) = k"
      using cp_at_imax by simp
    have apply_val: "Apply (clean_prefix_of R) k = m"
    proof -
      have "Apply (clean_prefix_of R) k =
              (case clean_prefix_of R ! i_max of
                 Cdc _ (Insert _ v) \<Rightarrow> Some v
               | Cdc _ (Update _ v) \<Rightarrow> Some v
               | Cdc _ (Delete _)   \<Rightarrow> None
               | Refresh _ m_obs _  \<Rightarrow> m_obs)"
        by (rule apply_at_latest_k_event[OF i_max_lt ev_key_imax i_max_latest])
      also have "\<dots> = m"
        using cp_at_imax by simp
      finally show ?thesis .
    qed

    \<comment> \<open>Refresh case Step 4: m = Src b0 H c_read k via Lemma 0.5
        (refresh_coordinate_match).\<close>
    have m_eq_src_at_cr: "m = Src b0 H c_read k"
    proof -
      from refresh_coordinate_match[OF wf ch_in_chunks k_in_dom crr_res]
      have "m = Src b0 H (chunk_read_coordinate R ch) k" .
      thus ?thesis using cr_eq by simp
    qed

    \<comment> \<open>Refresh case Step 5: no source event for k in (c_read, frontier].\<close>
    have no_later_src:
      "\<forall> j_src < length H. src_lt c_read (hist_coord (H ! j_src))
                            \<and> src_le (hist_coord (H ! j_src)) (frontier_of R)
                            \<longrightarrow> key_of (hist_event (H ! j_src)) \<noteq> k"
    proof (intro allI impI)
      fix j_src
      assume j_lt: "j_src < length H"
      assume j_after_le_f:
        "src_lt c_read (hist_coord (H ! j_src))
         \<and> src_le (hist_coord (H ! j_src)) (frontier_of R)"
      hence j_after: "src_lt c_read (hist_coord (H ! j_src))"
        and j_le_f: "src_le (hist_coord (H ! j_src)) (frontier_of R)"
        by auto
      show "key_of (hist_event (H ! j_src)) \<noteq> k"
      proof (rule ccontr)
        assume "\<not> key_of (hist_event (H ! j_src)) \<noteq> k"
        hence j_key: "key_of (hist_event (H ! j_src)) = k" by simp

        \<comment> \<open>chunk_read_coordinate R ch_k = chunk_read_coordinate R ch = c_read.\<close>
        have crk_eq: "chunk_read_coordinate R ch_k = c_read"
          using ch_eq cr_eq by simp
        have j_after_crk:
          "src_lt (chunk_read_coordinate R ch_k) (hist_coord (H ! j_src))"
          using crk_eq j_after by simp

        \<comment> \<open>Translate j_src's H properties to src_history_of R via src_hist_eq.\<close>
        have j_lt_R: "j_src < length (src_history_of R)"
          using j_lt src_hist_eq by simp
        have j_after_R:
          "src_lt (chunk_read_coordinate R ch_k)
                  (hist_coord (src_history_of R ! j_src))"
          using j_after_crk src_hist_eq by simp
        have j_le_f_R:
          "src_le (hist_coord (src_history_of R ! j_src)) (frontier_of R)"
          using j_le_f src_hist_eq by simp
        have j_key_R:
          "key_of (hist_event (src_history_of R ! j_src)) = k"
          using j_key src_hist_eq by simp

        \<comment> \<open>covers_ordinary_cdc: H!j_src ∈ cdc_events_of R.\<close>
        from cov_k_body j_lt_R j_after_R j_le_f_R j_key_R
        have hjs_in_cdc_R:
          "src_history_of R ! j_src \<in> set (cdc_events_of R)" by blast
        have hjs_in_cdc: "H ! j_src \<in> set (cdc_events_of R)"
          using hjs_in_cdc_R src_hist_eq by simp

        \<comment> \<open>WF7 forward: Cdc (hist_coord (H!j_src)) (hist_event (H!j_src))
            ∈ clean_prefix_of R.\<close>
        have key_in_scope_j:
          "key_of (hist_event (H ! j_src)) \<in> scope_of R"
          using j_key k_in_scope by simp
        from wf7_fwd hjs_in_cdc key_in_scope_j j_le_f
        have cdc_in_cp:
          "Cdc (hist_coord (H ! j_src)) (hist_event (H ! j_src))
             \<in> set (clean_prefix_of R)"
          by blast
        then obtain i_h where
          i_h_lt: "i_h < length (clean_prefix_of R)" and
          i_h_at: "clean_prefix_of R ! i_h
                     = Cdc (hist_coord (H ! j_src)) (hist_event (H ! j_src))"
          by (auto simp: in_set_conv_nth)

        have i_h_key: "event_key (clean_prefix_of R ! i_h) = k"
          using i_h_at j_key by simp

        \<comment> \<open>i_h ≤ i_max (else contradicts i_max_latest).\<close>
        have i_h_le_imax: "i_h \<le> i_max"
        proof (rule ccontr)
          assume "\<not> i_h \<le> i_max"
          hence imax_lt_ih: "i_max < i_h" by simp
          from i_max_latest imax_lt_ih i_h_lt have "event_key (clean_prefix_of R ! i_h) \<noteq> k"
            by blast
          with i_h_key show False by simp
        qed

        \<comment> \<open>Three sub-cases on i_h vs i_max.\<close>
        consider (eq) "i_h = i_max" | (lt) "i_h < i_max"
          using i_h_le_imax by linarith
        thus False
        proof cases
          case eq
          \<comment> \<open>clean_prefix R ! i_max = Refresh k m c_read AND = Cdc (...).
              Distinct constructors, contradiction.\<close>
          from cp_at_imax i_h_at eq show False by simp
        next
          case lt
          \<comment> \<open>By clean_prefix_of_order_respects_coordinate + cdc_coord,
              src_le (hist_coord (H!j_src)) c_read.
              But src_lt c_read (hist_coord (H!j_src)). Antisymmetry.\<close>
          from clean_prefix_of_order_respects_coordinate[OF wf lt i_max_lt]
          have "src_le (cdc_coord (clean_prefix_of R ! i_h))
                       (cdc_coord (clean_prefix_of R ! i_max))" .
          hence "src_le (hist_coord (H ! j_src)) c_read"
            using i_h_at cp_at_imax by simp
          with j_after show False
            unfolding src_lt_def
            using src_le_antisym by blast
        qed
      qed
    qed

    \<comment> \<open>Refresh case Step 6: c_read ≤ frontier via WF5.\<close>
    have c_read_le_f: "src_le c_read (frontier_of R)"
    proof -
      from wf5 ch_in_chunks
      have "src_le (chunk_read_coordinate R ch) (frontier_of R)" by blast
      thus ?thesis using cr_eq by simp
    qed

    \<comment> \<open>Refresh case Step 7: Src b0 H frontier k = Src b0 H c_read k.\<close>
    have src_eq:
      "Src b0 H (frontier_of R) k = Src b0 H c_read k"
      by (rule src_eq_when_no_later_src_event_for_k[OF c_read_le_f no_later_src])

    \<comment> \<open>Refresh case Step 8: assemble Apply = m = Src b0 H c_read k = Src b0 H frontier k.\<close>
    show "Apply (clean_prefix_of R) k = Src b0 H (frontier_of R) k"
      using apply_val m_eq_src_at_cr src_eq by simp
  qed
qed

end
