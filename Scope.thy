theory Scope
  imports Main
begin

text \<open>
  Layer 0: key-scope restriction of a per-key state.

  Given a per-key state @{text x} and a key set @{text K}, the
  restriction @{text "x \<restriction> K"} keeps exactly the entries whose
  key lies in @{text K} and drops the rest. The paper writes this
  with the restriction operator @{text \<open>\<restriction>\<close>}; the formalism
  exposes it as the plain function @{text restrict}, whose semantics
  are standard map-restriction.
\<close>

definition restrict :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k set \<Rightarrow> ('k \<rightharpoonup> 'v)"
  where "restrict m K = (\<lambda>k. if k \<in> K then m k else None)"

end
