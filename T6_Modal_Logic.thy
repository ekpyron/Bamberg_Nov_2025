theory T6_Modal_Logic
  imports Main
begin

text\<open>A simple embedding of an S5 modal logic with Actuality Operator.\<close>

typedecl w \<comment> \<open>Type of Possible Worlds\<close>

type_synonym \<o> = \<open>w \<Rightarrow> bool\<close> \<comment> \<open>Propositions have truth values in each world.\<close>

named_theorems mdefs

definition mnot :: \<open>\<o> \<Rightarrow> \<o>\<close> (\<open>\<^bold>\<not>_\<close> [840] 840) where [mdefs]:
  \<open>\<^bold>\<not>\<phi> \<equiv> \<lambda> w . \<not>\<phi> w\<close>
definition mimpl :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>\<close> (infixr \<open>\<^bold>\<rightarrow>\<close> 825) where [mdefs]:
  \<open>\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<lambda>w . \<phi> w \<longrightarrow> \<psi> w\<close>
definition mconj :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>\<close> (infixr \<open>\<^bold>\<and>\<close> 835) where [mdefs]:
  \<open>\<phi> \<^bold>\<and> \<psi> \<equiv> \<lambda>w . \<phi> w \<and> \<psi> w\<close>
definition mdisj :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>\<close> (infixr \<open>\<^bold>\<or>\<close> 830) where [mdefs]:
  \<open>\<phi> \<^bold>\<or> \<psi> \<equiv> \<lambda>w . \<phi> w \<or> \<psi> w\<close>
definition mequiv :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>\<close> (infixr \<open>\<^bold>\<equiv>\<close> 820) where [mdefs]:
  \<open>\<phi> \<^bold>\<equiv> \<psi> \<equiv> \<lambda>w . \<phi> w \<longleftrightarrow> \<psi> w\<close>
definition mall :: \<open>('a \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close> (binder \<open>\<^bold>\<forall>\<close> 810) where [mdefs]:
  \<open>\<^bold>\<forall> x . \<phi> x \<equiv> \<lambda>w . \<forall>x . \<phi> x w\<close>
definition mex :: \<open>('a \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close> (binder \<open>\<^bold>\<exists>\<close> 810) where [mdefs]:
  \<open>\<^bold>\<exists> x . \<phi> x \<equiv> \<lambda>w . \<exists>x . \<phi> x w\<close>

definition mnec :: \<open>\<o> \<Rightarrow> \<o>\<close> (\<open>\<^bold>\<box>_\<close> [830] 850) where [mdefs]:
  \<open>\<^bold>\<box>\<phi> \<equiv> \<lambda>w. \<forall> v . \<phi> v\<close>
definition mposs :: \<open>\<o> \<Rightarrow> \<o>\<close> (\<open>\<^bold>\<diamond>_\<close> [830] 850) where [mdefs]:
  \<open>\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w. \<exists> v . \<phi> v\<close>

consts w\<^sub>0 :: w \<comment> \<open>We choose an actual world.\<close>
definition mact :: \<open>\<o> \<Rightarrow> \<o>\<close> (\<open>\<^bold>\<A>_\<close> [830] 850) where [mdefs]:
  \<open>\<^bold>\<A>\<phi> \<equiv> \<lambda>w. \<phi> w\<^sub>0\<close>

definition mvalid_nec :: \<open>\<o> \<Rightarrow> bool\<close> (\<open>[\<Turnstile>\<^sub>\<box> _]\<close>) where [mdefs]:
  \<open>[\<Turnstile>\<^sub>\<box> \<phi>] \<equiv> \<forall>v . \<phi> v\<close>
definition mvalid_act :: \<open>\<o> \<Rightarrow> bool\<close> (\<open>[\<Turnstile> _]\<close>) where [mdefs]:
  \<open>[\<Turnstile> \<phi>] \<equiv> \<phi> w\<^sub>0\<close>

lemma \<open>[\<Turnstile>\<^sub>\<box> \<phi>] \<Longrightarrow> [\<Turnstile> \<phi>]\<close>
  by (simp add: mvalid_act_def mvalid_nec_def)

lemma \<open>[\<Turnstile> \<phi>] \<Longrightarrow> [\<Turnstile>\<^sub>\<box> \<phi>]\<close>
  nitpick[expect=genuine]
  oops

lemma A1: \<open>[\<Turnstile>\<^sub>\<box> \<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<phi>)]\<close>
  by (auto simp: mdefs)
lemma A2: \<open>[\<Turnstile>\<^sub>\<box> (\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<chi>)) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<chi>))]\<close>
  by (auto simp: mdefs)
lemma A3: \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi>) \<^bold>\<rightarrow> ((\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> \<phi>)]\<close>
  by (auto simp: mdefs)

lemma A4: \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> \<phi> x]\<close>
  by (auto simp: mdefs)
lemma A5: \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<forall> \<alpha> . \<phi> \<alpha> \<^bold>\<rightarrow> \<psi> \<alpha>) \<^bold>\<rightarrow> ((\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> (\<^bold>\<forall> \<alpha> . \<psi> \<alpha>))]\<close>
  by (auto simp: mdefs)
lemma A6: \<open>[\<Turnstile>\<^sub>\<box> \<phi> \<^bold>\<rightarrow> (\<^bold>\<forall> \<alpha> . \<phi>)]\<close>
  by (auto simp: mdefs)

lemma A7: \<open>[\<Turnstile> \<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<phi>]\<close>
  by (auto simp: mdefs)
lemma \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<phi>]\<close>
  nitpick[expect=genuine]
  oops

lemma A8: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<A>\<^bold>\<not>\<phi> \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<A>\<phi>]\<close>
  by (auto simp: mdefs)
lemma A9: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<A>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<equiv> \<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<A>\<psi>]\<close>
  by (auto simp: mdefs)
lemma A10: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<A>(\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<equiv> (\<^bold>\<forall> \<alpha> . \<^bold>\<A>\<phi> \<alpha>)]\<close>
  by (auto simp: mdefs)
lemma A11: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<A>\<phi> \<^bold>\<equiv> \<^bold>\<A>\<^bold>\<A>\<phi>]\<close>
  by (auto simp: mdefs)

lemma K: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)]\<close>
  by (auto simp: mdefs)
lemma T: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>]\<close>
  by (auto simp: mdefs)
lemma 5: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>]\<close>
  by (auto simp: mdefs)

lemma A12: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<A>\<phi>]\<close>
  by (auto simp: mdefs)

lemma A13: \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<A>\<^bold>\<box>\<phi>]\<close>
  by (auto simp: mdefs)

lemma \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<forall>x. \<^bold>\<box>\<phi> x) \<^bold>\<equiv> \<^bold>\<box>(\<^bold>\<forall>x. \<phi> x)]\<close>
  by (auto simp: mdefs)
lemma \<open>[\<Turnstile>\<^sub>\<box> (\<^bold>\<exists>x. \<^bold>\<diamond>\<phi> x) \<^bold>\<equiv> \<^bold>\<diamond>(\<^bold>\<exists>x. \<phi> x)]\<close>
  by (auto simp: mdefs)

lemma \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<box>(\<^bold>\<forall>R::(\<o> \<Rightarrow> \<o>) \<Rightarrow> \<o> \<Rightarrow> \<o>. \<phi> R) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> (\<lambda> F y . \<^bold>\<box>F y \<^bold>\<rightarrow> \<^bold>\<A>y))]\<close> \<comment> \<open>We get full higher order modal logic!\<close>
  by (auto simp: mdefs)

lemma \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<box>\<phi>] = (\<forall>w . \<phi> w)\<close>
  by (auto simp: mdefs)
lemma \<open>[\<Turnstile>\<^sub>\<box> \<^bold>\<diamond>\<phi>] = (\<exists>w . \<phi> w)\<close>
  by (auto simp: mdefs)

text\<open>Note: We specifically constructed an S5 modal logic. For weaker modal logics, necessity is
           defined relative to an accessibility relation between worlds.
           See e.g. @{url \<open>https://plato.stanford.edu/entries/logic-modal/#PosWorSem\<close>} for the
           theoretical background or @{url \<open>https://arxiv.org/pdf/1507.08717\<close>} for a description
           of a more general implementation in Isabelle/HOL.\<close>

end